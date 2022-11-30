from mathlibtools.file_status import PortStatus
from pathlib import Path

import re
from dataclasses import asdict, dataclass
from typing import Any, Dict, Optional, Union
import textwrap

import requests
import yaml

status = PortStatus.deserialize_old()

src_path = Path(__file__).parent.parent / 'src'

def make_comment(fstatus):
    return textwrap.dedent(f"""\
    > THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
    > https://github.com/leanprover-community/mathlib4/pull/{fstatus.mathlib4_pr}
    > Any changes to this file require a corresponding PR to mathlib4.""")

def replace_range(src, pos, end_pos, new):
    return src[:pos] + new + src[end_pos:]


class NoModuleDocstringError(ValueError): pass

def add_port_status(fcontent, fstatus):
    module_comment = re.search('/-!\s*(.*?)-/', fcontent, re.MULTILINE | re.DOTALL)
    if not module_comment:
        raise NoModuleDocstringError()

    module_comment_start = module_comment.start(1)
    module_comment_end = module_comment.end(1)

    comment_re = re.compile(
        r"^((?:> )?)THIS FILE IS SYNCHRONIZED WITH MATHLIB4\."
        r"(?:\n\1[^\n]+)*\n*",
        re.MULTILINE
    )
    header_re = re.compile('^#[^\n]*\n?', re.MULTILINE)

    existing_label = comment_re.search(fcontent, module_comment_start, module_comment_end)
    existing_header = header_re.search(fcontent, module_comment_start, module_comment_end)

    if not existing_label:
        rest = fcontent[existing_header.end():module_comment_end]
        trailing_whitespace = "\n" if rest.strip() else ""
        fcontent = replace_range(fcontent, existing_header.end(), existing_header.end(),
            "\n" + make_comment(f_status) + trailing_whitespace)
    else:
        if existing_label.end() <= existing_header.start():
            rest = fcontent[existing_header.end():module_comment_end]
            trailing_whitespace = "\n" if rest.strip() else ""
            fcontent = replace_range(fcontent, existing_header.end(), existing_header.end(),
                "\n" + make_comment(f_status) + trailing_whitespace)
            fcontent = replace_range(fcontent, existing_label.start(), existing_label.end(), "")
        elif existing_header.end() <= existing_label.start():
            rest = fcontent[existing_label.end():module_comment_end]
            trailing_whitespace = "\n" if rest.strip() else ""
            fcontent = replace_range(fcontent, existing_label.start(), existing_label.end(), "")
            fcontent = replace_range(fcontent, existing_header.end(), existing_header.end(),
                "\n" + make_comment(f_status) + trailing_whitespace)
        else:
            assert False
    return fcontent

def fname_for(import_path):
    return src_path / Path(*import_path.split('.')).with_suffix('.lean')


missing_docstrings = []
for iname, f_status in status.file_statuses.items():
    if f_status.ported:
        fname = fname_for(iname)
        with open(fname) as f:
            fcontent = f.read()
        try:
            new_fcontent = add_port_status(fcontent, f_status)
        except NoModuleDocstringError:
            missing_docstrings.append(fname)
            continue
        if new_fcontent == fcontent:
            continue
        print(f'* `{iname}`: https://github.com/leanprover-community/mathlib4/pull/{f_status.mathlib4_pr}')
        with open(fname, 'w') as f:
            f.write(new_fcontent)
if missing_docstrings:
    print('\n---')
    print('The following files have no module docstring, so I have not added a message in this PR')
    for fname in missing_docstrings:
        print(f'* [`{fname}`](https://github.com/leanprover-community/mathlib/blob/master/{fname})')
    print('\nPlease make a PR to add a module docstring (for Lean3 and Lean4!), then I will add the freeze comment next time.')
