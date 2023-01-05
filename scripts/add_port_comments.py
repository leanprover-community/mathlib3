from mathlibtools.file_status import PortStatus, FileStatus
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
    > Any changes to this file require a corresponding PR to mathlib4.""")

def replace_range(src: str, pos: int, end_pos: int, new: str) -> str:
    return src[:pos] + new + src[end_pos:]

def find_module_comment(s: str) -> Optional[re.Match]:
    """ find a doc-comment, even if it contains nested comments """
    start_marker = re.compile('/-!').search(s)
    if not start_marker:
        return None

    depth = 1
    ind = start_marker.end()
    while depth > 0:
        marker = re.compile(r'(/-)|(-/)').search(s, pos=ind)
        if not marker:
            raise ValueError('Could not find end of comment')
        ind = marker.end()
        if marker.group(1):
            depth += 1
        else:
            depth -= 1

    # Create a new match with sensible captures
    m = re.compile('/-!(.*)-/', re.MULTILINE | re.DOTALL).fullmatch(s, start_marker.start(), marker.end())
    assert m, s[start_marker.start():marker.end()]
    return m


class NoModuleDocstringError(ValueError): pass

def add_port_status(fcontent: str, fstatus: FileStatus) -> str:
    module_comment = find_module_comment(fcontent)
    if not module_comment:
        raise NoModuleDocstringError()

    module_comment_start = module_comment.start(1)
    module_comment_end = module_comment.end(1)
    module_comment = module_comment.group(1)

    # replace any markers that appear at the start of the docstring
    module_comment = re.compile(
        r"\A\n((?:> )?)THIS FILE IS SYNCHRONIZED WITH MATHLIB4\."
        r"(?:\n\1[^\n]+)*\n?",
        re.MULTILINE
    ).sub('', module_comment)

    # markers which appear with two blank lines before
    module_comment = re.compile(
        r"\n{,2}((?:> )?)THIS FILE IS SYNCHRONIZED WITH MATHLIB4\."
        r"(?:\n\1[^\n]+)*",
        re.MULTILINE
    ).sub('', module_comment)

    # find the header
    header_re = re.compile('(#[^\n]*)', re.MULTILINE)
    existing_header = header_re.search(module_comment)
    if existing_header:
        # insert a comment below the header
        module_comment = replace_range(module_comment, existing_header.end(1), existing_header.end(1),
            "\n\n" + make_comment(f_status))
    else:
        # insert the comment at the top
        module_comment = "\n" + make_comment(f_status) + "\n" + module_comment

    # and insert the new module docstring
    fcontent = replace_range(fcontent, module_comment_start, module_comment_end, module_comment)

    return fcontent

def fname_for(import_path: str) -> Path:
    return src_path / Path(*import_path.split('.')).with_suffix('.lean')


missing_docstrings = []
missing_files = []
for iname, f_status in status.file_statuses.items():
    if f_status.ported:
        fname = fname_for(iname)
        try:
            with open(fname) as f:
                fcontent = f.read()
        except FileNotFoundError:
            missing_files.append((iname, fname))
            continue
        try:
            new_fcontent = add_port_status(fcontent, f_status)
        except NoModuleDocstringError:
            missing_docstrings.append((iname, fname))
            continue
        if new_fcontent == fcontent:
            continue
        print(f'* `{iname}`')
        with open(fname, 'w') as f:
            f.write(new_fcontent)
if missing_docstrings:
    print('\n---')
    print('The following files have no module docstring, so I have not added a message in this PR')
    for iname, fname in missing_docstrings:
        print(f'* [`{iname}`](https://github.com/leanprover-community/mathlib/blob/master/{fname})')
    print('\nPlease make a PR to add a module docstring (for Lean3 and Lean4!), then I will add the freeze comment next time.')
if missing_files:
    print('\n---')
    print('The following files no longer exist in Lean 3\' mathlib, so I have not added a message in this PR')
    for iname, fname in missing_files:
        f_status = status.file_statuses[iname]
        print(f'* [`{iname}`](https://github.com/leanprover-community/mathlib/blob/{f_status.mathlib3_hash}/{fname})')
    print('\nIn future we should find where they moved to, and check that the files are still in sync.')
