from mathlibtools.lib import LeanProject
from pathlib import Path

import re
from dataclasses import asdict, dataclass
from typing import Any, Dict, Optional, Union
import textwrap

import requests
import yaml

# copied from https://github.com/leanprover-community/mathlib-tools/pull/137/files#

@dataclass()
class FileStatus:

    ported: bool = False
    mathlib4_pr: Optional[int] = None
    mathlib3_hash: Optional[str] = None
    comments: Optional[str] = None

    @classmethod
    def parse_old(cls, message: str) -> "FileStatus":
        ported = False
        mathlib4_pr: Optional[int] = None
        mathlib3_hash: Optional[str] = None
        if message.startswith("Yes"):
            ported = True
            if len(message.split()) > 2:
                mathlib3_hash = message.split()[2]
        if "mathlib4#" in message:
            mathlib4_pr = int(re.findall(r"[0-9]+", message.replace("mathlib4#", ""))[0])
        return cls(
            ported=ported,
            mathlib4_pr=mathlib4_pr,
            mathlib3_hash=mathlib3_hash,
        )

    def asdict(self) -> Dict[str, Any]:
        return {k: v for k, v in asdict(self).items() if v is not None}

    def color(self) -> Optional[str]:
        if self.ported:
            return "green"
        if self.mathlib4_pr:
            return "lightskyblue"
        if self.comments and "ready" in self.comments:
            return "turquoise1"
        return None


@dataclass
class PortStatus:

    file_statuses: Dict[str, FileStatus]

    @classmethod
    def old_yaml(cls, url: Optional[str] = None) -> Dict[str, str]:
        if url is None:
            url = "https://raw.githubusercontent.com/wiki/leanprover-community/mathlib/mathlib4-port-status.md"
        def yaml_md_load(wikicontent: bytes):
            return yaml.safe_load(wikicontent.replace(b"```", b""))

        return yaml_md_load(requests.get(url).content)

    @classmethod
    def deserialize_old(cls, yaml: Dict[str, str]) -> "PortStatus":
        return cls(file_statuses={k: FileStatus.parse_old(v) for k, v in yaml.items()})

    def serialize(self) -> Dict[str, Dict[str, Union[int, str, None]]]:
        return yaml.dump({k: v.asdict() for k, v in self.file_statuses.items()})



y = PortStatus.old_yaml()
status = PortStatus.deserialize_old(y)

src_path = Path(__file__).parent.parent / 'src'

def make_comment(fstatus):
    return textwrap.dedent(f"""\
    > THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
    > https://github.com/leanprover-community/mathlib4/pull/{fstatus.mathlib4_pr}
    > Any changes to this file require a corresponding PR to mathlib4.""")

def replace_range(src, pos, end_pos, new):
    return src[:pos] + new + src[end_pos:]


def add_port_status(fcontent, fstatus):
    module_comment = re.search('/-!\s*(.*?)-/', fcontent, re.MULTILINE | re.DOTALL)
    assert module_comment
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
            print("!!!", repr(rest))
            trailing_whitespace = "\n" if rest.strip() else ""
            fcontent = replace_range(fcontent, existing_label.start(), existing_label.end(), "")
            fcontent = replace_range(fcontent, existing_header.end(), existing_header.end(),
                "\n" + make_comment(f_status) + trailing_whitespace)
        else:
            assert False
    return fcontent

def fname_for(import_path):
    return src_path / Path(*import_path.split('.')).with_suffix('.lean')


for iname, f_status in status.file_statuses.items():
    if f_status.ported:
        fname = fname_for(iname)
        print(iname, f_status)
        with open(fname) as f:
            fcontent = f.read()
        fcontent = add_port_status(fcontent, f_status)
        with open(fname, 'w') as f:
            f.write(fcontent)
