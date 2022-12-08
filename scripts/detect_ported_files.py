import sys
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

def fname_for(import_path: str) -> Path:
    return src_path / Path(*import_path.split('.')).with_suffix('.lean')

if __name__ == '__main__':
    files = sys.argv[1:]
    print(files)
    # Just print it on every file!
    for iname, f_status in status.file_statuses.items():
        if f_status.ported:
            fname = fname_for(iname)
            print(fname, fname in files)
            print(f"::warning file={fname},line=1,col=1::This file was ported in https://github.com/leanprover-community/mathlib4/pull/{f_status.mathlib4_pr}")
