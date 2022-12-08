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

# Just print it on every file!
for iname, f_status in status.file_statuses.items():
    if f_status.ported:
        fname = fname_for(iname)
        print("::warning file={fname},line=1,col=1::This file has been ported!")
