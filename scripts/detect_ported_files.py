# this script is only intended to be run by CI
import sys
from pathlib import Path

from mathlibtools.file_status import PortStatus, FileStatus

status = PortStatus.deserialize_old()

src_path = Path(__file__).parent.parent / 'src'

def encode_msg_text_for_github(msg):
    # even though this is probably url quoting, we match the implementation at
    # https://github.com/actions/toolkit/blob/af821474235d3c5e1f49cee7c6cf636abb0874c4/packages/core/src/command.ts#L36-L94
    return msg.replace('%', '%25').replace('\r', '%0D').replace('\n', '%0A')

def fname_for(import_path: str) -> Path:
    return src_path / Path(*import_path.split('.')).with_suffix('.lean')

if __name__ == '__main__':
    files = [Path(f) for f in sys.argv[1:]]
    for iname, f_status in status.file_statuses.items():
        if f_status.ported:
            fname = fname_for(iname)
            if fname in files:
                msg = ("Changes to this file will need to be ported to mathlib 4!\n"
                    "Please consider retracting the changes to this file unless you are willing "
                    "to immediately forward-port them." )
                print(f"::warning file={fname},line=1,col=1::{encode_msg_text_for_github(msg)}")
