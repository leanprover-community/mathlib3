import itertools
from json import loads
from pathlib import Path
import sys

def format_msg(msg):
    return f"{msg['file_name']}:{msg.get('pos_line')}:{msg.get('pos_col')}: {msg.get('severity')}: {msg.get('text')}\n"

def write_and_print_noisy_files(noisy_files):
    with open('src/.noisy_files', 'w') as f:
        for file in noisy_files:
            f.write(file + '\n')
            print(file)

noisy_files = set()
for line in sys.stdin:
    msg = loads(line)
    print(format_msg(msg))
    if msg.get('severity') == 'error':
        if len(noisy_files) > 0:
            print("Also, the following files were noisy:")
            write_and_print_noisy_files(noisy_files)
        sys.exit(1)
    else:
        noisy_files.add(str(Path(msg['file_name']).relative_to(Path.cwd())))

if len(noisy_files) > 0:
    print("Build succeeded, but the following files were noisy:")
    write_and_print_noisy_files(noisy_files)
    sys.exit(1)
