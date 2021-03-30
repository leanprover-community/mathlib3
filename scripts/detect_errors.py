import itertools
from json import loads
from pathlib import Path
import sys

def encode_msg_text_for_github(msg):
    # even though this is probably url quoting, we match the implementation at
    # https://github.com/actions/toolkit/blob/af821474235d3c5e1f49cee7c6cf636abb0874c4/packages/core/src/command.ts#L36-L94
    return msg.replace('%', '%25').replace('\r', '%0D').replace('\n', '%0A')

def format_msg(msg):
    # Formatted for https://github.com/actions/toolkit/blob/master/docs/commands.md#log-level
    
    # mapping between lean severity levels and github levels.
    # github does not support info levels, which are emitted by `#check` etc:
    # https://docs.github.com/en/actions/reference/workflow-commands-for-github-actions#setting-a-debug-message
    severity_map = {'information': 'warning'}
    severity = msg.get('severity')
    severity = severity_map.get(severity, severity)
    
    # We include the filename / line number information as both message and metadata, to ensure
    # that github shows it.
    msg_text = f"{msg['file_name']}:{msg.get('pos_line')}:{msg.get('pos_col')}:\n{msg.get('text')}"
    msg_text = encode_msg_text_for_github(msg_text)
    return f"::{severity} file={msg['file_name']},line={msg.get('pos_line')},col={msg.get('pos_col')}::{msg_text}"

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
