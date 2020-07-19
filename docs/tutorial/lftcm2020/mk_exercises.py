#!/usr/bin/env python3

import regex
from pathlib import Path

inline_sorry_regex = regex.compile(r'/- inline sorry -/.*/- inline sorry -/')
sorry_regex = regex.compile(r'(.*)-- sorry.*')
omit_regex = regex.compile(r'(.*)-- omit.*')
root = Path(__file__).parent/'src'

if __name__ == '__main__':
    for path in (root/'solutions').glob('**/*.lean'):
        if path.name == 'numbers.lean':
            continue  # Rob's exercises need hand-crafted extraction
        if path.name == 'metaprogramming.lean':
            continue  # Rob's exercises need hand-crafted extraction
        print(path)
        out = root/'exercises_sources'/path.relative_to(root/'solutions')
        out.parent.mkdir(exist_ok=True)
        with out.open('w', encoding="utf8") as outp:
            with path.open(encoding="utf8") as inp:
                state = 'normal'
                for line in inp:
                    line, _ = inline_sorry_regex.subn("sorry", line)

                    match_sorry = sorry_regex.match(line)
                    match_omit = omit_regex.match(line)
                    if state == 'normal':
                        if match_sorry or match_omit:
                            state = 'sorry'
                        else:
                            outp.write(line)
                    else:
                        if match_sorry:
                            state = 'normal'
                            outp.write(match_sorry.group(1) + 'sorry\n')
                        else:
                            if match_omit :
                                state = 'normal'
                                outp.write(match_omit.group(1) + '\n')

            outp.write('\n')
