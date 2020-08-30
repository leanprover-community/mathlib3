import itertools
import sys

was_silent = True
for line in sys.stdin:
    sys.stdout.write(line)
    if 'error' in line:
        for line in itertools.islice(sys.stdin, 20):
            sys.stdout.write(line)
        sys.exit(1)
    elif not line.startswith('configuring mathlib') and not line.startswith('> lean --make'):
        print(line)
        was_silent = False

if not was_silent:
    sys.exit(1)
