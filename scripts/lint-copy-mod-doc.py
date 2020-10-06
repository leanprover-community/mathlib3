#!/usr/bin/env python3.8

import sys

fns = sys.argv[1:]

ERR_COP = 0
ERR_IMP = 1
ERR_MOD = 2

exceptions = []

with open("scripts/copy-mod-doc-exceptions-short.txt") as f:
    lines = f.readlines()
    for line in lines:
        (errno, c, fn) = line.split()
        if errno == "ERR_COP":
            exceptions += [(ERR_COP, fn)]
        if errno == "ERR_IMP":
            exceptions += [(ERR_IMP, fn)]
        if errno == "ERR_MOD":
            exceptions += [(ERR_MOD, fn)]

def import_only_check(lines, fn):
    import_only_file = True
    errors = []
    line_nr = 0
    for line in lines:
        line_nr += 1
        if line == "\n":
            continue
        imports = line.split()
        if imports[0] != "import":
            import_only_file = False
            break
        if len(imports) > 2:
            if imports[2] == "--":
                continue
            else:
                errors += [(ERR_IMP, line_nr, fn)]
    return (import_only_file, errors)

def regular_check(lines, fn):
    in_comment = False
    file_started = False
    line_nr = 0
    errors = []
    copy_started = False
    copy_done = False
    copy_start_line_nr = 0
    for line in lines:
        line_nr += 1
        if not copy_started and line == "\n":
            continue
        if not copy_started and line == "/-\n":
            copy_started = True
            copy_start_line_nr = line_nr
            continue
        if not copy_started:
            errors += [(ERR_COP, line_nr, fn)]
        if copy_started and not copy_done:
            if line_nr == copy_start_line_nr + 1 and not "Copyright (c)" in line:
                errors += [(ERR_COP, line_nr, fn)]
            if line_nr == copy_start_line_nr + 2 and not "Apache" in line:
                errors += [(ERR_COP, line_nr, fn)]
            if line_nr == copy_start_line_nr + 3 and not ("Authors:" in line or "Author:" in line):
                errors += [(ERR_COP, line_nr, fn)]
            if line_nr == copy_start_line_nr + 4 and not line == "-/\n":
                errors += [(ERR_COP, line_nr, fn)]
            if line == "-/\n":
                copy_done = True
            continue
        if copy_done and line == "\n":
            continue
        words = line.split()
        if words[0] != "import" and words[0] != "/-!":
            errors += [(ERR_MOD, line_nr, fn)]
            break
        if words[0] == "/-!":
            break
        # final case: words[0] == "import"
        if len(words) > 2:
            if words[2] != "--":
                errors += [(ERR_IMP, line_nr, fn)]
    return errors

def format_errors(errors):
    for (errno, line_nr, fn) in errors:
        if (errno, fn) in exceptions:
            continue
        if errno == ERR_COP:
            print("ERR_COP : Malformed or missing copyright header : line {:02d} : {}".format(line_nr, fn))
        if errno == ERR_IMP:
            print("ERR_IMP : More than one file imported per line  : line {:02d} : {}".format(line_nr, fn))
        if errno == ERR_MOD:
            print("ERR_MOD : Module docstring missing, or too late : line {:02d} : {}".format(line_nr, fn))

def lint(fn):
    with open(fn) as f:
        lines = f.readlines()
        (b, errs) = import_only_check(lines, fn)
        if b:
            format_errors(errs)
            return
        errs = regular_check(lines, fn)
        format_errors(errs)

for fn in fns:
    lint(fn)

