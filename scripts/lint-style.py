#!/usr/bin/env python3

import sys

fns = sys.argv[1:]

ERR_COP = 0 # copyright header
ERR_IMP = 1 # import statements
ERR_MOD = 2 # module docstring
ERR_LIN = 3 # line length
ERR_SAV = 4 # ᾰ
ERR_RNT = 5 # reserved notation
ERR_OPT = 6 # set_option

exceptions = []

with open("scripts/style-exceptions.txt", encoding="utf-8") as f:
    for line in f.readlines():
        fn, _, _, _, _, errno, *_ = line.split()
        if errno == "ERR_COP":
            exceptions += [(ERR_COP, fn)]
        if errno == "ERR_IMP":
            exceptions += [(ERR_IMP, fn)]
        if errno == "ERR_MOD":
            exceptions += [(ERR_MOD, fn)]
        if errno == "ERR_LIN":
            exceptions += [(ERR_LIN, fn)]
        if errno == "ERR_SAV":
            exceptions += [(ERR_SAV, fn)]
        if errno == "ERR_RNT":
            exceptions += [(ERR_RNT, fn)]
        if errno == "ERR_OPT":
            exceptions += [(ERR_OPT, fn)]

new_exceptions = False

def skip_comments(enumerate_lines):
    in_comment = False
    for line_nr, line in enumerate_lines:
        if "/-" in line:
            in_comment = True
        if "-/" in line:
            in_comment = False
            continue
        if line == "\n" or in_comment:
            continue
        yield line_nr, line

def skip_string(enumerate_lines):
    in_string = False
    in_comment = False
    for line_nr, line in enumerate_lines:
        # ignore comment markers inside string literals
        if not in_string:
            if "/-" in line:
                in_comment = True
            if "-/" in line:
                in_comment = False
        # ignore quotes inside comments
        if not in_comment:
            # crude heuristic: if the number of non-escaped quote signs is odd,
            # we're starting / ending a string literal
            if line.count("\"") - line.count("\\\"") % 2 == 1:
                in_string = not in_string
            # if there are quote signs in this line,
            # a string literal probably begins and / or ends here,
            # so we skip this line
            if line.count("\"") > 0:
                continue
            if in_string:
                continue
        yield line_nr, line

def small_alpha_vrachy_check(lines, fn):
    errors = []
    for line_nr, line in skip_string(skip_comments(enumerate(lines, 1))):
        if 'ᾰ' in line:
            errors += [(ERR_SAV, line_nr, fn)]
    return errors

def reserved_notation_check(lines, fn):
    if fn == 'src/tactic/reserved_notation.lean':
        return []
    errors = []
    for line_nr, line in skip_string(skip_comments(enumerate(lines, 1))):
        if line.startswith('reserve') or line.startswith('precedence'):
            errors += [(ERR_RNT, line_nr, fn)]
    return errors

def set_option_check(lines, fn):
    errors = []
    for line_nr, line in skip_string(skip_comments(enumerate(lines, 1))):
        if line.startswith('set_option'):
            next_two_chars = line.split(' ')[1][:2]
            # forbidden options: pp, profiler, trace
            if next_two_chars == 'pp' or next_two_chars == 'pr' or next_two_chars == 'tr':
                errors += [(ERR_OPT, line_nr, fn)]
    return errors

def long_lines_check(lines, fn):
    errors = []
    # TODO: some string literals (in e.g. tactic output messages) can be excepted from this rule
    for line_nr, line in enumerate(lines, 1):
        if "http" in line:
            continue
        if len(line) > 101:
            errors += [(ERR_LIN, line_nr, fn)]
    return errors

def import_only_check(lines, fn):
    import_only_file = True
    errors = []
    for line_nr, line in skip_comments(enumerate(lines, 1)):
        imports = line.split()
        if imports[0] == "--":
            continue
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
    errors = []
    copy_started = False
    copy_done = False
    copy_start_line_nr = 0
    copy_lines = ""
    for line_nr, line in enumerate(lines, 1):
        if not copy_started and line == "\n":
            errors += [(ERR_COP, copy_start_line_nr, fn)]
            continue
        if not copy_started and line == "/-\n":
            copy_started = True
            copy_start_line_nr = line_nr
            continue
        if not copy_started:
            errors += [(ERR_COP, line_nr, fn)]
        if copy_started and not copy_done:
            copy_lines += line
            if line == "-/\n":
                if ((not "Copyright" in copy_lines) or
                    (not "Apache" in copy_lines) or
                    (not "Author" in copy_lines)):
                    errors += [(ERR_COP, copy_start_line_nr, fn)]
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
    global new_exceptions
    for (errno, line_nr, fn) in errors:
        if (errno, fn) in exceptions:
            continue
        new_exceptions = True
        # filename first, then line so that we can call "sort" on the output
        if errno == ERR_COP:
            print("{} : line {} : ERR_COP : Malformed or missing copyright header".format(fn, line_nr))
        if errno == ERR_IMP:
            print("{} : line {} : ERR_IMP : More than one file imported per line".format(fn, line_nr))
        if errno == ERR_MOD:
            print("{} : line {} : ERR_MOD : Module docstring missing, or too late".format(fn, line_nr))
        if errno == ERR_LIN:
            print("{} : line {} : ERR_LIN : Line has more than 100 characters".format(fn, line_nr))
        if errno == ERR_SAV:
            print("{} : line {} : ERR_SAV : File contains the character ᾰ".format(fn, line_nr))
        if errno == ERR_RNT:
            print("{} : line {} : ERR_RNT : Reserved notation outside tactic.reserved_notation".format(fn, line_nr))
        if errno == ERR_OPT:
            print("{} : line {} : ERR_OPT : Forbidden set_option command".format(fn, line_nr))

def lint(fn):
    with open(fn, encoding="utf-8") as f:
        lines = f.readlines()
        errs = long_lines_check(lines, fn)
        format_errors(errs)
        (b, errs) = import_only_check(lines, fn)
        if b:
            format_errors(errs)
            return
        errs = regular_check(lines, fn)
        format_errors(errs)
        errs = small_alpha_vrachy_check(lines, fn)
        format_errors(errs)
        errs = reserved_notation_check(lines, fn)
        format_errors(errs)
        errs = set_option_check(lines, fn)
        format_errors(errs)

for fn in fns:
    lint(fn)

# if "exceptions" is empty,
# we're trying to generate style-exceptions.txt,
# so new exceptions are expected
if new_exceptions and len(exceptions) > 0:
    exit(1)
