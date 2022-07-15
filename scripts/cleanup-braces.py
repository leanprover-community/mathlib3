#!/usr/bin/env python3

from pathlib import Path
import re
import sys, os

TMP_SUFFIX = ".brace_cleanup"

def fix_brace_o(a, b):
    """Move any `{`s between the contents of line `a` and line `b` to the start of line `b`.
    
    :param a: A line of Lean code, ending with `\n'
    :param b: A line of Lean code, ending with `\n'
    
    :returns: A tuple `(anew, bnew, fix)`, where `anew` and `bnew` are `a` and `b` with corrected brace positions,
    and `fix` is a boolean indicating whether there was a change, i.e. `fix = ((anew, bnew) != (a, b))`.
    """
    astr = a.rstrip()
    if astr == "":
        return a, b, False
    if not astr[-1] == '{':
        return a, b, False
    a = astr[:-1].rstrip() + '\n'
    bstr = b.lstrip()
    indent = len(b) - len(bstr)
    indent = max(indent - 2, 0)
    b = " " * indent + "{ " + bstr
    return a, b, True

def fix_brace_c(a, b):
    """Move any `}`s between the contents of line `a` and line `b` to the end of line `a`.
    
    :param a: A line of Lean code, ending with `\n'
    :param b: A line of Lean code, ending with `\n'
    
    :returns: A tuple `(anew, bnew, merge)`, where `anew` and `bnew` are `a` and `b` with corrected brace positions,
    and `merge` is a boolean indicating if the result is a single line, returned in `bnew` (and `anew` can be ignored).
    """
    bstr = b.lstrip()
    if bstr == "":
        return a, b, False
    if not bstr[0] == '}':
        return a, b, False
    return "", a.rstrip() + " " + bstr, True

def fix_brace_pair(a, b):
    """Move any `{`s and `}`s between the contents of line `a` and line `b` to the correct position.
    
    :param a: A line of Lean code, ending with `\n'
    :param b: A line of Lean code, ending with `\n'
    
    :returns: A tuple `(anew, bnew, merge)`, where `anew` and `bnew` are `a` and `b` with corrected brace positions,
    and `merge` is a boolean indicating if the result is a single line, returned in `bnew` (and `anew` can be ignored).
    """
    anew, bnew, fix = fix_brace_o(a, b)
    if fix:  # `a` ended with a `{` that got moved to `bnew`, so `fix_brace_c` doesn't have anything to do.
        return anew, bnew, False
    else:
        return fix_brace_c(anew, bnew)

def fix_braces(filename):
    # open files for reading and writing
    fi = Path(filename).open(mode="r", encoding="utf-8", newline='\n')
    fo = Path(filename + TMP_SUFFIX).open(mode="w", encoding="utf-8", newline='\n')
    merge = False  # indicates when `ao` got merged into `bo`, so we can ignore `ao`.
    # read the first line
    ai = fi.readline()
    bo = ai # if there is only one line, the last output line is the first line
    while (bi := fi.readline()):
        ao, bo, merge = fix_brace_pair(ai, bi)
        # prepare for next iteration
        ai = bo
        if not merge:
            fo.write(ao)
    # write the last line
    fo.write(bo)
    # close the files
    fi.close()
    fo.close()
    # move the output file back to the input
    os.rename(filename + TMP_SUFFIX, filename)

for filename in sys.argv[1:]:
    fix_braces(filename)

