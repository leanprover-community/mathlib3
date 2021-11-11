#!/usr/bin/env python3

from pathlib import Path
import re
import sys, os

DEBUG = True

TMP_SUFFIX = ".brace_cleanup"

def debug(s):
    if DEBUG:
        print(s)

def fix_brace_o(a, b):
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
    bstr = b.lstrip()
    if bstr == "":
        return a, b, False
    if not bstr[0] == '}':
        return a, b, False
    return "", a.rstrip() + " " + bstr, True

def fix_brace_pair(a, b):
    anew, bnew, fix = fix_brace_o(a, b)
    if fix:
        return anew, bnew, False
    else:
        return fix_brace_c(anew, bnew)

def fix_braces(filename):
    # open files for reading and writing
    fi = Path(filename).open(mode="r", encoding="utf-8", newline='\n')
    fo = Path(filename + TMP_SUFFIX).open(mode="w", encoding="utf-8", newline='\n')
    bo = ""
    merge = False
    more_than_one_line = False
    # read the first line
    ai = fi.readline()
    bo = ai # if there is only one line, the last output line is the first line
    while (bi := fi.readline()):
        more_than_one_line = True
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

