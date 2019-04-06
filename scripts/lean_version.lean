-- Print the current version of lean, using logic copied from leanpkg.

import system.io

def lean_version_string_core :=
let (major, minor, patch) := lean.version in
sformat!("{major}.{minor}.{patch}")

def main : io unit :=
io.put_str_ln lean_version_string_core
