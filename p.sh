#!/bin/bash

# Top-level root directory of the Git repository
root=`git rev-parse --show-toplevel`

# A list of directories containing .olean files. We are being conservative to
# avoid traversing irrelevant directories and affecting directories we do not
# want changed (e.g. $root/.git).

dirs=(src test)

# Delete every <path>.olean without a matching <path>.lean.
dir0=$(pwd)

for dir in "${dirs[@]}"
do
    cd "$root"/"$dir"
    for olean_file in `find . -name "*.olean"`
    do
	lean_file=${olean_file/%.olean/.lean}
	if [ ! -e "$lean_file" ]; then
            echo "rm \"$olean_file\""
            rm "$olean_file"
	fi
    done

    # Delete all empty directories. An empty directory may have been created if it
    # does not contain any .lean files and all of its .olean files were deleted.
    
    find . -type d -empty -delete
    
done

cd "$dir0"



