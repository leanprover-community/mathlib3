#!/bin/sh

# Delete every <path>.olean without a matching <path>.lean.

for olean_file in `find . -name "*.olean"`
do
    lean_file=`echo $olean_file | sed "s/\.olean/.lean/"`
    if [ ! -e $lean_file ]; then
        echo "rm $olean_file"
        rm $olean_file
    fi
done

# Delete all empty directories. An empty directory may have been created if it
# does not contain any .lean files and all of its .olean files were deleted.

find . -type d -empty -delete
