#!/bin/bash

input=nolints.txt

fn=''
cnt=0

while read -r line
do
        case "$line" in
                '-- '*)
			cnt=0
                        fn=${line:3}
                        ;;
                apply*)
			cnt=$(($cnt+1))
                        ;;
                '')
                        if [ $cnt -gt 0 ]
			then
				echo "$cnt $fn"
			fi
                        ;;
        esac
done < "$input"

echo $(($cnt+1)) $fn
