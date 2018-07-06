for i in $(echo "A" "B") ; do
    echo "version $i" > profile_config.txt
    touch tactic/transport.lean
    lean tactic/transport.lean 2>&1 | grep -e "elaboration: tactic execution took\|version"
    lean tests/examples.lean 2>&1 | grep -e "elaboration: tactic execution took\|version" > nil

    for i in {1..10}; do
        ( lean tests/examples.lean 2>&1 | grep -e "elaboration: tactic execution took\|version" | stack collect_data.hs ) ;
    done

done
