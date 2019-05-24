- The `vampire` tactic requires the Vampire theorem prover on your system. It has been tested with version 4.2.2 of Vampire without Z3, which you can obtain at : https://vprover.github.io/download.html

- For Linux, simply place the downloaded binary in a directory of your choice and set the value of `vampire_path` (in `main.lean`) accordingly. Since there are no officially available Vampire binaries for Windows or Mac, you will probably have to compile Vampire from source on those systems. Keep in mind that there may be unknown issues, as the tactic has only been tested on Linux.

- When invoked, `vampire` writes the proof goal (translated into TPTP CNF format) in a temporary file, which is subsequently read by Vampire. You can change the location of this temporary file by modifying `temp_goal_file`.

- The tactic uses the shell script `vampire.sh` for writing the temporary goal file and calling Vampire. Set `vampire_script_path` to the location of this script (`./src/tactic/vampire` by default).
