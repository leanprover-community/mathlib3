- The `vampire` tactic requires the Vampire theorem prover on your system. It has been tested with version 4.2.2 of Vampire without Z3, which you can obtain at: https://vprover.github.io/download.html

- The tactic requires both the executable file `vampire` and the shell script `vampire.sh` (in `tactic/vampire`) on your path.

- Since there are no officially available Vampire binaries for Windows or Mac, you will have to compile Vampire from source on those systems. Keep in mind that there may be unknown issues, as the tactic has only been tested on Linux.

- When invoked, `vampire` writes the proof goal (translated into TPTP CNF format) in a temporary file, which is subsequently read by Vampire. In most cases the default location for this file should work, but if necessary you can change it by modifying `temp_goal_file_path` in `main.lean`.
