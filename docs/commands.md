# Commands

Commands provide a way to interact with and modify a Lean environment outside of the context of a proof.
Familiar commands from core Lean include `#check`, `#eval`, and `run_cmd`.

Mathlib provides a number of commands that offer customized behavior. These commands fall into two
categories:

* *Transient* commands are used to query the environment for information, but do not modify it,
  and have no effect on the following proofs. These are useful as a user to get information from Lean.
  They should not appear in "finished" files.
  Transient commands typically begin with the symbol `#`.
  `#check` is a standard example of a transient command.

* *Permanent* commands modify the environment. Removing a permanent command from a file may affect
  the following proofs. `set_option class.instance_max_depth 500` is a standard example of a
  permanent command.

User-defined commands can have unintuitive interactions with the parser. For the most part, this is
not something to worry about. However, you may occasionally see strange error messages when using
mathlib commands: for instance, running these commands immediately after `import file.name` will
produce an error. An easy solution is to run a built-in no-op command in between, for example:

```
import data.nat.basic

run_cmd tactic.skip -- this serves as a "barrier" between `import` and `#find`

#find _ + _ = _ + _
```
