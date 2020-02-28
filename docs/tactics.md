# Mathlib tactics

In addition to the [tactics found in the core library](https://leanprover.github.io/reference/tactics.html),
mathlib provides a number of specific interactive tactics.
Here we document the mostly commonly used ones, as well as some underdocumented tactics from core.

## default_dec_tac'

`default_dec_tac'` is a replacement for the core tactic `default_dec_tac`, fixing a bug. This
bug is often indicated by a message `nested exception message: tactic failed, there are no goals to be solved`,and solved by appending `using_well_founded wf_tacs` to the recursive definition.
See also additional documentation of `using_well_founded` in
[docs/extras/well_founded_recursion.md](extras/well_founded_recursion.md).
