# The Mathlib Test Directory

In this directory we collect various tests for the commands, tactics and metaprograms written in
mathlib (see [the tactic folder](../src/tactic)).

Tests for all tactics are highly encouraged, especially if they are used sparingly in mathlib.
Here are some guidelines for writing a test:

* Make sure that the test fails if something unexpected happens. Use `guard`, `guard_target`, `guard_hyp`, `get_decl` or similar tactics that fail if the tactic state is incorrect.
* Make sure that the test is silent, i.e. produces no output when it succeeds. This makes it easy to spot the tests that actually failed. Furthermore, it is unlikely that anyone will notice the output changing if the test keeps succeeding.

Some tips to make a test silent:
* Instead of `trace e`, write `guard (e = expected_expression)`.
* If you write a tactic/command that normally produces output, consider adding an option that silences it. See for example the uses of `set_option trace.silence_library_search true` in the [library_search](library_search) folder.
* Do not prove a lemma using `admit` or `sorry`. Instead make sure that the lemma is provable, and prove it by `assumption` or `trivial` or similar.
