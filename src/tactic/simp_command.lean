/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Scott Morrison
-/
import tactic.core

/-!
## #simp
A user command to run the simplifier.
-/

namespace tactic

setup_tactic_parser

/--
The basic usage is `#simp e`, where `e` is an expression,
which will print the simplified form of `e`.

You can specify additional simp lemmas as usual for example using
`#simp [f, g] : e`, or `#simp with attr : e`.
(The colon is optional, but helpful for the parser.)

`#simp` does not understand local variables,
so you will need to use lambda-expressions
to introduce parameters.
-/
@[user_command] meta def simp_cmd (_ : parse $ tk "#simp") : lean.parser unit :=
do
  no_dflt ← only_flag,
  hs ← simp_arg_list,
  attr_names ← with_ident_list,
  o ← optional (tk ":"),
  e ← types.texpr,

  /- Synthesize a `tactic_state` including local variables as hypotheses under which `expr.simp`
    may be safely called with expected behaviour given the `variables` in the environment.  -/
  (ts, e) ← synthesize_tactic_state_with_variables_as_hyps e,
  /- Call `expr.simp` with `e`, *critically* using the synthesized tactic state `ts`. -/
  simp_result ← lean.parser.of_tactic $ λ _,
    (prod.fst <$> e.simp {} failed no_dflt attr_names hs) ts,

  /- Trace the result. -/
  trace simp_result

add_tactic_doc
{ name                     := "#simp",
  category                 := doc_category.cmd,
  decl_names               := [`tactic.simp_cmd],
  tags                     := ["simplification"] }

end tactic
