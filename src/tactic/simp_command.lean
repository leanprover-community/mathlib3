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

setup_tactic_parser

namespace tactic

/-- Add the given list of `expr.local_const`s to the tactic state. -/
meta def add_local_consts_as_local_hyps (vars : list expr) : tactic unit :=
vars.mmap' $ λ var, do {
  tactic.assertv var.local_pp_name var.local_type var,
  tactic.skip
}

/-- From the `lean.parser` monad, synthesize a `tactic_state` which includes of all of the local
variables referenced in `e : pexpr`, and those variables which have been `include`ed in the local
context---precisely those variables which would be ambiently accessible if we were in a tactic block
where the goal was `to_expr e`, for example.

Returns a new `tactic_state` with these local variables added, and an `expr` obtained by resolving
`e` against the new state with `to_expr`. -/
meta def synthesize_tactic_state_with_variables_as_hyps (e : pexpr) : lean.parser (tactic_state × expr) :=
do /- First, in order to get `to_expr e` to resolve declared `variables`, we add all of the
      declared variables to a fake `tactic_state`, and perform the resolution. At the end,
      `to_expr e` has done the work of determining which variables were actually referenced, which
      we then obtain from `fe` via `expr.list_local_consts` (which, importantly, is not defined for
      `pexpr`s). -/
   vars ← list_available_include_vars,
   fake_e ← lean.parser.of_tactic $ lock_tactic_state $ do {
     add_local_consts_as_local_hyps vars,
     to_expr e
   },

   /- Now calculate lists of a) the explicitly `include`ed variables and b) the variables which were
      referenced in `e` when it was resolved to `fake_e`.

      It is important that we include variables of the kind a) because we want `simp` to have access
      to declared local instances, and it is important that we only restrict to variables of kind a)
      and b) together since we do not to recognise a hypothesis which is posited as a `variable`
      in the environment but not referenced in the `pexpr` we were passed.

      Once use case for this behaviour is running `simp` on the passed `pexpr`, since we do not want
      simp to use arbitrary hypotheses which were declared as `variables` in the local environment
      but not referenced in the expression to simplify (as one would be expect generally in tactic
      mode).
   -/
   included_vars ← list_include_var_names,
   let referenced_vars := fake_e.list_local_consts.map expr.local_pp_name,
   let vars := vars.filter $ λ var,
     (var.local_pp_name ∈ included_vars) ∨ (var.local_pp_name ∈ referenced_vars),

   /- Capture a tactic state where both of these kinds of variables have been added as local
      hypotheses, and resolve `e` against this state with `to_expr`, this time for real. -/
   lean.parser.of_tactic $ do {
     add_local_consts_as_local_hyps vars,
     e ← to_expr e,
     ts ← get_state,
     return (ts, e)
   }

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
@[user_command] meta def simp_cmd
  (_ : parse $ tk "#simp") : lean.parser unit :=
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
