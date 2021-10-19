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

/-- Strip all annotations of non local constants in the passed `expr`. (This is required in an
incantation later on in order to make the C++ simplifier happy.) -/
private meta def strip_annotations_from_all_non_local_consts {elab : bool} (e : expr elab)
  : expr elab :=
expr.unsafe_cast $ e.unsafe_cast.replace $ λ e n,
  match e.is_annotation with
  | some (_, expr.local_const _ _ _ _) := none
  | some (_, _) := e.erase_annotations
  | _ := none
  end

/-- `simp_arg_type.to_pexpr` retrieves the `pexpr` underlying the given `simp_arg_type`, if there is
one. -/
meta def simp_arg_type.to_pexpr : simp_arg_type → option pexpr
| sat@(simp_arg_type.expr e) := e
| sat@(simp_arg_type.symm_expr e) := e
| sat := none

/-- Incantation which prepares a `pexpr` in a `simp_arg_type` for use by the simplifier after
`expr.replace_subexprs` as been called to replace some of its local variables. -/
private meta def replace_subexprs_for_simp_arg (e : pexpr) (rules : list (expr × expr)) : pexpr :=
strip_annotations_from_all_non_local_consts $ pexpr.of_expr $ e.unsafe_cast.replace_subexprs rules

/-- `simp_arg_type.replace_subexprs` calls `expr.replace_subexprs` on the underlying `pexpr`, if
there is one, and then prepares the result for use by the simplifier. -/
meta def simp_arg_type.replace_subexprs : simp_arg_type → list (expr × expr) → simp_arg_type
| (simp_arg_type.expr      e) rules :=
    simp_arg_type.expr      $ replace_subexprs_for_simp_arg e rules
| (simp_arg_type.symm_expr e) rules :=
    simp_arg_type.symm_expr $ replace_subexprs_for_simp_arg e rules
| sat rules := sat

setup_tactic_parser

/- Turn off the messages if the result is exactly `true` with this option. -/
declare_trace silence_simp_if_true

/--
The basic usage is `#simp e`, where `e` is an expression,
which will print the simplified form of `e`.

You can specify additional simp lemmas as usual for example using
`#simp [f, g] : e`, or `#simp with attr : e`.
(The colon is optional, but helpful for the parser.)

`#simp` understands local variables, so you can use them to
introduce parameters.
-/
@[user_command] meta def simp_cmd (_ : parse $ tk "#simp") : lean.parser unit :=
do
  no_dflt ← only_flag,
  hs ← simp_arg_list,
  attr_names ← with_ident_list,
  o ← optional (tk ":"),
  e ← types.texpr,

  /- Retrieve the `pexpr`s parsed as part of the simp args, and collate them into a big list. -/
  let hs_es := list.join $ hs.map $ option.to_list ∘ simp_arg_type.to_pexpr,

  /- Synthesize a `tactic_state` including local variables as hypotheses under which `expr.simp`
     may be safely called with expected behaviour given the `variables` in the environment. -/
  (ts, mappings) ← synthesize_tactic_state_with_variables_as_hyps (e :: hs_es),

  /- Enter the `tactic` monad, *critically* using the synthesized tactic state `ts`. -/
  simp_result ← lean.parser.of_tactic $ λ _, do {
    /- Resolve the local variables added by the parser to `e` (when it was parsed) against the local
       hypotheses added to the `ts : tactic_state` which we are using. -/
    e ← to_expr e,

    /- Replace the variables referenced in the passed `simp_arg_list` with the `expr`s corresponding
       to the local hypotheses we created.

       We would prefer to just elaborate the `pexpr`s encoded in the `simp_arg_list` against the
       tactic state we have created (as we could with `e` above), but the simplifier expects
       `pexpr`s and not `expr`s. Thus, we just modify the `pexpr`s now and let `simp` do the
       elaboration when the time comes.

       You might think that we could just examine each of these `pexpr`s, call `to_expr` on them,
       and then call `to_pexpr` afterward and save the results over the original `pexprs`. Due to
       how functions like `simp_lemmas.add_pexpr` are implemented in the core library, the `simp`
       framework is not robust enough to handle this method. When pieces of expressions like
       annotation macros are injected, the direct patten matches in the `simp_lemmas.*` codebase
       fail, and the lemmas we want don't get added.
       -/
    let hs := hs.map $ λ sat, sat.replace_subexprs mappings,

    /- Finally, call `expr.simp` with `e` and return the result. -/
    prod.fst <$> e.simp {} failed no_dflt attr_names hs } ts,

  /- Trace the result. -/
  when (¬ is_trace_enabled_for `silence_simp_if_true ∨ simp_result ≠ expr.const `true [])
    (trace simp_result)

add_tactic_doc
{ name                     := "#simp",
  category                 := doc_category.cmd,
  decl_names               := [`tactic.simp_cmd],
  tags                     := ["simplification"] }

end tactic
