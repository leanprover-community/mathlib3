/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Scott Morrison, Kyle Miller
-/
import tactic.simp_command
import tactic.norm_num

/-!
## #norm_num
A user command to run `norm_num`.
-/

namespace tactic

setup_tactic_parser

/--
The basic usage is `#norm_num e`, where `e` is an expression,
which will print the `norm_num` form of `e`.

This accepts the same options as the `#simp` command.
You can specify additional simp lemmas as usual, for example using
`#norm_num [f, g] : e`, or `#norm_num with attr : e`.
(The colon is optional, but helpful for the parser.)
Like `#simp`, the command accepts `only` to prevent initial simplification,
which makes this behave similar to `norm_num1`.

`#norm_num` understands local variables, so you can use them to
introduce parameters.
-/
@[user_command] meta def norm_num_cmd (_ : parse $ tk "#norm_num") : lean.parser unit :=
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
  simp_result ← lean.parser.of_tactic $ λ _, do
  { /- Resolve the local variables added by the parser to `e` (when it was parsed) against the local
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

    e ← prod.fst <$> e.simp {} failed no_dflt attr_names hs <|> return e,
    e ← prod.fst <$> norm_num.derive e <|> return e,
    return e } ts,

  /- Trace the result. -/
  when (¬ is_trace_enabled_for `silence_simp_if_true ∨ simp_result ≠ expr.const `true [])
    (trace simp_result)

add_tactic_doc
{ name                     := "#norm_num",
  category                 := doc_category.cmd,
  decl_names               := [`tactic.norm_num_cmd],
  tags                     := ["simplification"] }

end tactic
