/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.core
import tactic.doc_commands

namespace tactic
namespace interactive

open interactive
open interactive.types
open tactic

/--
`trunc_cases e` performs case analysis on a `trunc` expression,
preferentially using the recursor `trunc.rec_on_subsingleton`
when the goal is a subsingleton, and using `trunc.rec` otherwise.

`trunc_cases e with h` names the new hypothesis `h`.
If `e` is a local hypothesis already,
`trunc_cases` defaults to reusing the same name

Additionally, if the new hypothesis is a type class,
reset the instance cache.
-/
meta def trunc_cases (e : parse texpr) (ids : parse with_ident_list) : tactic unit :=
do
  e ← to_expr e,
  let ids := if ids = [] ∧ e.is_local_constant then [e.local_pp_name] else ids,
  e ← if e.is_local_constant then return e else note_anon none e,
  tgt ← target,
  ss ← succeeds (mk_app `subsingleton [tgt] >>= mk_instance),
  (_, [e], _) :: _ ← if ss then
    tactic.induction e ids `trunc.rec_on_subsingleton
  else
    tactic.induction e ids,
  c ← infer_type e >>= is_class,
  when c unfreeze_local_instances

end interactive
end tactic

add_tactic_doc
{ name                     := "trunc_cases",
  category                 := doc_category.tactic,
  decl_names               := [`tactic.interactive.trunc_cases],
  tags                     := ["case bashing"] }
