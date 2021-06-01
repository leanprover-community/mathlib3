/-
Copyright (c) 2017 Mario Carneiro All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import meta.expr
import meta.rb_map

namespace tactic

open expr
/-- `additive_test e ff` tests whether the expression contains no constant that is not applied to
  arguments.
  `additive_test e tt` is the same, except that it returns `tt` if the expression itself
  is a constant.
  This is used in `@[to_additive]` for deciding which subexpressions to transform: we only transform
  constants if `additive_test` applied to their first argument returns `tt`.
  This means we will replace expression applied to e.g. `α` or `α × β`, but not when applied to
  e.g. `ℕ` or `ℝ × α`. -/
meta def additive_test : bool → expr → bool
| b (var n)                := tt
| b (sort l)               := tt
| b (const n ls)           := b
| b (mvar n m t)           := tt
| b (local_const n m bi t) := tt
| b (app e f)              := additive_test tt e && additive_test ff f
| b (lam n bi e t)         := additive_test ff t
| b (pi n bi e t)          := additive_test ff t
| b (elet n g e f)         := additive_test ff e && additive_test ff f
| b (macro d args)         := tt

private meta def transform_decl_with_prefix_fun_aux (f : name → option name) (pre tgt_pre : name)
  (attrs : list name) :
  name → command :=
λ src,
do
  let tgt := src.map_prefix (λ n, if n = pre then some tgt_pre else none),
  (get_decl tgt >> skip) <|>
  do
    decl ← get_decl src,
    (decl.type.list_names_with_prefix pre).mfold () (λ n _, transform_decl_with_prefix_fun_aux n),
    (decl.value.list_names_with_prefix pre).mfold () (λ n _, transform_decl_with_prefix_fun_aux n),
    is_protected ← is_protected_decl src,
    let decl := decl.update_with_fun (name.map_prefix f) (additive_test ff) tgt,
    if is_protected then add_protected_decl decl else add_decl decl,
    attrs.mmap' (λ n, copy_attribute n src tgt)

/--
Make a new copy of a declaration,
replacing fragments of the names of identifiers in the type and the body using the function `f`.
This is used to implement `@[to_additive]`.
-/
meta def transform_decl_with_prefix_fun (f : name → option name) (src tgt : name) (attrs : list name) :
  command :=
do transform_decl_with_prefix_fun_aux f src tgt attrs src,
   ls ← get_eqn_lemmas_for tt src,
   ls.mmap' $ transform_decl_with_prefix_fun_aux f src tgt attrs

/--
Make a new copy of a declaration,
replacing fragments of the names of identifiers in the type and the body using the dictionary `dict`.
This is used to implement `@[to_additive]`.
-/
meta def transform_decl_with_prefix_dict (dict : name_map name) (src tgt : name) (attrs : list name) :
  command :=
transform_decl_with_prefix_fun dict.find src tgt attrs

end tactic
