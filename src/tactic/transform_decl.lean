/-
Copyright (c) 2017 Mario Carneiro All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import meta.expr
import meta.rb_map

namespace tactic

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
    let decl := decl.update_with_fun (name.map_prefix f) tgt,
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
