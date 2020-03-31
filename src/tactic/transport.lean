import meta.expr meta.rb_map

namespace tactic

private meta def transport_with_prefix_fun_aux (f : name → option name) (pre tgt_pre : name)
  (attrs : list name) :
  name → command :=
λ src,
do
  let tgt := src.map_prefix (λ n, if n = pre then some tgt_pre else none),
  (get_decl tgt >> skip) <|>
  do
    decl ← get_decl src,
    (decl.type.list_names_with_prefix pre).mfold () (λ n _, transport_with_prefix_fun_aux n),
    (decl.value.list_names_with_prefix pre).mfold () (λ n _, transport_with_prefix_fun_aux n),
    is_protected ← is_protected_decl src,
    let decl := decl.update_with_fun (name.map_prefix f) tgt,
    if is_protected then add_protected_decl decl else add_decl decl,
    attrs.mmap' (λ n, copy_attribute n src tgt)

meta def transport_with_prefix_fun (f : name → option name) (src tgt : name) (attrs : list name) :
  command :=
do transport_with_prefix_fun_aux f src tgt attrs src,
   ls ← get_eqn_lemmas_for tt src,
   ls.mmap' $ transport_with_prefix_fun_aux f src tgt attrs

meta def transport_with_prefix_dict (dict : name_map name) (src tgt : name) (attrs : list name) :
  command :=
transport_with_prefix_fun dict.find src tgt attrs

end tactic
