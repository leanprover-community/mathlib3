import data.tree
import computability.primrec.basic

@[user_attribute]
meta def primrec_attr : user_attribute :=
{ name := `primrec,
  descr := "lemmas usable to prove a function is primitive recursive" }

namespace tactic

meta def is_tencodable (e : expr) : tactic bool :=
(do
   e' ← infer_type e,
   cache ← mk_instance_cache e',
   (cache', s) ← instance_cache.get cache ``tencodable,
   return tt) <|> (return ff)

-- meta def get_num_params (s : expr) : tactic ℕ :=
-- -- TODO: This should be based on the type of `s`, not the fact that `s` is a lambda function
-- do  guard s.is_lambda <|> fail "Not a lambda function",
--     mv ← mk_meta_var s.binding_domain,
--     e ←  instantiate_mvars (s.instantiate_lambdas [mv]),
--     f ← mfilter is_tencodable e.get_app_args,
--     return f.length

meta def get_num_params_aux : expr → list expr → tactic ℕ
| tp (x :: xs) :=
do tp' ← whnf tp reducible,
  (do guard tp'.is_arrow,
    to_expr ``(tencodable %%tp'.binding_domain) >>= mk_instance,
    (+1) <$> get_num_params_aux tp'.binding_body xs
  ) <|> (guard tp'.is_pi >> get_num_params_aux (tp'.instantiate_pis [x]) xs)
| tp [] := pure 0

meta def get_num_params (s : expr) : tactic ℕ :=
do guard s.is_lambda <|> fail "Not a lambda function",
   mv ← mk_meta_var s.binding_domain,
   e ←  instantiate_mvars (s.instantiate_lambdas [mv]),
   let args := e.get_app_args,
   tp ← infer_type e.get_app_fn,
   get_num_params_aux tp args

meta def get_goal_uncurry_base_fun : tactic (expr × option expr × expr) :=
(do `(@primrec _ _ _ %%dm_enc %%out_enc (@function.has_uncurry_base _ _) %%e) ← target,
   return (dm_enc, out_enc, e)) <|>
(do `(@primrec_pred _ _ %%dm_enc (@function.has_uncurry_base _ _) %%e) ← target,
   return (dm_enc, none, e))

meta def uncurry_target (md : transparency) : tactic unit :=
do fail_if_success get_goal_uncurry_base_fun,
   dsimp_target simp_lemmas.mk [``primrec, ``primrec_pred, ``function.has_uncurry.uncurry, ``id] { md := md },
   (to_expr ``(primrec1_iff_primrec_pred) >>= rewrite_target) <|>
   (to_expr ``(primrec1_iff_primrec) >>= rewrite_target)

-- meta def unfold_curry (unfold_lemmas : list name) (md : transparency) : tactic unit :=
-- do dunfold_target (``function.uncurry :: unfold_lemmas),
--    try (dsimp_target none [] { md := md, eta := ff })

inductive tactic_classes
| prim | poly | computable

meta def tactic_classes.attr_name : tactic_classes → name
| tactic_classes.prim := primrec_attr.name
| _ := default

meta def tactic_classes.fail_lemmas : tactic_classes → list name
| tactic_classes.prim := [``primrec.const, ``primrec.pair]
| _ := []

-- meta def tactic_classes.unfold_lemmas : tactic_classes → list name
-- | tactic_classes.prim := [``primrec₂, ``primrec₃, ``primrec₄, ``primrec₅, ``primrec_pred]
-- | _ := []

meta def tactic_classes.comp_lemmas : tactic_classes → list name
| tactic_classes.prim := [``primrec.const, ``primrec.comp, ``primrec.comp₂, ``primrec.comp₃, ``primrec.comp₄, ``primrec.comp₅]
| _ := []

meta def tactic_classes.fun_match : tactic_classes → tactic (expr × list name)
| tactic_classes.prim := (do `(primrec %%s) ← target, return (s,
  [``primrec.const, ``primrec.comp, ``primrec.comp₂, ``primrec.comp₃, ``primrec.comp₄, ``primrec.comp₅, ``primrec.comp₆])) <|>
  (do `(primrec_pred %%s) ← target, return (s,
  [``primrec.const, ``primrec_pred.comp, ``primrec_pred.comp₂, ``primrec_pred.comp₃]))
| _ := fail "Unimplemented class"

meta def try_comp (t : tactic_classes)
  (md : transparency) : tactic ℕ :=
do t.fail_lemmas.mfoldl (λ (_ : unit) x, fail_if_success (do
    x' ← resolve_name x,
    e ← to_expr x' tt ff,
    apply e { md := md })
   ) (),
   old_goal ← target,
   (target_fun, comp_lemmas) ← t.fun_match,
   n ← get_num_params target_fun,
   guard (0 < n ∧ n < comp_lemmas.length),
   s' ← to_expr $ expr.const (comp_lemmas.inth n) [],
   apply s' {md := md},
   try `[ any_goals { apply_instance, } ], -- why is this necessary??
   (fail_if_success (uncurry_target md >> target >>= λ t, unify t old_goal md)) <|>
    focus1 (apply_rules [] [t.attr_name] 50 { md := md } >> done),
  return n

meta def auto_computable (t : tactic_classes) (md : transparency := reducible) : list (tactic string) :=
[
  apply_rules [] [t.attr_name] 50 { md := md }
                        >> pure ("apply_rules with " ++ (to_string t.attr_name)),
  uncurry_target md >> pure ("uncurry_target md"),
  -- simp_to_bool >> pure "simp only [bool.to_bool_not, bool.to_bool_and, bool.to_bool_or]",
  try_comp t md >>= λ n, pure ("apply " ++ (to_string $ t.comp_lemmas.inth (n-1)))
]

meta def rw_arg_ext (new_tgt : pexpr) : tactic unit :=
do tgt ← target,
   guard (expr.is_app tgt),
   let arg := expr.app_arg tgt,
   n ← mk_fresh_name,
   to_expr ``(%%arg = %%new_tgt) >>= assert n,
   focus1 (symmetry >> tactic.funext),
   swap,
   resolve_name n >>= to_expr >>= rewrite_target

namespace interactive

setup_tactic_parser

meta def primrec
  (bang : parse $ optional (tk "!")) (trace : parse $ optional (tk "?")) (rw_tgt : parse $ (tk "using" *> texpr)?) (cfg : tidy.cfg := {}) :
  tactic unit :=
let md              := if bang.is_some then semireducible else reducible,
    polyfun_core := tactic.tidy { tactics := auto_computable tactic_classes.prim md, ..cfg },
    trace_fn        := if trace.is_some then show_term else id in
rw_tgt.elim skip (λ rw_tgt', rw_arg_ext rw_tgt') >>
trace_fn polyfun_core

meta def clean_target : tactic unit :=
(expr.clean <$> target) >>= unsafe_change

end interactive


end tactic

@[primrec] lemma unit_tree.primrec.of_primrec {f : unit_tree → unit_tree} (hf : primrec f) :
  unit_tree.primrec f := by simpa

@[primrec] lemma primrec1_of_primrec {α β : Type} [tencodable α] [tencodable β] {f : α → β}
  (hf : primrec f) : primrec1 f := by simpa

attribute [primrec]
  primrec.id
  primrec.const
  primrec.pair
  primrec.fst
  primrec.snd
  primrec.ite

@[primrec]
lemma primrec.id' {α} [tencodable α] : primrec (λ x : α, x) := primrec.id
