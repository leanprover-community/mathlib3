/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import data.dlist
import tactic.core

namespace tactic
open expr list

meta def match_fn (fn : expr) : expr → tactic (expr × expr)
| (app (app fn' e₀) e₁) := unify fn fn' $> (e₀, e₁)
| _ := failed

meta def fill_args : expr → tactic (expr × list expr)
| (pi n bi d b) :=
do v ← mk_meta_var d,
   (r, vs) ← fill_args (b.instantiate_var v),
   return (r, v::vs)
| e := return (e, [])

meta def mk_assoc_pattern' (fn : expr) : expr → tactic (dlist expr)
| e :=
  (do (e₀, e₁) ← match_fn fn e,
      (++) <$> mk_assoc_pattern' e₀ <*> mk_assoc_pattern' e₁) <|>
  pure (dlist.singleton e)

meta def mk_assoc_pattern (fn e : expr) : tactic (list expr) :=
dlist.to_list <$> mk_assoc_pattern' fn e

meta def mk_assoc (fn : expr) : list expr → tactic expr
| [] := failed
| [x] := pure x
| (x₀ :: x₁ :: xs) := mk_assoc (fn x₀ x₁ :: xs)

meta def chain_eq_trans : list expr → tactic expr
| [] := to_expr ``(rfl)
| [e] := pure e
| (e :: es) := chain_eq_trans es >>= mk_eq_trans e

meta def unify_prefix : list expr → list expr → tactic unit
| [] _ := pure ()
| _ [] := failed
| (x :: xs) (y :: ys) :=
unify x y >> unify_prefix xs ys

meta def match_assoc_pattern' (p : list expr) : list expr → tactic (list expr × list expr) | es :=
unify_prefix p es $> ([], es.drop p.length) <|>
  match es with
  | [] := failed
  | (x :: xs) := prod.map (cons x) id <$> match_assoc_pattern' xs
  end

meta def match_assoc_pattern (fn p e : expr) : tactic (list expr × list expr) :=
do p' ← mk_assoc_pattern fn p,
   e' ← mk_assoc_pattern fn e,
   match_assoc_pattern' p' e'

meta def mk_eq_proof (fn : expr) (e₀ e₁ : list expr) (p : expr) : tactic (expr × expr × expr) :=
do (l, r) ← infer_type p >>= match_eq,
   if e₀.empty ∧ e₁.empty then pure (l, r, p)
   else do
     l' ← mk_assoc fn (e₀ ++ [l] ++ e₁),
     r' ← mk_assoc fn (e₀ ++ [r] ++ e₁),
     t  ← infer_type l',
     v  ← mk_local_def `x t,
     e  ← mk_assoc fn (e₀ ++ [v] ++ e₁),
     p  ← mk_congr_arg (e.lambdas [v]) p,
     p' ← mk_id_eq l' r' p,
     return (l', r', p')

meta def assoc_root (fn assoc : expr) : expr → tactic (expr × expr) | e :=
(do (e₀, e₁) ← match_fn fn e,
    (ea, eb) ← match_fn fn e₁,
    let e' := fn (fn e₀ ea) eb,
    p' ← mk_eq_symm (assoc e₀ ea eb),
    (e'', p'') ← assoc_root e',
    prod.mk e'' <$> mk_eq_trans p' p'') <|>
prod.mk e <$> mk_eq_refl e

meta def assoc_refl' (fn assoc : expr) : expr → expr → tactic expr
| l r := (is_def_eq l r >> mk_eq_refl l) <|> do
  (l', l_p)  ← assoc_root fn assoc l <|> fail "A",
  (el₀, el₁) ← match_fn   fn l' <|> fail "B",
  (r', r_p)  ← assoc_root fn assoc r <|> fail "C",
  (er₀, er₁) ← match_fn   fn r' <|> fail "D",
  p₀ ← assoc_refl' el₀ er₀,
  p₁ ← is_def_eq el₁ er₁ >> mk_eq_refl el₁,
  f_eq ← mk_congr_arg fn p₀ <|> fail "G",
  p' ← mk_congr f_eq p₁ <|> fail "H",
  r_p' ← mk_eq_symm r_p,
  chain_eq_trans [l_p, p', r_p']

meta def assoc_refl (fn : expr) : tactic unit :=
do (l, r) ← target >>= match_eq,
   assoc ← mk_mapp ``is_associative.assoc [none, fn, none]
     <|> fail format!"{fn} is not associative",
   assoc_refl' fn assoc l r >>= tactic.exact

meta def flatten (fn assoc e : expr) : tactic (expr × expr) :=
do ls ← mk_assoc_pattern fn e,
   e' ← mk_assoc fn ls,
   p  ← assoc_refl' fn assoc e e',
   return (e', p)

meta def assoc_rewrite_intl (assoc h e : expr) : tactic (expr × expr) :=
do t ← infer_type h,
   (lhs, rhs) ← match_eq t,
   let fn  := lhs.app_fn.app_fn,
   (l, r) ← match_assoc_pattern fn lhs e,
   (lhs', rhs', h') ← mk_eq_proof fn l r h,
   e_p ← assoc_refl' fn assoc e lhs',
   (rhs'', rhs_p) ← flatten fn assoc rhs',
   final_p ← chain_eq_trans [e_p, h', rhs_p],
   return (rhs'', final_p)

-- TODO(Simon): visit expressions built of `fn` nested inside other such expressions:
-- e.g.: x + f (a + b + c) + y should generate two rewrite candidates
meta def enum_assoc_subexpr' (fn : expr) : expr → tactic (dlist expr)
| e :=
  dlist.singleton e <$ (match_fn fn e >> guard (¬ e.has_var)) <|>
  expr.mfoldl (λ es e', (++ es) <$> enum_assoc_subexpr' e') dlist.empty e

meta def enum_assoc_subexpr (fn e : expr) : tactic (list expr) :=
dlist.to_list <$> enum_assoc_subexpr' fn e

meta def mk_assoc_instance (fn : expr) : tactic expr :=
do t ← mk_mapp ``is_associative [none, fn],
   inst ← prod.snd <$> solve_aux t assumption <|>
     (mk_instance t >>= assertv `_inst t) <|>
     fail format!"{fn} is not associative",
   mk_mapp ``is_associative.assoc [none, fn, inst]

meta def assoc_rewrite (h e : expr) (opt_assoc : option expr := none) :
  tactic (expr × expr × list expr) :=
do (t, vs) ← infer_type h >>= fill_args,
   (lhs, rhs) ← match_eq t,
   let fn := lhs.app_fn.app_fn,
   es ← enum_assoc_subexpr fn e,
   assoc ← match opt_assoc with
           | none := mk_assoc_instance fn
           | (some assoc) := pure assoc
           end,
   (_, p) ← mfirst (assoc_rewrite_intl assoc $ h.mk_app vs) es,
   (e', p', _) ← tactic.rewrite p e,
   pure (e', p', vs)

meta def assoc_rewrite_target (h : expr) (opt_assoc : option expr :=  none) :
  tactic unit :=
do tgt ← target,
   (tgt', p, _) ← assoc_rewrite h tgt opt_assoc,
   replace_target tgt' p

meta def assoc_rewrite_hyp (h hyp : expr) (opt_assoc : option expr := none) :
  tactic expr :=
do tgt ← infer_type hyp,
   (tgt', p, _) ← assoc_rewrite h tgt opt_assoc,
   replace_hyp hyp tgt' p

namespace interactive

open lean.parser interactive interactive.types tactic

private meta def assoc_rw_goal (rs : list rw_rule) : tactic unit :=
rs.mmap' $ λ r, do
 save_info r.pos,
 eq_lemmas ← get_rule_eqn_lemmas r,
 orelse'
   (do e ← to_expr' r.rule, assoc_rewrite_target e)
   (eq_lemmas.mfirst $ λ n, do e ← mk_const n, assoc_rewrite_target e)
   (eq_lemmas.empty)

private meta def uses_hyp (e : expr) (h : expr) : bool :=
e.fold ff $ λ t _ r, r || (t = h)

private meta def assoc_rw_hyp : list rw_rule → expr → tactic unit
| []      hyp := skip
| (r::rs) hyp := do
  save_info r.pos,
  eq_lemmas ← get_rule_eqn_lemmas r,
  orelse'
    (do e ← to_expr' r.rule, when (¬ uses_hyp e hyp) $ assoc_rewrite_hyp e hyp >>= assoc_rw_hyp rs)
    (eq_lemmas.mfirst $ λ n, do e ← mk_const n, assoc_rewrite_hyp e hyp >>= assoc_rw_hyp rs)
    (eq_lemmas.empty)

private meta def assoc_rw_core (rs : parse rw_rules) (loca : parse location) : tactic unit :=
match loca with
| loc.wildcard := loca.try_apply (assoc_rw_hyp rs.rules) (assoc_rw_goal rs.rules)
| _            := loca.apply (assoc_rw_hyp rs.rules) (assoc_rw_goal rs.rules)
end >> try reflexivity
    >> try (returnopt rs.end_pos >>= save_info)

/--
`assoc_rewrite [h₀,← h₁] at ⊢ h₂` behaves like `rewrite [h₀,← h₁] at ⊢ h₂`
with the exception that associativity is used implicitly to make rewriting
possible.

It works for any function `f` for which an `is_associative f` instance can be found.

```
example {α : Type*} (f : α → α → α) [is_associative α f] (a b c d x : α) :
  let infix `~` := f in
  b ~ c = x → (a ~ b ~ c ~ d) = (a ~ x ~ d) :=
begin
  intro h,
  assoc_rw h, 
end
```
-/
meta def assoc_rewrite (q : parse rw_rules) (l : parse location) : tactic unit :=
propagate_tags (assoc_rw_core q l)

/-- synonym for `assoc_rewrite` -/
meta def assoc_rw (q : parse rw_rules) (l : parse location) : tactic unit :=
assoc_rewrite q l

add_tactic_doc
{ name                     := "assoc_rewrite",
  category                 := doc_category.tactic,
  decl_names               := [`tactic.interactive.assoc_rewrite, `tactic.interactive.assoc_rw],
  tags                     := ["rewriting"],
  inherit_description_from := `tactic.interactive.assoc_rewrite }

end interactive
end tactic
