/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

namespace expr
open tactic

protected meta def to_pos_nat : expr → option ℕ
| `(has_one.one _) := some 1
| `(bit0 %%e) := bit0 <$> e.to_pos_nat
| `(bit1 %%e) := bit1 <$> e.to_pos_nat
| _           := none

protected meta def to_nat : expr → option ℕ
| `(has_zero.zero _) := some 0
| e                  := e.to_pos_nat

protected meta def to_int : expr → option ℤ
| `(has_neg.neg %%e) := do n ← e.to_nat, some (-n)
| e                  := do n ← e.to_nat, return n

protected meta def of_nat (α : expr) : ℕ → tactic expr :=
nat.binary_rec
  (tactic.mk_mapp ``has_zero.zero [some α, none])
  (λ b n tac, if n = 0 then mk_mapp ``has_one.one [some α, none] else
    do e ← tac, tactic.mk_app (cond b ``bit1 ``bit0) [e])

protected meta def of_int (α : expr) : ℤ → tactic expr
| (n : ℕ) := expr.of_nat α n
| -[1+ n] := do
  e ← expr.of_nat α (n+1),
  tactic.mk_app ``has_neg.neg [e]

end expr

namespace tactic

meta definition mk_local (n : name) : expr :=
expr.local_const n n binder_info.default (expr.const n [])

meta def exact_dec_trivial : tactic unit := `[exact dec_trivial]

meta def replace_at (tac : expr → tactic (expr × expr)) (hs : list expr) (tgt : bool) : tactic bool :=
do to_remove ← hs.mfilter $ λ h, do {
         h_type ← infer_type h,
         (do (new_h_type, pr) ← tac h_type,
             assert h.local_pp_name new_h_type,
             mk_eq_mp pr h >>= tactic.exact >> return tt)
         <|>
         (return ff) },
   goal_simplified ← if tgt then (do
     (new_t, pr) ← target >>= tac,
     replace_target new_t pr,
     return tt) <|> return ff else return ff,
   to_remove.mmap' (λ h, try (clear h)),
   return (¬ to_remove.empty ∨ goal_simplified)

meta def simp_bottom_up' (post : expr → tactic (expr × expr)) (e : expr) (cfg : simp_config := {}) : tactic (expr × expr) :=
prod.snd <$> simplify_bottom_up () (λ _, (<$>) (prod.mk ()) ∘ post) e cfg

meta structure instance_cache :=
(α : expr)
(univ : level)
(inst : name_map expr)

meta def mk_instance_cache (α : expr) : tactic instance_cache :=
do u ← mk_meta_univ,
   infer_type α >>= unify (expr.sort (level.succ u)),
   u ← get_univ_assignment u,
   return ⟨α, u, mk_name_map⟩

namespace instance_cache

meta def get (c : instance_cache) (n : name) : tactic (instance_cache × expr) :=
match c.inst.find n with
| some i := return (c, i)
| none := do e ← mk_app n [c.α] >>= mk_instance,
  return (⟨c.α, c.univ, c.inst.insert n e⟩, e)
end

open expr
meta def append_typeclasses : expr → instance_cache → list expr →
  tactic (instance_cache × list expr)
| (pi _ binder_info.inst_implicit (app (const n _) (var _)) body) c l :=
  do (c, p) ← c.get n, return (c, p :: l)
| _ c l := return (c, l)

meta def mk_app (c : instance_cache) (n : name) (l : list expr) : tactic (instance_cache × expr) :=
do d ← get_decl n,
   (c, l) ← append_typeclasses d.type.binding_body c l,
   return (c, (expr.const n [c.univ]).mk_app (c.α :: l))

end instance_cache

/-- Reset the instance cache for the main goal. -/
meta def reset_instance_cache : tactic unit := unfreeze_local_instances

meta def match_head (e : expr) : expr → tactic unit
| e' :=
    unify e e'
<|> do `(_ → %%e') ← whnf e',
       v ← mk_mvar,
       match_head (e'.instantiate_var v)

meta def find_matching_head : expr → list expr → tactic (list expr)
| e []         := return []
| e (H :: Hs) :=
  do t ← infer_type H,
     ((::) H <$ match_head e t <|> pure id) <*> find_matching_head e Hs

meta def subst_locals (s : list (expr × expr)) (e : expr) : expr :=
(e.abstract_locals (s.map (expr.local_uniq_name ∘ prod.fst)).reverse).instantiate_vars (s.map prod.snd)

meta def set_binder : expr → list binder_info → expr
 | e [] := e
 | (expr.pi v _ d b) (bi :: bs) := expr.pi v bi d (set_binder b bs)
 | e _ := e

end tactic
