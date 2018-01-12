/-
Copyright (c) 2017 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Mario Carneiro

Evaluating arithmetic expressions including *, +, -, ^, ≤
-/

import algebra.group_power data.rat tactic.interactive data.hash_map

universes u v w
open tactic

namespace expr

protected meta def to_pos_nat : expr → option ℕ
| `(has_one.one _) := some 1
| `(bit0 %%e) := bit0 <$> e.to_pos_nat
| `(bit1 %%e) := bit1 <$> e.to_pos_nat
| _           := none

protected meta def to_nat : expr → option ℕ
| `(has_zero.zero _) := some 0
| e                  := e.to_pos_nat

protected meta def to_pos_rat : expr → option ℚ
| `(%%e₁ / %%e₂) := do m ← e₁.to_nat, n ← e₂.to_nat, some (rat.mk m n)
| e              := do n ← e.to_nat, return (rat.of_int n)

protected meta def to_int : expr → option ℤ
| `(has_neg.neg %%e) := do n ← e.to_nat, some (-n)
| e                  := do n ← e.to_nat, return n

protected meta def to_rat : expr → option ℚ
| `(has_neg.neg %%e) := do q ← e.to_pos_rat, some (-q)
| e                  := e.to_pos_rat

protected meta def of_nat (α : expr) : ℕ → tactic expr :=
nat.binary_rec
  (tactic.mk_mapp ``has_zero.zero [some α, none])
  (λ b n tac, if n = 0 then mk_mapp ``has_one.one [some α, none] else
    do e ← tac, tactic.mk_app (cond b ``bit1 ``bit0) [e])

protected meta def of_rat (α : expr) : ℚ → tactic expr
| ⟨(n:ℕ), d, h, c⟩   := do
  e₁ ← expr.of_nat α n,
  if d = 1 then return e₁ else
  do e₂ ← expr.of_nat α d,
  tactic.mk_app ``has_div.div [e₁, e₂]
| ⟨-[1+n], d, h, c⟩ := do
  e₁ ← expr.of_nat α (n+1),
  e ← (if d = 1 then return e₁ else do
    e₂ ← expr.of_nat α d,
    tactic.mk_app ``has_div.div [e₁, e₂]),
  tactic.mk_app ``has_neg.neg [e]
end expr

namespace tactic

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

end tactic

namespace norm_num
variable {α : Type u}

theorem bit0_zero [add_group α] : bit0 (0 : α) = 0 := add_zero _
 
theorem bit1_zero [add_group α] [has_one α] : bit1 (0 : α) = 1 :=
by rw [bit1, bit0_zero, zero_add]

local infix ` ^ ` := monoid.pow
lemma pow_bit0_helper [monoid α] (a t : α) (b : ℕ) (h : a ^ b = t) :
  a ^ bit0 b = t * t :=
by simp [pow_bit0, h]

lemma pow_bit1_helper [monoid α] (a t : α) (b : ℕ) (h : a ^ b = t) :
  a ^ bit1 b = t * t * a :=
by simp [pow_bit1, h]

lemma lt_add_of_pos_helper [ordered_cancel_comm_monoid α]
  (a b c : α) (h : a + b = c) (h₂ : 0 < b) : a < c :=
h ▸ (lt_add_iff_pos_right _).2 h₂

lemma nat_div_helper (a b q r : ℕ) (h : r + q * b = a) (h₂ : r < b) : a / b = q :=
by rw [← h, nat.add_mul_div_right _ _ (lt_of_le_of_lt (nat.zero_le _) h₂),
       nat.div_eq_of_lt h₂, zero_add]

lemma int_div_helper (a b q r : ℤ) (h : r + q * b = a) (h₁ : 0 ≤ r) (h₂ : r < b) : a / b = q :=
by rw [← h, int.add_mul_div_right _ _ (ne_of_gt (lt_of_le_of_lt h₁ h₂)),
       int.div_eq_zero_of_lt h₁ h₂, zero_add]

lemma nat_mod_helper (a b q r : ℕ) (h : r + q * b = a) (h₂ : r < b) : a % b = r :=
by rw [← h, nat.add_mul_mod_self_right, nat.mod_eq_of_lt h₂]

lemma int_mod_helper (a b q r : ℤ) (h : r + q * b = a) (h₁ : 0 ≤ r) (h₂ : r < b) : a % b = r :=
by rw [← h, int.add_mul_mod_self, int.mod_eq_of_lt h₁ h₂]

meta structure instance_cache :=
(α : expr)
(univ : level)
(inst : hash_map name (λ_, expr))

meta def mk_instance_cache (α : expr) : tactic instance_cache :=
do u ← mk_meta_univ,
   infer_type α >>= unify (expr.sort (level.succ u)),
   u ← get_univ_assignment u,
   return ⟨α, u, mk_hash_map (λ n, (expr.const n []).hash)⟩

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

meta def eval_pow (simp : expr → tactic (expr × expr)) : expr → tactic (expr × expr)
| `(monoid.pow %%e₁ 0) := do
  p ← mk_app ``pow_zero [e₁],
  a ← infer_type e₁,
  o ← mk_app ``has_one.one [a],
  return (o, p)
| `(monoid.pow %%e₁ 1) := do
  p ← mk_app ``pow_one [e₁],
  return (e₁, p)
| `(monoid.pow %%e₁ (bit0 %%e₂)) := do
  e ← mk_app ``monoid.pow [e₁, e₂],
  (e', p) ← simp e,
  p' ← mk_app ``norm_num.pow_bit0_helper [e₁, e', e₂, p],
  e'' ← to_expr ``(%%e' * %%e'),
  return (e'', p')
| `(monoid.pow %%e₁ (bit1 %%e₂)) := do
  e ← mk_app ``monoid.pow [e₁, e₂],
  (e', p) ← simp e,
  p' ← mk_app ``norm_num.pow_bit1_helper [e₁, e', e₂, p],
  e'' ← to_expr ``(%%e' * %%e' * %%e₁),
  return (e'', p')
| `(nat.pow %%e₁ %%e₂) := do
  p₁ ← mk_app ``nat.pow_eq_pow [e₁, e₂],
  e ← mk_app ``monoid.pow [e₁, e₂],
  (e', p₂) ← simp e,
  p ← mk_eq_trans p₁ p₂,
  return (e', p)
| _ := failed

meta def prove_pos : instance_cache → expr → tactic (instance_cache × expr)
| c `(has_one.one _) := do (c, p) ← c.mk_app ``zero_lt_one [], return (c, p)
| c `(bit0 %%e)      := do (c, p) ← prove_pos c e, (c, p) ← c.mk_app ``bit0_pos [e, p], return (c, p)
| c `(bit1 %%e)      := do (c, p) ← prove_pos c e, (c, p) ← c.mk_app ``bit1_pos' [e, p], return (c, p)
| c `(%%e₁ / %%e₂)   := do
  (c, p₁) ← prove_pos c e₁, (c, p₂) ← prove_pos c e₂,
  (c, p) ← c.mk_app ``div_pos_of_pos_of_pos [e₁, e₂, p₁, p₂],
  return (c, p)
| c e                       := failed

meta def prove_lt (simp : expr → tactic (expr × expr)) : instance_cache → expr → expr → tactic (instance_cache × expr)
| c `(- %%e₁) `(- %%e₂) := do
  (c, p) ← prove_lt c e₁ e₂,
  (c, p) ← c.mk_app ``neg_lt_neg [e₁, e₂, p],
  return (c, p)
| c `(- %%e₁) `(has_zero.zero _) := do
  (c, p) ← prove_pos c e₁,
  (c, p) ← c.mk_app ``neg_neg_of_pos [e₁, p],
  return (c, p)
| c `(- %%e₁) e₂ := do
  (c, p₁) ← prove_pos c e₁,
  (c, me₁) ← c.mk_app ``has_neg.neg [e₁],
  (c, p₁) ← c.mk_app ``neg_neg_of_pos [e₁, p₁],
  (c, p₂) ← prove_pos c e₂,
  (c, z) ← c.mk_app ``has_zero.zero [],
  (c, p) ← c.mk_app ``lt_trans [me₁, z, e₂, p₁, p₂],
  return (c, p)
| c `(has_zero.zero _) e₂ := prove_pos c e₂
| c e₁ e₂ := do
  n₁ ← e₁.to_rat, n₂ ← e₂.to_rat,
  d ← expr.of_rat c.α (n₂ - n₁),
  (c, e₃) ← c.mk_app ``has_add.add [e₁, d],
  (e₂', p) ← norm_num e₃,
  guard (e₂' =ₐ e₂),
  (c, p') ← prove_pos c d,
  (c, p) ← c.mk_app ``norm_num.lt_add_of_pos_helper [e₁, d, e₂, p, p'],
  return (c, p)

private meta def true_intro (p : expr) : tactic (expr × expr) :=
prod.mk <$> mk_const `true <*> mk_app ``eq_true_intro [p]

private meta def false_intro (p : expr) : tactic (expr × expr) :=
prod.mk <$> mk_const `false <*> mk_app ``eq_false_intro [p]

meta def eval_ineq (simp : expr → tactic (expr × expr)) : expr → tactic (expr × expr)
| `(%%e₁ < %%e₂) := do
  n₁ ← e₁.to_rat, n₂ ← e₂.to_rat,
  c ← infer_type e₁ >>= mk_instance_cache,
  if n₁ < n₂ then
    do (_, p) ← prove_lt simp c e₁ e₂, true_intro p
  else do
    (c, p) ← if n₁ = n₂ then c.mk_app ``lt_irrefl [e₁] else
      (do (c, p') ← prove_lt simp c e₂ e₁,
          c.mk_app ``not_lt_of_gt [e₁, e₂, p']),
    false_intro p
| `(%%e₁ ≤ %%e₂) := do
  n₁ ← e₁.to_rat, n₂ ← e₂.to_rat,
  c ← infer_type e₁ >>= mk_instance_cache,
  if n₁ ≤ n₂ then do
    (c, p) ← if n₁ = n₂ then c.mk_app ``le_refl [e₁] else
      (do (c, p') ← prove_lt simp c e₁ e₂,
          c.mk_app ``le_of_lt [e₁, e₂, p']),
    true_intro p
  else do
    (c, p) ← prove_lt simp c e₂ e₁,
    (c, p) ← c.mk_app ``not_le_of_gt [e₁, e₂, p],
    false_intro p
| `(%%e₁ = %%e₂) := do
  n₁ ← e₁.to_rat, n₂ ← e₂.to_rat,
  c ← infer_type e₁ >>= mk_instance_cache,
  if n₁ < n₂ then do
    (c, p) ← prove_lt simp c e₁ e₂,
    (c, p) ← c.mk_app ``ne_of_lt [e₁, e₂, p],
    false_intro p
  else if n₂ < n₁ then do
    (c, p) ← prove_lt simp c e₂ e₁,
    (c, p) ← c.mk_app ``ne_of_gt [e₁, e₂, p],
    false_intro p
  else mk_eq_refl e₁ >>= true_intro
| `(%%e₁ > %%e₂) := mk_app ``has_lt.lt [e₂, e₁] >>= simp
| `(%%e₁ ≥ %%e₂) := mk_app ``has_le.le [e₂, e₁] >>= simp
| `(%%e₁ ≠ %%e₂) := do e ← mk_app ``eq [e₁, e₂], mk_app ``not [e] >>= simp
| _ := failed

meta def eval_div_ext (simp : expr → tactic (expr × expr)) : expr → tactic (expr × expr)
| `(has_inv.inv %%e) := do
  c ← infer_type e >>= mk_instance_cache,
  (c, p₁) ← c.mk_app ``inv_eq_one_div [e],
  (c, o) ← c.mk_app ``has_one.one [],
  (c, e') ← c.mk_app ``has_div.div [o, e],
  (do (e'', p₂) ← simp e',
    p ← mk_eq_trans p₁ p₂,
    return (e'', p)) <|> return (e', p₁)
| `(%%e₁ / %%e₂) := do
  α ← infer_type e₁,
  c ← mk_instance_cache α,
  match α with
  | `(nat) := do
    n₁ ← e₁.to_nat, n₂ ← e₂.to_nat,
    q ← expr.of_nat α (n₁ / n₂),
    r ← expr.of_nat α (n₁ % n₂),
    (c, e₃) ← c.mk_app ``has_mul.mul [q, e₂],
    (c, e₃) ← c.mk_app ``has_add.add [r, e₃],
    (e₁', p) ← norm_num e₃,
    guard (e₁' =ₐ e₁),
    (c, p') ← prove_lt simp c r e₂,
    p ← mk_app ``norm_num.nat_div_helper [e₁, e₂, q, r, p, p'],
    return (q, p)
  | `(int) := match e₂ with
    | `(- %%e₂') := do
      (c, p₁) ← c.mk_app ``int.div_neg [e₁, e₂'],
      (c, e) ← c.mk_app ``has_div.div [e₁, e₂'],
      (c, e) ← c.mk_app ``has_neg.neg [e],
      (e', p₂) ← simp e,
      p ← mk_eq_trans p₁ p₂,
      return (e', p)
    | _ := do
      n₁ ← e₁.to_int,
      n₂ ← e₂.to_int,
      q ← expr.of_rat α $ rat.of_int (n₁ / n₂),
      r ← expr.of_rat α $ rat.of_int (n₁ % n₂),
      (c, e₃) ← c.mk_app ``has_mul.mul [q, e₂],
      (c, e₃) ← c.mk_app ``has_add.add [r, e₃],
      (e₁', p) ← norm_num e₃,
      guard (e₁' =ₐ e₁),
      (c, r0) ← c.mk_app ``has_zero.zero [],
      (c, r0) ← c.mk_app ``has_le.le [r0, r],
      (_, p₁) ← simp r0,
      p₁ ← mk_app ``of_eq_true [p₁],
      (c, p₂) ← prove_lt simp c r e₂,
      p ← mk_app ``norm_num.int_div_helper [e₁, e₂, q, r, p, p₁, p₂],
      return (q, p)
    end
  | _ := failed
  end
| `(%%e₁ % %%e₂) := do
  α ← infer_type e₁,
  c ← mk_instance_cache α,
  match α with
  | `(nat) := do
    n₁ ← e₁.to_nat, n₂ ← e₂.to_nat,
    q ← expr.of_nat α (n₁ / n₂),
    r ← expr.of_nat α (n₁ % n₂),
    (c, e₃) ← c.mk_app ``has_mul.mul [q, e₂],
    (c, e₃) ← c.mk_app ``has_add.add [r, e₃],
    (e₁', p) ← norm_num e₃,
    guard (e₁' =ₐ e₁),
    (c, p') ← prove_lt simp c r e₂,
    p ← mk_app ``norm_num.nat_mod_helper [e₁, e₂, q, r, p, p'],
    return (r, p)
  | `(int) := match e₂ with
    | `(- %%e₂') := do
      (c, p₁) ← c.mk_app ``int.mod_neg [e₁, e₂'],
      (c, e) ← c.mk_app ``has_mod.mod [e₁, e₂'],
      (e', p₂) ← simp e,
      p ← mk_eq_trans p₁ p₂,
      return (e', p)
    | _ := do
      n₁ ← e₁.to_int,
      n₂ ← e₂.to_int,
      q ← expr.of_rat α $ rat.of_int (n₁ / n₂),
      r ← expr.of_rat α $ rat.of_int (n₁ % n₂),
      (c, e₃) ← c.mk_app ``has_mul.mul [q, e₂],
      (c, e₃) ← c.mk_app ``has_add.add [r, e₃],
      (e₁', p) ← norm_num e₃,
      guard (e₁' =ₐ e₁),
      (c, r0) ← c.mk_app ``has_zero.zero [],
      (c, r0) ← c.mk_app ``has_le.le [r0, r],
      (_, p₁) ← simp r0,
      p₁ ← mk_app ``of_eq_true [p₁],
      (c, p₂) ← prove_lt simp c r e₂,
      p ← mk_app ``norm_num.int_mod_helper [e₁, e₂, q, r, p, p₁, p₂],
      return (r, p)
    end
  | _ := failed
  end
| _ := failed

meta def derive1 (simp : expr → tactic (expr × expr)) (e : expr) :
  tactic (expr × expr) :=
norm_num e <|> eval_div_ext simp e <|> eval_pow simp e <|> eval_ineq simp e

meta def derive : expr → tactic (expr × expr) | e :=
do (_, e', pr) ←
    ext_simplify_core () {} simp_lemmas.mk (λ _, failed) (λ _ _ _ _ _, failed)
      (λ _ _ _ _ e,
        do (new_e, pr) ← derive1 derive e,
           guard (¬ new_e =ₐ e),
           return ((), new_e, some pr, tt))
      `eq e,
    return (e', pr)

end norm_num

namespace tactic.interactive
open norm_num interactive interactive.types

/-- Basic version of `norm_num` that does not call `simp`. -/
meta def norm_num1 (loc : parse location) : tactic unit :=
do ns ← loc.get_locals,
   tt ← tactic.replace_at derive ns loc.include_goal
      | fail "norm_num failed to simplify",
   when loc.include_goal $ try tactic.triv,
   when (¬ ns.empty) $ try tactic.contradiction

/-- Normalize numerical expressions. Supports the operations
  `+` `-` `*` `/` `^` `<` `≤` over ordered fields (or other
  appropriate classes), as well as `-` `/` `%` over `ℤ` and `ℕ`. -/
meta def norm_num (loc : parse location) : tactic unit :=
let t := orelse' (norm_num1 loc) $ simp_core {} failed ff [] [] loc in
t >> repeat t

meta def apply_normed (x : parse texpr) : tactic unit :=
do x₁ ← to_expr x,
  (x₂,_) ← derive x₁,
  tactic.exact x₂

end tactic.interactive
