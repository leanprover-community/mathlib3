/-
Copyright (c) 2017 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Mario Carneiro

Evaluating arithmetic expressions including *, +, -, ^, ≤
-/

import algebra.group_power data.rat data.nat.prime
import tactic.interactive tactic.converter.interactive

universes u v w

namespace expr

protected meta def to_pos_rat : expr → option ℚ
| `(%%e₁ / %%e₂) := do m ← e₁.to_nat, n ← e₂.to_nat, some (rat.mk m n)
| e              := do n ← e.to_nat, return (rat.of_int n)

protected meta def to_rat : expr → option ℚ
| `(has_neg.neg %%e) := do q ← e.to_pos_rat, some (-q)
| e                  := e.to_pos_rat

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

meta def refl_conv (e : expr) : tactic (expr × expr) :=
do p ← mk_eq_refl e, return (e, p)

meta def trans_conv (t₁ t₂ : expr → tactic (expr × expr)) (e : expr) :
  tactic (expr × expr) :=
(do (e₁, p₁) ← t₁ e,
  (do (e₂, p₂) ← t₂ e₁,
    p ← mk_eq_trans p₁ p₂, return (e₂, p)) <|>
  return (e₁, p₁)) <|> t₂ e

end tactic

open tactic

namespace norm_num
variable {α : Type u}

lemma subst_into_neg {α} [has_neg α] (a ta t : α) (pra : a = ta) (prt : -ta = t) : -a = t :=
by simp [pra, prt]

theorem bit0_zero [add_group α] : bit0 (0 : α) = 0 := add_zero _

theorem bit1_zero [add_group α] [has_one α] : bit1 (0 : α) = 1 :=
by rw [bit1, bit0_zero, zero_add]

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

meta def eval_pow (simp : expr → tactic (expr × expr)) : expr → tactic (expr × expr)
| `(@has_pow.pow %%α _ %%m %%e₁ %%e₂) :=
  match m with
  | `(nat.has_pow) :=
    mk_app ``nat.pow [e₁, e₂] >>= eval_pow
  | `(@monoid.has_pow %%α %%m) :=
    mk_app ``monoid.pow [e₁, e₂] >>= eval_pow
  | _ := failed
  end
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
      let p₁ := (expr.const ``int.mod_neg []).mk_app [e₁, e₂'],
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
| `(%%e₁ ∣ %%e₂) := do
  α ← infer_type e₁,
  c ← mk_instance_cache α,
  n ← match α with
  | `(nat) := return ``nat.dvd_iff_mod_eq_zero
  | `(int) := return ``int.dvd_iff_mod_eq_zero
  | _ := failed
  end,
  p₁ ← mk_app ``propext [@expr.const tt n [] e₁ e₂],
  (e', p₂) ← simp `(%%e₂ % %%e₁ = 0),
  p' ← mk_eq_trans p₁ p₂,
  return (e', p')
| _ := failed

lemma not_prime_helper (a b n : ℕ)
  (h : a * b = n) (h₁ : 1 < a) (h₂ : 1 < b) : ¬ nat.prime n :=
by rw ← h; exact nat.not_prime_mul h₁ h₂

lemma is_prime_helper (n : ℕ)
  (h₁ : 1 < n) (h₂ : nat.min_fac n = n) : nat.prime n :=
nat.prime_def_min_fac.2 ⟨h₁, h₂⟩

lemma min_fac_bit0 (n : ℕ) : nat.min_fac (bit0 n) = 2 :=
by simp [nat.min_fac_eq, show 2 ∣ bit0 n, by simp [bit0_eq_two_mul n]]

def min_fac_helper (n k : ℕ) : Prop :=
0 < k ∧ bit1 k ≤ nat.min_fac (bit1 n)

theorem min_fac_helper.n_pos {n k : ℕ} (h : min_fac_helper n k) : 0 < n :=
nat.pos_iff_ne_zero.2 $ λ e,
by rw e at h; exact not_le_of_lt (nat.bit1_lt h.1) h.2

lemma min_fac_ne_bit0 {n k : ℕ} : nat.min_fac (bit1 n) ≠ bit0 k :=
by rw bit0_eq_two_mul; exact λ e, absurd
  ((nat.dvd_add_iff_right (by simp [bit0_eq_two_mul n])).2
    (dvd_trans ⟨_, e⟩ (nat.min_fac_dvd _)))
  dec_trivial

lemma min_fac_helper_0 (n : ℕ) (h : 0 < n) : min_fac_helper n 1 :=
begin
  refine ⟨zero_lt_one, lt_of_le_of_ne _ min_fac_ne_bit0.symm⟩,
  refine @lt_of_le_of_ne ℕ _ _ _ (nat.min_fac_pos _) _,
  intro e,
  have := nat.min_fac_prime _,
  { rw ← e at this, exact nat.not_prime_one this },
  { exact ne_of_gt (nat.bit1_lt h) }
end

lemma min_fac_helper_1 {n k k' : ℕ} (e : k + 1 = k')
  (np : nat.min_fac (bit1 n) ≠ bit1 k)
  (h : min_fac_helper n k) : min_fac_helper n k' :=
begin
  rw ← e,
  refine ⟨nat.succ_pos _,
    (lt_of_le_of_ne (lt_of_le_of_ne _ _ : k+1+k < _)
      min_fac_ne_bit0.symm : bit0 (k+1) < _)⟩,
  { rw add_right_comm, exact h.2 },
  { rw add_right_comm, exact np.symm }
end

lemma min_fac_helper_2 (n k k' : ℕ) (e : k + 1 = k')
  (np : ¬ nat.prime (bit1 k)) (h : min_fac_helper n k) : min_fac_helper n k' :=
begin
  refine min_fac_helper_1 e _ h,
  intro e₁, rw ← e₁ at np,
  exact np (nat.min_fac_prime $ ne_of_gt $ nat.bit1_lt h.n_pos)
end

lemma min_fac_helper_3 (n k k' : ℕ) (e : k + 1 = k')
  (nd : bit1 k ∣ bit1 n = false)
  (h : min_fac_helper n k) : min_fac_helper n k' :=
begin
  refine min_fac_helper_1 e _ h,
  intro e₁, rw [eq_false, ← e₁] at nd,
  exact nd (nat.min_fac_dvd _)
end

lemma min_fac_helper_4 (n k : ℕ) (hd : bit1 k ∣ bit1 n = true)
  (h : min_fac_helper n k) : nat.min_fac (bit1 n) = bit1 k :=
by rw eq_true at hd; exact
le_antisymm (nat.min_fac_le_of_dvd (nat.bit1_lt h.1) hd) h.2

lemma min_fac_helper_5 (n k k' : ℕ) (e : bit1 k * bit1 k = k')
  (hd : bit1 n < k') (h : min_fac_helper n k) : nat.min_fac (bit1 n) = bit1 n :=
begin
  refine (nat.prime_def_min_fac.1 (nat.prime_def_le_sqrt.2
    ⟨nat.bit1_lt h.n_pos, _⟩)).2,
  rw ← e at hd,
  intros m m2 hm md,
  have := le_trans h.2 (le_trans (nat.min_fac_le_of_dvd m2 md) hm),
  rw nat.le_sqrt at this,
  exact not_le_of_lt hd this
end

meta def prove_non_prime (simp : expr → tactic (expr × expr)) (e : expr) (n d₁ : ℕ) : tactic expr :=
do let e₁ := reflect d₁,
  c ← mk_instance_cache `(nat),
  (c, p₁) ← prove_lt simp c `(1) e₁,
  let d₂ := n / d₁, let e₂ := reflect d₂,
  (e', p) ← mk_app ``has_mul.mul [e₁, e₂] >>= norm_num,
  guard (e' =ₐ e),
  (c, p₂) ← prove_lt simp c `(1) e₂,
  return $ (expr.const ``not_prime_helper []).mk_app [e₁, e₂, e, p, p₁, p₂]

meta def prove_min_fac (simp : expr → tactic (expr × expr))
  (e₁ : expr) (n1 : ℕ) : expr → expr → tactic (expr × expr)
| e₂ p := do
  k ← e₂.to_nat,
  let k1 := bit1 k,
  e₁1 ← mk_app ``bit1 [e₁],
  e₂1 ← mk_app ``bit1 [e₂],
  if n1 < k1*k1 then do
    c ← mk_instance_cache `(nat),
    (c, e') ← c.mk_app ``has_mul.mul [e₂1, e₂1],
    (e', p₁) ← norm_num e',
    (c, p₂) ← prove_lt simp c e₁1 e',
    p' ← mk_app ``min_fac_helper_5 [e₁, e₂, e', p₁, p₂, p],
    return (e₁1, p')
  else let d := k1.min_fac in
  if to_bool (d < k1) then do
    (e', p₁) ← norm_num `(%%e₂ + 1),
    p₂ ← prove_non_prime simp e₂1 k1 d,
    mk_app ``min_fac_helper_2 [e₁, e₂, e', p₁, p₂, p] >>= prove_min_fac e'
  else do
    (_, p₂) ← simp `((%%e₂1 : ℕ) ∣ %%e₁1),
    if k1 ∣ n1 then do
      p' ← mk_app ``min_fac_helper_4 [e₁, e₂, p₂, p],
      return (e₂1, p')
    else do
      (e', p₁) ← norm_num `(%%e₂ + 1),
      mk_app ``min_fac_helper_3 [e₁, e₂, e', p₁, p₂, p] >>= prove_min_fac e'

meta def eval_prime (simp : expr → tactic (expr × expr)) : expr → tactic (expr × expr)
| `(nat.prime %%e) := do
  n ← e.to_nat,
  match n with
  | 0 := false_intro `(nat.not_prime_zero)
  | 1 := false_intro `(nat.not_prime_one)
  | _ := let d₁ := n.min_fac in
    if d₁ < n then prove_non_prime simp e n d₁ >>= false_intro
    else do
      let e₁ := reflect d₁,
      c ← mk_instance_cache `(nat),
      (c, p₁) ← prove_lt simp c `(1) e₁,
      (e₁, p) ← simp `(nat.min_fac %%e),
      true_intro $ (expr.const ``is_prime_helper []).mk_app [e, p₁, p]
  end
| `(nat.min_fac 0) := refl_conv (reflect (0:ℕ))
| `(nat.min_fac 1) := refl_conv (reflect (1:ℕ))
| `(nat.min_fac (bit0 %%e)) := prod.mk `(2) <$> mk_app ``min_fac_bit0 [e]
| `(nat.min_fac (bit1 %%e)) := do
  n ← e.to_nat,
  c ← mk_instance_cache `(nat),
  (c, p) ← prove_pos c e,
  mk_app ``min_fac_helper_0 [e, p] >>= prove_min_fac simp e (bit1 n) `(1)
| _ := failed

meta def derive1 (simp : expr → tactic (expr × expr)) (e : expr) :
  tactic (expr × expr) :=
norm_num e <|> eval_div_ext simp e <|>
eval_pow simp e <|> eval_ineq simp e <|> eval_prime simp e

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
meta def norm_num (hs : parse simp_arg_list) (l : parse location) : tactic unit :=
repeat1 $ orelse' (norm_num1 l) $
simp_core {} (norm_num1 (loc.ns [none])) ff hs [] l

meta def apply_normed (x : parse texpr) : tactic unit :=
do x₁ ← to_expr x,
  (x₂,_) ← derive x₁,
  tactic.exact x₂

end tactic.interactive

namespace conv.interactive
open conv interactive tactic.interactive
open norm_num (derive)

meta def norm_num1 : conv unit := replace_lhs derive

meta def norm_num (hs : parse simp_arg_list) : conv unit :=
repeat1 $ orelse' norm_num1 $
simp_core {} norm_num1 ff hs [] (loc.ns [none])

end conv.interactive
