/-
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin, Mario Carneiro

Euclidean domains and Euclidean algorithm (extended to come)
A lot is based on pre-existing code in mathlib for natural number gcds
-/
import data.int.basic

universe u

class euclidean_domain (α : Type u) extends integral_domain α :=
(quotient : α → α → α)
(remainder : α → α → α)
 -- This could be changed to the same order as int.mod_add_div.
 -- We normally write qb+r rather than r + qb though.
(quotient_mul_add_remainder_eq : ∀ a b, b * quotient a b + remainder a b = a)
(r : α → α → Prop)
(r_well_founded : well_founded r)
(remainder_lt : ∀ a {b}, b ≠ 0 → r (remainder a b) b)
/- `val_le_mul_left` is often not a required in definitions of a euclidean
  domain since given the other properties we can show there is a
  (noncomputable) euclidean domain α with the property `val_le_mul_left`.
  So potentially this definition could be split into two different ones
  (euclidean_domain_weak and euclidean_domain_strong) with a noncomputable
  function from weak to strong. I've currently divided the lemmas into
  strong and weak depending on whether they require `val_le_mul_left` or not. -/
(mul_left_not_lt : ∀ a {b}, b ≠ 0 → ¬r (a * b) a)

namespace euclidean_domain
variable {α : Type u}
variables [euclidean_domain α]

local infix ` ≺ `:50 := euclidean_domain.r

instance : has_div α := ⟨quotient⟩

instance : has_mod α := ⟨remainder⟩

theorem div_add_mod (a b : α) : b * (a / b) + a % b = a :=
quotient_mul_add_remainder_eq _ _

lemma mod_eq_sub_mul_div {α : Type*} [euclidean_domain α] (a b : α) :
  a % b = a - b * (a / b) :=
calc a % b = b * (a / b) + a % b - b * (a / b) : (add_sub_cancel' _ _).symm
... = a - b * (a / b) : by rw div_add_mod

theorem mod_lt : ∀ a {b : α}, b ≠ 0 → (a % b) ≺ b :=
remainder_lt

theorem mul_right_not_lt {a : α} (b) (h : a ≠ 0) : ¬(a * b) ≺ b :=
by rw mul_comm; exact mul_left_not_lt b h

lemma mul_div_cancel_left {a : α} (b) (a0 : a ≠ 0) : a * b / a = b :=
eq.symm $ eq_of_sub_eq_zero $ classical.by_contradiction $ λ h,
begin
  have := mul_left_not_lt a h,
  rw [mul_sub, sub_eq_iff_eq_add'.2 (div_add_mod (a*b) a).symm] at this,
  exact this (mod_lt _ a0)
end

lemma mul_div_cancel (a) {b : α} (b0 : b ≠ 0) : a * b / b = a :=
by rw mul_comm; exact mul_div_cancel_left a b0

@[simp] lemma mod_zero (a : α) : a % 0 = a :=
by simpa only [zero_mul, zero_add] using div_add_mod a 0

@[simp] lemma mod_eq_zero {a b : α} : a % b = 0 ↔ b ∣ a :=
⟨λ h, by rw [← div_add_mod a b, h, add_zero]; exact dvd_mul_right _ _,
 λ ⟨c, e⟩, begin
  rw [e, ← add_left_cancel_iff, div_add_mod, add_zero],
  haveI := classical.dec,
  by_cases b0 : b = 0,
  { simp only [b0, zero_mul] },
  { rw [mul_div_cancel_left _ b0] }
 end⟩

@[simp] lemma mod_self (a : α) : a % a = 0 :=
mod_eq_zero.2 (dvd_refl _)

lemma dvd_mod_iff {a b c : α} (h : c ∣ b) : c ∣ a % b ↔ c ∣ a :=
by rw [dvd_add_iff_right (dvd_mul_of_dvd_left h _), div_add_mod]

lemma lt_one (a : α) : a ≺ (1:α) → a = 0 :=
by haveI := classical.dec; exact
not_imp_not.1 (λ h, by simpa only [one_mul] using mul_left_not_lt 1 h)

lemma val_dvd_le : ∀ a b : α, b ∣ a → a ≠ 0 → ¬a ≺ b
| _ b ⟨d, rfl⟩ ha := mul_left_not_lt b (mt (by rintro rfl; exact mul_zero _) ha)

@[simp] lemma mod_one (a : α) : a % 1 = 0 :=
mod_eq_zero.2 (one_dvd _)

@[simp] lemma zero_mod (b : α) : 0 % b = 0 :=
mod_eq_zero.2 (dvd_zero _)

@[simp] lemma zero_div {a : α} (a0 : a ≠ 0) : 0 / a = 0 :=
by simpa only [zero_mul] using mul_div_cancel 0 a0

@[simp] lemma div_self {a : α} (a0 : a ≠ 0) : a / a = 1 :=
by simpa only [one_mul] using mul_div_cancel 1 a0

section gcd
variable [decidable_eq α]

def gcd : α → α → α
| a := λ b, if a0 : a = 0 then b else
  have h:_ := mod_lt b a0,
  gcd (b%a) a
using_well_founded {dec_tac := tactic.assumption,
  rel_tac := λ _ _, `[exact ⟨_, r_well_founded α⟩]}

@[simp] theorem gcd_zero_left (a : α) : gcd 0 a = a :=
by rw gcd; exact if_pos rfl

@[simp] theorem gcd_zero_right (a : α) : gcd a 0 = a :=
by rw gcd; split_ifs; simp only [h, zero_mod, gcd_zero_left]

theorem gcd_val (a b : α) : gcd a b = gcd (b % a) a :=
by rw gcd; split_ifs; [simp only [h, mod_zero, gcd_zero_right], refl]

@[elab_as_eliminator]
theorem gcd.induction {P : α → α → Prop} : ∀ a b : α,
  (∀ x, P 0 x) →
  (∀ a b, a ≠ 0 → P (b % a) a → P a b) →
  P a b
| a := λ b H0 H1, if a0 : a = 0 then by rw [a0]; apply H0 else
  have h:_ := mod_lt b a0,
  H1 _ _ a0 (gcd.induction (b%a) a H0 H1)
using_well_founded {dec_tac := tactic.assumption,
  rel_tac := λ _ _, `[exact ⟨_, r_well_founded α⟩]}

theorem gcd_dvd (a b : α) : gcd a b ∣ a ∧ gcd a b ∣ b :=
gcd.induction a b
  (λ b, by rw [gcd_zero_left]; exact ⟨dvd_zero _, dvd_refl _⟩)
  (λ a b aneq ⟨IH₁, IH₂⟩, by rw gcd_val;
    exact ⟨IH₂, (dvd_mod_iff IH₂).1 IH₁⟩)

theorem gcd_dvd_left (a b : α) : gcd a b ∣ a := (gcd_dvd a b).left

theorem gcd_dvd_right (a b : α) : gcd a b ∣ b := (gcd_dvd a b).right

theorem dvd_gcd {a b c : α} : c ∣ a → c ∣ b → c ∣ gcd a b :=
gcd.induction a b
  (λ _ _ H, by simpa only [gcd_zero_left] using H)
  (λ a b a0 IH ca cb, by rw gcd_val;
    exact IH ((dvd_mod_iff ca).2 cb) ca)

theorem gcd_eq_left {a b : α} : gcd a b = a ↔ a ∣ b :=
⟨λ h, by rw ← h; apply gcd_dvd_right,
 λ h, by rw [gcd_val, mod_eq_zero.2 h, gcd_zero_left]⟩

@[simp] theorem gcd_one_left (a : α) : gcd 1 a = 1 :=
gcd_eq_left.2 (one_dvd _)

@[simp] theorem gcd_self (a : α) : gcd a a = a :=
gcd_eq_left.2 (dvd_refl _)

def xgcd_aux : α → α → α → α → α → α → α × α × α
| r := λ s t r' s' t',
if hr : r = 0 then (r', s', t')
  else
  have r' % r ≺ r, from mod_lt _ hr,
  let q := r' / r in xgcd_aux (r' % r) (s' - q * s) (t' - q * t) r s t
using_well_founded {dec_tac := tactic.assumption,
  rel_tac := λ _ _, `[exact ⟨_, r_well_founded α⟩]}

@[simp] theorem xgcd_zero_left {s t r' s' t' : α} : xgcd_aux 0 s t r' s' t' = (r', s', t') :=
by unfold xgcd_aux; exact if_pos rfl

@[simp] theorem xgcd_aux_rec {r s t r' s' t' : α} (h : r ≠ 0) :
  xgcd_aux r s t r' s' t' = xgcd_aux (r' % r) (s' - (r' / r) * s) (t' - (r' / r) * t) r s t :=
by conv {to_lhs, rw [xgcd_aux]}; exact if_neg h

/-- Use the extended GCD algorithm to generate the `a` and `b` values
  satisfying `gcd x y = x * a + y * b`. -/
def xgcd (x y : α) : α × α := (xgcd_aux x 1 0 y 0 1).2

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
def gcd_a (x y : α) : α := (xgcd x y).1

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
def gcd_b (x y : α) : α := (xgcd x y).2

@[simp] theorem xgcd_aux_fst (x y : α) : ∀ s t s' t',
  (xgcd_aux x s t y s' t').1 = gcd x y :=
gcd.induction x y (by intros; rw [xgcd_zero_left, gcd_zero_left])
(λ x y h IH s t s' t', by simp only [xgcd_aux_rec h, if_neg h, IH]; rw ← gcd_val)

theorem xgcd_aux_val (x y : α) : xgcd_aux x 1 0 y 0 1 = (gcd x y, xgcd x y) :=
by rw [xgcd, ← xgcd_aux_fst x y 1 0 0 1, prod.mk.eta]

theorem xgcd_val (x y : α) : xgcd x y = (gcd_a x y, gcd_b x y) :=
prod.mk.eta.symm

private def P (a b : α) : α × α × α → Prop | (r, s, t) := (r : α) = a * s + b * t

theorem xgcd_aux_P (a b : α) {r r' : α} : ∀ {s t s' t'}, P a b (r, s, t) →
  P a b (r', s', t') → P a b (xgcd_aux r s t r' s' t') :=
gcd.induction r r' (by intros; simpa only [xgcd_zero_left]) $ λ x y h IH s t s' t' p p', begin
  rw [xgcd_aux_rec h], refine IH _ p, unfold P at p p' ⊢,
  rw [mul_sub, mul_sub, add_sub, sub_add_eq_add_sub, ← p', sub_sub,
    mul_comm _ s, ← mul_assoc, mul_comm _ t, ← mul_assoc, ← add_mul, ← p,
    mod_eq_sub_mul_div]
end

theorem gcd_eq_gcd_ab (a b : α) : (gcd a b : α) = a * gcd_a a b + b * gcd_b a b :=
by have := @xgcd_aux_P _ _ _ a b a b 1 0 0 1
  (by rw [P, mul_one, mul_zero, add_zero]) (by rw [P, mul_one, mul_zero, zero_add]);
rwa [xgcd_aux_val, xgcd_val] at this

end gcd

instance : euclidean_domain ℤ :=
{ quotient := (/),
  remainder := (%),
  quotient_mul_add_remainder_eq := λ a b, by rw add_comm; exact int.mod_add_div _ _,
  r := λ a b, a.nat_abs < b.nat_abs,
  r_well_founded := measure_wf (λ a, int.nat_abs a),
  remainder_lt := λ a b b0, int.coe_nat_lt.1 $
    by rw [int.nat_abs_of_nonneg (int.mod_nonneg _ b0), ← int.abs_eq_nat_abs];
    exact int.mod_lt _ b0,
  mul_left_not_lt := λ a b b0, not_lt_of_ge $
    by rw [← mul_one a.nat_abs, int.nat_abs_mul];
    exact mul_le_mul_of_nonneg_left (int.nat_abs_pos_of_ne_zero b0) (nat.zero_le _) }

end euclidean_domain