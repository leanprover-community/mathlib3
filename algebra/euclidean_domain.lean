/-
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin, Mario Carneiro

Euclidean domains and Euclidean algorithm (extended to come)
A lot is based on pre-existing code in mathlib for natural number gcds
-/
import algebra.group algebra.order

universe u

class euclidean_domain (α : Type u) extends integral_domain α :=
(quotient : α → α → α)
(remainder : α → α → α)
 -- This could be changed to the same order as int.mod_add_div.
 -- We normally write qb+r rather than r + qb though.
(quotient_mul_add_remainder_eq : ∀ a b, b * quotient a b + remainder a b = a)
(valuation : α → ℕ)
(val_remainder_lt : ∀ a {b}, b ≠ 0 → valuation (remainder a b) < valuation b)
/- `val_le_mul_left` is often not a required in definitions of a euclidean
  domain since given the other properties we can show there is a
  (noncomputable) euclidean domain α with the property `val_le_mul_left`.
  So potentially this definition could be split into two different ones
  (euclidean_domain_weak and euclidean_domain_strong) with a noncomputable
  function from weak to strong. I've currently divided the lemmas into
  strong and weak depending on whether they require `val_le_mul_left` or not. -/
(val_le_mul_left : ∀ a {b}, b ≠ 0 → valuation a ≤ valuation (a * b))

namespace euclidean_domain
variable {α : Type u}
variables [euclidean_domain α]

instance : has_div α := ⟨quotient⟩

instance : has_mod α := ⟨remainder⟩

theorem div_add_mod (a b : α) : b * (a / b) + a % b = a :=
quotient_mul_add_remainder_eq _ _

theorem val_mod_lt : ∀ a {b : α}, b ≠ 0 → valuation (a % b) < valuation b :=
val_remainder_lt

theorem val_le_mul_right {a : α} (b) (h : a ≠ 0) : valuation b ≤ valuation (a * b) :=
by rw mul_comm; exact val_le_mul_left b h

lemma mul_div_cancel_left {a : α} (b) (a0 : a ≠ 0) : a * b / a = b :=
eq.symm $ eq_of_sub_eq_zero $ classical.by_contradiction $ λ h,
begin
  have := val_le_mul_left a h,
  rw [mul_sub, sub_eq_iff_eq_add'.2 (div_add_mod (a*b) a).symm] at this,
  exact not_lt_of_le this (val_mod_lt _ a0)
end

lemma mul_div_cancel (a) {b : α} (b0 : b ≠ 0) : a * b / b = a :=
by rw mul_comm; exact mul_div_cancel_left a b0

@[simp] lemma mod_zero (a : α) : a % 0 = a :=
by simpa using div_add_mod a 0

@[simp] lemma mod_eq_zero {a b : α} : a % b = 0 ↔ b ∣ a :=
⟨λ h, by rw [← div_add_mod a b]; simp [h],
 λ ⟨c, e⟩, begin
  rw [e, ← add_left_cancel_iff, div_add_mod, add_zero],
  haveI := classical.dec,
  by_cases b0 : b = 0; simp [b0, mul_div_cancel_left],
 end⟩

@[simp] lemma mod_self (a : α) : a % a = 0 :=
mod_eq_zero.2 (dvd_refl _)

lemma dvd_mod_iff {a b c : α} (h : c ∣ b) : c ∣ a % b ↔ c ∣ a :=
by rw [dvd_add_iff_right (dvd_mul_of_dvd_left h _), div_add_mod]

lemma val_lt_one (a : α) : valuation a < valuation (1:α) → a = 0 :=
by haveI := classical.dec; exact
not_imp_not.1 (λ h, by simpa using val_le_mul_left 1 h)

lemma val_dvd_le : ∀ a b : α, b ∣ a → a ≠ 0 → valuation b ≤ valuation a
| _ b ⟨d, rfl⟩ ha := val_le_mul_left b $
  mt (by intro h; simp [h]) ha

@[simp] lemma mod_one (a : α) : a % 1 = 0 :=
mod_eq_zero.2 (one_dvd _)

@[simp] lemma zero_mod (b : α) : 0 % b = 0 :=
mod_eq_zero.2 (dvd_zero _)

@[simp] lemma zero_div {a : α} (a0 : a ≠ 0) : 0 / a = 0 :=
by simpa using mul_div_cancel 0 a0

@[simp] lemma div_self {a : α} (a0 : a ≠ 0) : a / a = 1 :=
by simpa using mul_div_cancel 1 a0

section gcd
variable [decidable_eq α]

def gcd : α → α → α
| a := λ b, if a0 : a = 0 then b else
  have h:_ := val_mod_lt b a0,
  gcd (b%a) a
using_well_founded {rel_tac :=
  λ _ _, `[exact ⟨_, measure_wf valuation⟩]}

@[simp] theorem gcd_zero_left (a : α) : gcd 0 a = a :=
by rw gcd; simp

@[simp] theorem gcd_zero_right (a : α) : gcd a 0 = a :=
by rw gcd; by_cases a0 : a = 0; simp [a0]

theorem gcd_val (a b : α) : gcd a b = gcd (b % a) a :=
by rw gcd; by_cases a0 : a = 0; simp [a0]

@[elab_as_eliminator]
theorem gcd.induction {P : α → α → Prop} : ∀ a b : α,
  (∀ x, P 0 x) →
  (∀ a b, a ≠ 0 → P (b % a) a → P a b) →
  P a b
| a := λ b H0 H1, if a0 : a = 0 then by simp [a0, H0] else
  have h:_ := val_mod_lt b a0,
  H1 _ _ a0 (gcd.induction (b%a) a H0 H1)
using_well_founded {rel_tac :=
  λ _ _, `[exact ⟨_, measure_wf valuation⟩]}

theorem gcd_dvd (a b : α) : gcd a b ∣ a ∧ gcd a b ∣ b :=
gcd.induction a b
  (λ b, by simp)
  (λ a b aneq ⟨IH₁, IH₂⟩,
    by rw gcd_val; exact
    ⟨IH₂, (dvd_mod_iff IH₂).1 IH₁⟩)

theorem gcd_dvd_left (a b : α) : gcd a b ∣ a := (gcd_dvd a b).left

theorem gcd_dvd_right (a b : α) : gcd a b ∣ b := (gcd_dvd a b).right

theorem dvd_gcd {a b c : α} : c ∣ a → c ∣ b → c ∣ gcd a b :=
gcd.induction a b
  (by simp {contextual := tt})
  (λ a b a0 IH ca cb,
    by rw gcd_val; exact
    IH ((dvd_mod_iff ca).2 cb) ca)

theorem gcd_eq_left {a b : α} : gcd a b = a ↔ a ∣ b :=
⟨λ h, by rw ← h; apply gcd_dvd_right,
 λ h, by rw [gcd_val, mod_eq_zero.2 h, gcd_zero_left]⟩

@[simp] theorem gcd_one_left (a : α) : gcd 1 a = 1 :=
gcd_eq_left.2 (one_dvd _)

@[simp] theorem gcd_self (a : α) : gcd a a = a :=
gcd_eq_left.2 (dvd_refl _)

end gcd

end euclidean_domain