/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/

import data.nat.units
import data.int.basic
import algebra.ring.units

/-!
# Lemmas about units in `ℤ`.
-/

namespace int

/-! ### units -/

@[simp] theorem units_nat_abs (u : ℤˣ) : nat_abs u = 1 :=
units.ext_iff.1 $ nat.units_eq_one ⟨nat_abs u, nat_abs ↑u⁻¹,
  by rw [← nat_abs_mul, units.mul_inv]; refl,
  by rw [← nat_abs_mul, units.inv_mul]; refl⟩

theorem units_eq_one_or (u : ℤˣ) : u = 1 ∨ u = -1 :=
by simpa only [units.ext_iff, units_nat_abs] using nat_abs_eq u

lemma is_unit_eq_one_or {a : ℤ} : is_unit a → a = 1 ∨ a = -1
| ⟨x, hx⟩ := hx ▸ (units_eq_one_or _).imp (congr_arg coe) (congr_arg coe)

lemma is_unit_iff {a : ℤ} : is_unit a ↔ a = 1 ∨ a = -1 :=
begin
  refine ⟨λ h, is_unit_eq_one_or h, λ h, _⟩,
  rcases h with rfl | rfl,
  { exact is_unit_one },
  { exact is_unit_one.neg }
end

lemma is_unit_eq_or_eq_neg {a b : ℤ} (ha : is_unit a) (hb : is_unit b) : a = b ∨ a = -b :=
begin
  rcases is_unit_eq_one_or hb with rfl | rfl,
  { exact is_unit_eq_one_or ha },
  { rwa [or_comm, neg_neg, ←is_unit_iff] },
end

lemma eq_one_or_neg_one_of_mul_eq_one {z w : ℤ} (h : z * w = 1) : z = 1 ∨ z = -1 :=
is_unit_iff.mp (is_unit_of_mul_eq_one z w h)

lemma eq_one_or_neg_one_of_mul_eq_one' {z w : ℤ} (h : z * w = 1) :
  (z = 1 ∧ w = 1) ∨ (z = -1 ∧ w = -1) :=
begin
  have h' : w * z = 1 := (mul_comm z w) ▸ h,
  rcases eq_one_or_neg_one_of_mul_eq_one h with rfl | rfl;
  rcases eq_one_or_neg_one_of_mul_eq_one h' with rfl | rfl;
  tauto,
end

theorem is_unit_iff_nat_abs_eq {n : ℤ} : is_unit n ↔ n.nat_abs = 1 :=
by simp [nat_abs_eq_iff, is_unit_iff, nat.cast_zero]

alias is_unit_iff_nat_abs_eq ↔ is_unit.nat_abs_eq _

@[norm_cast]
lemma of_nat_is_unit {n : ℕ} : is_unit (n : ℤ) ↔ is_unit n :=
by rw [nat.is_unit_iff, is_unit_iff_nat_abs_eq, nat_abs_of_nat]

lemma is_unit_mul_self {a : ℤ} (ha : is_unit a) : a * a = 1 :=
(is_unit_eq_one_or ha).elim (λ h, h.symm ▸ rfl) (λ h, h.symm ▸ rfl)

lemma is_unit_add_is_unit_eq_is_unit_add_is_unit {a b c d : ℤ}
  (ha : is_unit a) (hb : is_unit b) (hc : is_unit c) (hd : is_unit d) :
  a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c :=
begin
  rw is_unit_iff at ha hb hc hd,
  cases ha; cases hb; cases hc; cases hd;
  subst ha; subst hb; subst hc; subst hd;
  tidy,
end

end int
