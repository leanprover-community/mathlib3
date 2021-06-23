/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import data.nat.choose.sum

/-!
# Nilpotent elements

## Main definitions

  * `is_nilpotent`
  * `is_nilpotent_neg_iff`
  * `commute.is_nilpotent_add`
  * `commute.is_nilpotent_mul_left`
  * `commute.is_nilpotent_mul_right`
  * `commute.is_nilpotent_sub`

## Tags

nilpotent, subhas_mul, subhas_add
-/

universes u

variables {R : Type u} {x y : R}

/-- An element is said to be nilpotent if some natural-number-power of it equals zero.

Note that we require only the bare minimum assumptions for the definition to make sense. Even
`monoid_with_zero` is too strong since nilpotency is important in the study of rings that are only
power-associative. -/
def is_nilpotent [has_zero R] [has_pow R ℕ] (x : R) : Prop := ∃ (n : ℕ), x^n = 0

lemma monoid_with_zero.pow_zero_of_le [monoid_with_zero R] {n m : ℕ} (hn : n ≤ m) (hx : x^n = 0) :
  x^m = 0 :=
by rw [← nat.sub_add_cancel hn, pow_add, hx, mul_zero]

lemma is_nilpotent.zero [monoid_with_zero R] : is_nilpotent (0 : R) := ⟨1, pow_one 0⟩

lemma is_nilpotent.neg [ring R] (h : is_nilpotent x) : is_nilpotent (-x) :=
begin
  obtain ⟨n, hn⟩ := h,
  use n,
  rw [neg_pow, hn, mul_zero],
end

lemma is_nilpotent_neg_iff [ring R] : is_nilpotent (-x) ↔ is_nilpotent x :=
⟨λ h, neg_neg x ▸ h.neg, λ h, h.neg⟩

namespace commute

section semiring

variables [semiring R] (h_comm : commute x y)

include h_comm

lemma is_nilpotent_add (hx : is_nilpotent x) (hy : is_nilpotent y) : is_nilpotent (x + y) :=
begin
  obtain ⟨n, hn⟩ := hx,
  obtain ⟨m, hm⟩ := hy,
  use n + m - 1,
  rw h_comm.add_pow',
  apply finset.sum_eq_zero,
  rintros ⟨i, j⟩ hij,
  suffices : x^i * y^j = 0, { simp only [this, nsmul_eq_mul, mul_zero], },
  cases nat.le_or_le_of_add_eq_add_pred (finset.nat.mem_antidiagonal.mp hij) with hi hj,
  { rw [monoid_with_zero.pow_zero_of_le hi hn, zero_mul], },
  { rw [monoid_with_zero.pow_zero_of_le hj hm, mul_zero], },
end

lemma is_nilpotent_mul_left (h : is_nilpotent x) : is_nilpotent (x * y) :=
begin
  obtain ⟨n, hn⟩ := h,
  use n,
  rw [h_comm.mul_pow, hn, zero_mul],
end

lemma is_nilpotent_mul_right (h : is_nilpotent y) : is_nilpotent (x * y) :=
by { rw h_comm.eq, exact h_comm.symm.is_nilpotent_mul_left h, }

end semiring

section ring

variables [ring R] (h_comm : commute x y)

include h_comm

lemma is_nilpotent_sub (hx : is_nilpotent x) (hy : is_nilpotent y) : is_nilpotent (x - y) :=
begin
  rw ← neg_right_iff at h_comm,
  rw ← is_nilpotent_neg_iff at hy,
  rw sub_eq_add_neg,
  exact h_comm.is_nilpotent_add hx hy,
end

end ring

end commute
