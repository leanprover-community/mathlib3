/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Ken Lee, Chris Hughes
-/

import algebra.big_operators
import data.fintype.basic
import data.set.disjointed

/-!
# Coprime elements of a ring

## Main definitions

* `is_coprime x y`: that `x` and `y` are coprime, defined to be the existence of `a` and `b` such
that `a * x + b * y = 1`.

-/

open_locale classical big_operators

universes u v

variables {R : Type u} [comm_semiring R] (x y z : R)

/-- The proposition that `x` and `y` are coprime, defined to be the existence of `a` and `b` such
that `a * x + b * y = 1`. -/
@[simp] def is_coprime : Prop :=
∃ a b, a * x + b * y = 1

variables {x y z}

theorem is_coprime_self :
  is_coprime x x ↔ is_unit x :=
⟨λ ⟨a, b, h⟩, is_unit_of_mul_eq_one x (a + b) $ by rwa [mul_comm, add_mul],
λ h, let ⟨b, hb⟩ := is_unit_iff_exists_inv'.1 h in ⟨b, 0, by rwa [zero_mul, add_zero]⟩⟩

theorem is_coprime.mul_dvd (H : is_coprime x y) (H1 : x ∣ z) (H2 : y ∣ z) : x * y ∣ z :=
begin
  obtain ⟨a, b, h⟩ := H,
  rw [← mul_one z, ← h, mul_add],
  apply dvd_add,
  { rw [mul_comm z, mul_assoc],
    exact dvd_mul_of_dvd_right (mul_dvd_mul_left _ H2) _ },
  { rw [mul_comm b, ← mul_assoc],
    exact dvd_mul_of_dvd_left (mul_dvd_mul_right H1 _) _ }
end

variables {I : Type v} {s : I → R}

theorem is_coprime_prod_of_pairwise_coprime (hs : pairwise (is_coprime on s)) {t : finset I}
  {x : I} : x ∉ t → is_coprime (s x) (∏ y in t, s y) :=
finset.induction_on t (λ _, ⟨0, 1, by { rw [zero_mul, zero_add, one_mul], refl }⟩)
(λ a r har ih hxar,
have hxa : x ≠ a, from mt (λ h, (h ▸ finset.mem_insert_self x r : x ∈ insert a r)) hxar,
have hxr : x ∉ r, from mt finset.mem_insert_of_mem hxar,
let ⟨ia, ib, hiaib⟩ := ih hxr, ⟨c, d, hcd⟩ := hs _ _ hxa in
⟨ia * s x * c + ia * d * s a + ib * (∏ y in r, s y) * c, ib * d,
calc  (ia * s x * c + ia * d * s a + ib * (∏ y in r, s y) * c) * s x +
        ib * d * (∏ y in insert a r, s y)
    = (ia * s x * c + ia * d * s a + ib * (∏ y in r, s y) * c) * s x +
        ib * d * (s a * (∏ y in r, s y)) : by rw finset.prod_insert har
... = (ia * s x + ib * (∏ y in r, s y)) * (c * s x + d * s a) : by ring
... = 1 : by rw [hiaib, hcd, mul_one]⟩)

theorem finset.prod_dvd_of_coprime (Hs : pairwise (is_coprime on s)) (Hs1 : ∀ i, s i ∣ z)
  {t : finset I} : ∏ x in t, s x ∣ z :=
finset.induction_on t (one_dvd z) (λ a r har ih, by { rw finset.prod_insert har,
exact (is_coprime_prod_of_pairwise_coprime Hs har).mul_dvd (Hs1 a) ih })

theorem fintype.prod_dvd_of_coprime [fintype I] (Hs : pairwise (is_coprime on s))
  (Hs1 : ∀ i, s i ∣ z) : ∏ x, s x ∣ z :=
finset.prod_dvd_of_coprime Hs Hs1
