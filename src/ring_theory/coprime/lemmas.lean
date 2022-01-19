/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Ken Lee, Chris Hughes
-/
import algebra.big_operators.basic
import data.fintype.basic
import data.int.gcd
import data.set.pairwise
import ring_theory.coprime.basic

/-!
# Additional lemmas about elements of a ring satisfying `is_coprime`

These lemmas are in a separate file to the definition of `is_coprime` as they require more imports.

Notably, this includes lemmas about `finset.prod` as this requires importing big_operators, and
lemmas about `has_pow` since these are easiest to prove via `finset.prod`.

-/

universes u v

variables {R : Type u} {I : Type v} [comm_semiring R] {x y z : R} {s : I → R} {t : finset I}

open_locale big_operators classical

theorem nat.is_coprime_iff_coprime {m n : ℕ} : is_coprime (m : ℤ) n ↔ nat.coprime m n :=
⟨λ ⟨a, b, H⟩, nat.eq_one_of_dvd_one $ int.coe_nat_dvd.1 $ by { rw [int.coe_nat_one, ← H],
  exact dvd_add (dvd_mul_of_dvd_right (int.coe_nat_dvd.2 $ nat.gcd_dvd_left m n) _)
    (dvd_mul_of_dvd_right (int.coe_nat_dvd.2 $ nat.gcd_dvd_right m n) _) },
λ H, ⟨nat.gcd_a m n, nat.gcd_b m n, by rw [mul_comm _ (m : ℤ), mul_comm _ (n : ℤ),
    ← nat.gcd_eq_gcd_ab, show _ = _, from H, int.coe_nat_one]⟩⟩

theorem is_coprime.prod_left : (∀ i ∈ t, is_coprime (s i) x) → is_coprime (∏ i in t, s i) x :=
finset.induction_on t (λ _, is_coprime_one_left) $ λ b t hbt ih H,
by { rw finset.prod_insert hbt, rw finset.forall_mem_insert at H, exact H.1.mul_left (ih H.2) }

theorem is_coprime.prod_right : (∀ i ∈ t, is_coprime x (s i)) → is_coprime x (∏ i in t, s i) :=
by simpa only [is_coprime_comm] using is_coprime.prod_left

theorem is_coprime.prod_left_iff : is_coprime (∏ i in t, s i) x ↔ ∀ i ∈ t, is_coprime (s i) x :=
finset.induction_on t (iff_of_true is_coprime_one_left $ λ _, false.elim) $ λ b t hbt ih,
by rw [finset.prod_insert hbt, is_coprime.mul_left_iff, ih, finset.forall_mem_insert]

theorem is_coprime.prod_right_iff : is_coprime x (∏ i in t, s i) ↔ ∀ i ∈ t, is_coprime x (s i) :=
by simpa only [is_coprime_comm] using is_coprime.prod_left_iff

theorem is_coprime.of_prod_left (H1 : is_coprime (∏ i in t, s i) x) (i : I) (hit : i ∈ t) :
  is_coprime (s i) x :=
is_coprime.prod_left_iff.1 H1 i hit

theorem is_coprime.of_prod_right (H1 : is_coprime x (∏ i in t, s i)) (i : I) (hit : i ∈ t) :
  is_coprime x (s i) :=
is_coprime.prod_right_iff.1 H1 i hit

theorem finset.prod_dvd_of_coprime :
  ∀ (Hs : set.pairwise (↑t : set I) (is_coprime on s)) (Hs1 : ∀ i ∈ t, s i ∣ z),
  ∏ x in t, s x ∣ z :=
finset.induction_on t (λ _ _, one_dvd z)
begin
  intros a r har ih Hs Hs1,
  rw finset.prod_insert har,
  have aux1 : a ∈ (↑(insert a r) : set I) := finset.mem_insert_self a r,
  refine (is_coprime.prod_right $ λ i hir, Hs a aux1 i _ (by { rintro rfl, exact har hir })).mul_dvd
    (Hs1 a aux1) (ih (Hs.mono _) $ λ i hi, Hs1 i (finset.mem_insert_of_mem hi)),
  { exact finset.mem_insert_of_mem hir },
  { simp only [finset.coe_insert, set.subset_insert] }
end

theorem fintype.prod_dvd_of_coprime [fintype I] (Hs : pairwise (is_coprime on s))
  (Hs1 : ∀ i, s i ∣ z) : ∏ x, s x ∣ z :=
finset.prod_dvd_of_coprime (Hs.set_pairwise _) (λ i _, Hs1 i)

variables {m n : ℕ}

theorem is_coprime.pow_left (H : is_coprime x y) : is_coprime (x ^ m) y :=
by { rw [← finset.card_range m, ← finset.prod_const], exact is_coprime.prod_left (λ _ _, H) }

theorem is_coprime.pow_right (H : is_coprime x y) : is_coprime x (y ^ n) :=
by { rw [← finset.card_range n, ← finset.prod_const], exact is_coprime.prod_right (λ _ _, H) }

theorem is_coprime.pow (H : is_coprime x y) : is_coprime (x ^ m) (y ^ n) :=
H.pow_left.pow_right

theorem is_coprime.pow_left_iff (hm : 0 < m) : is_coprime (x ^ m) y ↔ is_coprime x y :=
begin
  refine ⟨λ h, _, is_coprime.pow_left⟩,
  rw [← finset.card_range m, ← finset.prod_const] at h,
  exact h.of_prod_left 0 (finset.mem_range.mpr hm),
end

theorem is_coprime.pow_right_iff (hm : 0 < m) : is_coprime x (y ^ m) ↔ is_coprime x y :=
is_coprime_comm.trans $ (is_coprime.pow_left_iff hm).trans $ is_coprime_comm

theorem is_coprime.pow_iff (hm : 0 < m) (hn : 0 < n) :
  is_coprime (x ^ m) (y ^ n) ↔ is_coprime x y :=
(is_coprime.pow_left_iff hm).trans $ is_coprime.pow_right_iff hn
