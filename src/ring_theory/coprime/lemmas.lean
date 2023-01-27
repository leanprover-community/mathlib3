/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Ken Lee, Chris Hughes
-/
import algebra.big_operators.ring
import data.fintype.basic
import data.int.gcd
import ring_theory.coprime.basic

/-!
# Additional lemmas about elements of a ring satisfying `is_coprime`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

These lemmas are in a separate file to the definition of `is_coprime` as they require more imports.

Notably, this includes lemmas about `finset.prod` as this requires importing big_operators, and
lemmas about `has_pow` since these are easiest to prove via `finset.prod`.

-/

universes u v

variables {R : Type u} {I : Type v} [comm_semiring R] {x y z : R} {s : I → R} {t : finset I}

open_locale big_operators
section
open_locale classical

theorem nat.is_coprime_iff_coprime {m n : ℕ} : is_coprime (m : ℤ) n ↔ nat.coprime m n :=
⟨λ ⟨a, b, H⟩, nat.eq_one_of_dvd_one $ int.coe_nat_dvd.1 $ by { rw [int.coe_nat_one, ← H],
  exact dvd_add (dvd_mul_of_dvd_right (int.coe_nat_dvd.2 $ nat.gcd_dvd_left m n) _)
    (dvd_mul_of_dvd_right (int.coe_nat_dvd.2 $ nat.gcd_dvd_right m n) _) },
λ H, ⟨nat.gcd_a m n, nat.gcd_b m n, by rw [mul_comm _ (m : ℤ), mul_comm _ (n : ℤ),
    ← nat.gcd_eq_gcd_ab, show _ = _, from H, int.coe_nat_one]⟩⟩

alias nat.is_coprime_iff_coprime ↔ is_coprime.nat_coprime nat.coprime.is_coprime

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
  ∀ (Hs : (t : set I).pairwise (is_coprime on s)) (Hs1 : ∀ i ∈ t, s i ∣ z),
  ∏ x in t, s x ∣ z :=
finset.induction_on t (λ _ _, one_dvd z)
begin
  intros a r har ih Hs Hs1,
  rw finset.prod_insert har,
  have aux1 : a ∈ (↑(insert a r) : set I) := finset.mem_insert_self a r,
  refine (is_coprime.prod_right $ λ i hir, Hs aux1 (finset.mem_insert_of_mem hir)
    $ by { rintro rfl, exact har hir }).mul_dvd
    (Hs1 a aux1) (ih (Hs.mono _) $ λ i hi, Hs1 i $ finset.mem_insert_of_mem hi),
  simp only [finset.coe_insert, set.subset_insert],
end

theorem fintype.prod_dvd_of_coprime [fintype I] (Hs : pairwise (is_coprime on s))
  (Hs1 : ∀ i, s i ∣ z) : ∏ x, s x ∣ z :=
finset.prod_dvd_of_coprime (Hs.set_pairwise _) (λ i _, Hs1 i)

end

open finset

lemma exists_sum_eq_one_iff_pairwise_coprime [decidable_eq I] (h : t.nonempty) :
  (∃ μ : I → R, ∑ i in t, μ i * ∏ j in t \ {i}, s j = 1) ↔ pairwise (is_coprime on λ i : t, s i) :=
begin
  refine h.cons_induction _ _; clear' t h,
  { simp only [pairwise, sum_singleton, finset.sdiff_self, prod_empty, mul_one,
      exists_apply_eq_apply, ne.def, true_iff],
    rintro a ⟨i, hi⟩ ⟨j, hj⟩ h,
    rw finset.mem_singleton at hi hj,
    simpa [hi, hj] using h },
  intros a t hat h ih,
  rw pairwise_cons',
  have mem : ∀ x ∈ t, a ∈ insert a t \ {x} := λ x hx, by
    { rw [mem_sdiff, mem_singleton], exact ⟨mem_insert_self _ _, λ ha, hat (ha.symm.cases_on hx)⟩ },
  split,
  { rintro ⟨μ, hμ⟩,
    rw [sum_cons, cons_eq_insert, sdiff_singleton_eq_erase, erase_insert hat] at hμ,
    refine ⟨ih.mp ⟨pi.single h.some (μ a * s h.some) + μ * λ _, s a, _⟩, λ b hb, _⟩,
    { rw [prod_eq_mul_prod_diff_singleton h.some_spec, ← mul_assoc,
        ← @if_pos _ _ h.some_spec R (_ * _) 0, ← sum_pi_single', ← sum_add_distrib] at hμ,
      rw [← hμ, sum_congr rfl], intros x hx, convert @add_mul R _ _ _ _ _ _ using 2,
      { by_cases hx : x = h.some,
        { rw [hx, pi.single_eq_same, pi.single_eq_same] },
        { rw [pi.single_eq_of_ne hx, pi.single_eq_of_ne hx, zero_mul] } },
      { convert (mul_assoc _ _ _).symm,
        convert prod_eq_mul_prod_diff_singleton (mem x hx) _ using 3,
        convert sdiff_sdiff_comm, rw [sdiff_singleton_eq_erase, erase_insert hat] } },
    { have : is_coprime (s b) (s a) :=
        ⟨μ a * ∏ i in t \ {b}, s i, ∑ i in t, μ i * ∏ j in t \ {i}, s j, _⟩,
      { exact ⟨this.symm, this⟩ },
      rw [mul_assoc, ← prod_eq_prod_diff_singleton_mul hb, sum_mul, ← hμ, sum_congr rfl],
      intros x hx, convert mul_assoc _ _ _,
      convert prod_eq_prod_diff_singleton_mul (mem x hx) _ using 3,
      convert sdiff_sdiff_comm, rw [sdiff_singleton_eq_erase, erase_insert hat] } },
  { rintro ⟨hs, Hb⟩, obtain ⟨μ, hμ⟩ := ih.mpr hs,
    obtain ⟨u, v, huv⟩ := is_coprime.prod_left (λ b hb, (Hb b hb).right),
    use λ i, if i = a then u else v * μ i,
    have hμ' : ∑ i in t, v * ((μ i * ∏ j in t \ {i}, s j) * s a) = v * s a := by
      rw [← mul_sum, ← sum_mul, hμ, one_mul],
    rw [sum_cons, cons_eq_insert, sdiff_singleton_eq_erase, erase_insert hat, if_pos rfl,
      ← huv, ← hμ', sum_congr rfl], intros x hx,
    rw [mul_assoc, if_neg (λ ha : x = a, hat (ha.cases_on hx))],
    convert mul_assoc _ _ _, convert (prod_eq_prod_diff_singleton_mul (mem x hx) _).symm using 3,
    convert sdiff_sdiff_comm, rw [sdiff_singleton_eq_erase, erase_insert hat] }
end

lemma exists_sum_eq_one_iff_pairwise_coprime' [fintype I] [nonempty I] [decidable_eq I] :
  (∃ μ : I → R, ∑ (i : I), μ i * ∏ j in {i}ᶜ, s j = 1) ↔ pairwise (is_coprime on s) :=
begin
  convert exists_sum_eq_one_iff_pairwise_coprime finset.univ_nonempty using 1,
  simp only [function.on_fun, pairwise_subtype_iff_pairwise_finset', coe_univ, set.pairwise_univ],
  assumption
end

lemma pairwise_coprime_iff_coprime_prod [decidable_eq I] :
  pairwise (is_coprime on λ i : t, s i) ↔ ∀ i ∈ t, is_coprime (s i) (∏ j in t \ {i}, (s j)) :=
begin
  refine ⟨λ hp i hi, is_coprime.prod_right_iff.mpr (λ j hj, _), λ hp, _⟩,
  { rw [finset.mem_sdiff, finset.mem_singleton] at hj,
    obtain ⟨hj, ji⟩ := hj,
    exact @hp ⟨i, hi⟩ ⟨j, hj⟩ (λ h, ji (congr_arg coe h).symm) },
  { rintro ⟨i, hi⟩ ⟨j, hj⟩ h,
    apply is_coprime.prod_right_iff.mp (hp i hi),
    exact finset.mem_sdiff.mpr ⟨hj, λ f, h $ subtype.ext (finset.mem_singleton.mp f).symm⟩ }
end

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
