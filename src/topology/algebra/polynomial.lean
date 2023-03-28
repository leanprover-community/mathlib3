/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import data.polynomial.algebra_map
import data.polynomial.inductions
import data.polynomial.splits
import ring_theory.polynomial.vieta
import analysis.normed.field.basic

/-!
# Polynomials and limits

In this file we prove the following lemmas.

* `polynomial.continuous_eval₂: `polynomial.eval₂` defines a continuous function.
* `polynomial.continuous_aeval: `polynomial.aeval` defines a continuous function;
  we also prove convenience lemmas `polynomial.continuous_at_aeval`,
  `polynomial.continuous_within_at_aeval`, `polynomial.continuous_on_aeval`.
* `polynomial.continuous`:  `polynomial.eval` defines a continuous functions;
  we also prove convenience lemmas `polynomial.continuous_at`, `polynomial.continuous_within_at`,
  `polynomial.continuous_on`.
* `polynomial.tendsto_norm_at_top`: `λ x, ‖polynomial.eval (z x) p‖` tends to infinity provided that
  `λ x, ‖z x‖` tends to infinity and `0 < degree p`;
* `polynomial.tendsto_abv_eval₂_at_top`, `polynomial.tendsto_abv_at_top`,
  `polynomial.tendsto_abv_aeval_at_top`: a few versions of the previous statement for
  `is_absolute_value abv` instead of norm.

## Tags

polynomial, continuity
-/

open is_absolute_value filter

namespace polynomial
open_locale polynomial

section topological_semiring

variables {R S : Type*} [semiring R] [topological_space R] [topological_semiring R]
  (p : R[X])

@[continuity]
protected lemma continuous_eval₂ [semiring S] (p : S[X]) (f : S →+* R) :
  continuous (λ x, p.eval₂ f x) :=
begin
  simp only [eval₂_eq_sum, finsupp.sum],
  exact continuous_finset_sum _ (λ c hc, continuous_const.mul (continuous_pow _))
end

@[continuity]
protected lemma continuous : continuous (λ x, p.eval x) :=
p.continuous_eval₂ _

protected lemma continuous_at {a : R} : continuous_at (λ x, p.eval x) a :=
p.continuous.continuous_at

protected lemma continuous_within_at {s a} : continuous_within_at (λ x, p.eval x) s a :=
p.continuous.continuous_within_at

protected lemma continuous_on {s} : continuous_on (λ x, p.eval x) s :=
p.continuous.continuous_on

end topological_semiring

section topological_algebra

variables {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]
  [topological_space A] [topological_semiring A]
  (p : R[X])

@[continuity]
protected lemma continuous_aeval : continuous (λ x : A, aeval x p) :=
p.continuous_eval₂ _

protected lemma continuous_at_aeval {a : A} : continuous_at (λ x : A, aeval x p) a :=
p.continuous_aeval.continuous_at

protected lemma continuous_within_at_aeval {s a} : continuous_within_at (λ x : A, aeval x p) s a :=
p.continuous_aeval.continuous_within_at

protected lemma continuous_on_aeval {s} : continuous_on (λ x : A, aeval x p) s :=
p.continuous_aeval.continuous_on

end topological_algebra

lemma tendsto_abv_eval₂_at_top {R S k α : Type*} [semiring R] [ring S] [linear_ordered_field k]
  (f : R →+* S) (abv : S → k) [is_absolute_value abv] (p : R[X]) (hd : 0 < degree p)
  (hf : f p.leading_coeff ≠ 0) {l : filter α} {z : α → S} (hz : tendsto (abv ∘ z) l at_top) :
  tendsto (λ x, abv (p.eval₂ f (z x))) l at_top :=
begin
  revert hf, refine degree_pos_induction_on p hd _ _ _; clear hd p,
  { rintros c - hc,
    rw [leading_coeff_mul_X, leading_coeff_C] at hc,
    simpa [abv_mul abv] using hz.const_mul_at_top ((abv_pos abv).2 hc) },
  { intros p hpd ihp hf,
    rw [leading_coeff_mul_X] at hf,
    simpa [abv_mul abv] using  (ihp hf).at_top_mul_at_top hz },
  { intros p a hd ihp hf,
    rw [add_comm, leading_coeff_add_of_degree_lt (degree_C_le.trans_lt hd)] at hf,
    refine tendsto_at_top_of_add_const_right (abv (-f a)) _,
    refine tendsto_at_top_mono (λ _, abv_add abv _ _) _,
    simpa using ihp hf }
end

lemma tendsto_abv_at_top {R k α : Type*} [ring R] [linear_ordered_field k]
  (abv : R → k) [is_absolute_value abv] (p : R[X]) (h : 0 < degree p)
  {l : filter α} {z : α → R} (hz : tendsto (abv ∘ z) l at_top) :
  tendsto (λ x, abv (p.eval (z x))) l at_top :=
tendsto_abv_eval₂_at_top _ _ _ h (mt leading_coeff_eq_zero.1 $ ne_zero_of_degree_gt h) hz

lemma tendsto_abv_aeval_at_top {R A k α : Type*} [comm_semiring R] [ring A] [algebra R A]
  [linear_ordered_field k] (abv : A → k) [is_absolute_value abv] (p : R[X])
  (hd : 0 < degree p) (h₀ : algebra_map R A p.leading_coeff ≠ 0)
  {l : filter α} {z : α → A} (hz : tendsto (abv ∘ z) l at_top) :
  tendsto (λ x, abv (aeval (z x) p)) l at_top :=
tendsto_abv_eval₂_at_top _ abv p hd h₀ hz

variables {α R : Type*} [normed_ring R] [is_absolute_value (norm : R → ℝ)]

lemma tendsto_norm_at_top (p : R[X]) (h : 0 < degree p) {l : filter α} {z : α → R}
  (hz : tendsto (λ x, ‖z x‖) l at_top) :
  tendsto (λ x, ‖p.eval (z x)‖) l at_top :=
p.tendsto_abv_at_top norm h hz

lemma exists_forall_norm_le [proper_space R] (p : R[X]) :
  ∃ x, ∀ y, ‖p.eval x‖ ≤ ‖p.eval y‖ :=
if hp0 : 0 < degree p
then p.continuous.norm.exists_forall_le $ p.tendsto_norm_at_top hp0 tendsto_norm_cocompact_at_top
else ⟨p.coeff 0, by rw [eq_C_of_degree_le_zero (le_of_not_gt hp0)]; simp⟩

section roots

open_locale polynomial nnreal

variables {F K : Type*} [comm_ring F] [normed_field K]

open multiset

lemma eq_one_of_roots_le {p : F[X]} {f : F →+* K} {B : ℝ} (hB : B < 0)
  (h1 : p.monic) (h2 : splits f p) (h3 : ∀ z ∈ (map f p).roots, ‖z‖ ≤ B) :
  p = 1 :=
h1.nat_degree_eq_zero_iff_eq_one.mp begin
  contrapose !hB,
  rw [← h1.nat_degree_map f, nat_degree_eq_card_roots' h2] at hB,
  obtain ⟨z, hz⟩ := card_pos_iff_exists_mem.mp (zero_lt_iff.mpr hB),
  exact le_trans (norm_nonneg _) (h3 z hz),
end

lemma coeff_le_of_roots_le {p : F[X]} {f : F →+* K} {B : ℝ} (i : ℕ)
  (h1 : p.monic) (h2 : splits f p) (h3 : ∀ z ∈ (map f p).roots, ‖z‖ ≤ B) :
  ‖ (map f p).coeff i ‖ ≤ B^(p.nat_degree - i) * p.nat_degree.choose i  :=
begin
  obtain hB | hB := lt_or_le B 0,
  { rw [eq_one_of_roots_le hB h1 h2 h3, polynomial.map_one,
      nat_degree_one, zero_tsub, pow_zero, one_mul, coeff_one],
    split_ifs; norm_num [h] },
  rw ← h1.nat_degree_map f,
  obtain hi | hi := lt_or_le (map f p).nat_degree i,
  { rw [coeff_eq_zero_of_nat_degree_lt hi, norm_zero], positivity },
  rw [coeff_eq_esymm_roots_of_splits ((splits_id_iff_splits f).2 h2) hi,
    (h1.map _).leading_coeff, one_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul],
  apply ((norm_multiset_sum_le _).trans $ sum_le_card_nsmul _ _ $ λ r hr, _).trans,
  { rw [multiset.map_map, card_map, card_powerset_len,
      ←nat_degree_eq_card_roots' h2, nat.choose_symm hi, mul_comm, nsmul_eq_mul] },
  simp_rw multiset.mem_map at hr,
  obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := hr,
  rw mem_powerset_len at hs,
  lift B to ℝ≥0 using hB,
  rw [←coe_nnnorm, ←nnreal.coe_pow, nnreal.coe_le_coe,
    ←nnnorm_hom_apply, ←monoid_hom.coe_coe, monoid_hom.map_multiset_prod],
  refine (prod_le_pow_card _ B $ λ x hx, _).trans_eq (by rw [card_map, hs.2]),
  obtain ⟨z, hz, rfl⟩ := multiset.mem_map.1 hx,
  exact h3 z (mem_of_le hs.1 hz),
end

/-- The coefficients of the monic polynomials of bounded degree with bounded roots are
uniformely bounded. -/
lemma coeff_bdd_of_roots_le {B : ℝ} {d : ℕ} (f : F →+* K) {p : F[X]}
  (h1 : p.monic) (h2 : splits f p) (h3 : p.nat_degree ≤ d) (h4 : ∀ z ∈ (map f p).roots, ‖z‖ ≤ B)
  (i : ℕ) : ‖(map f p).coeff i‖ ≤ (max B 1) ^ d * d.choose (d / 2) :=
begin
  obtain hB | hB := le_or_lt 0 B,
  { apply (coeff_le_of_roots_le i h1 h2 h4).trans,
    calc
    _   ≤ (max B 1) ^ (p.nat_degree - i) * (p.nat_degree.choose i)
      : mul_le_mul_of_nonneg_right (pow_le_pow_of_le_left hB (le_max_left _ _) _) _
    ... ≤ (max B 1) ^ d * (p.nat_degree.choose i)
      : mul_le_mul_of_nonneg_right ((pow_mono (le_max_right _ _)) (le_trans (nat.sub_le _ _) h3)) _
    ... ≤ (max B 1) ^ d * d.choose (d / 2)
      : mul_le_mul_of_nonneg_left (nat.cast_le.mpr ((i.choose_mono h3).trans
        (i.choose_le_middle d))) _,
    all_goals { positivity, }},
  { rw [eq_one_of_roots_le hB h1 h2 h4, polynomial.map_one, coeff_one],
    refine trans _ (one_le_mul_of_one_le_of_one_le (one_le_pow_of_one_le (le_max_right B 1) d) _),
    { split_ifs; norm_num, },
    { exact_mod_cast nat.succ_le_iff.mpr (nat.choose_pos (d.div_le_self 2)), }},
end

end roots

end polynomial
