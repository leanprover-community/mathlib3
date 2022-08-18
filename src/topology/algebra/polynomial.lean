/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import analysis.normed_space.basic
import data.polynomial.algebra_map
import data.polynomial.inductions
import ring_theory.polynomial.vieta
import field_theory.splitting_field

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
* `polynomial.tendsto_norm_at_top`: `λ x, ∥polynomial.eval (z x) p∥` tends to infinity provided that
  `λ x, ∥z x∥` tends to infinity and `0 < degree p`;
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
  dsimp only [eval₂_eq_sum, finsupp.sum],
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
  (hz : tendsto (λ x, ∥z x∥) l at_top) :
  tendsto (λ x, ∥p.eval (z x)∥) l at_top :=
p.tendsto_abv_at_top norm h hz

lemma exists_forall_norm_le [proper_space R] (p : R[X]) :
  ∃ x, ∀ y, ∥p.eval x∥ ≤ ∥p.eval y∥ :=
if hp0 : 0 < degree p
then p.continuous.norm.exists_forall_le $ p.tendsto_norm_at_top hp0 tendsto_norm_cocompact_at_top
else ⟨p.coeff 0, by rw [eq_C_of_degree_le_zero (le_of_not_gt hp0)]; simp⟩

section roots

open_locale polynomial
open_locale nnreal

variables {F K : Type*} [field F] [nontrivial K] [normed_field K]

open multiset

lemma coeff_le_of_roots_le {p : F[X]} {f : F →+* K} {B : ℝ} (i : ℕ)
  (h1 : p.monic) (h2 : splits f p) (h3 : ∀ z ∈ (map f p).roots, ∥z∥ ≤ B) :
  ∥ (map f p).coeff i ∥ ≤ B^(p.nat_degree - i) * p.nat_degree.choose i  :=
begin
  have hcd : card (map f p).roots = p.nat_degree := (nat_degree_eq_card_roots h2).symm,
  by_cases hB : 0 ≤ B,
  { by_cases hi : i ≤ p.nat_degree,
    { rw [eq_prod_roots_of_splits h2, monic.def.mp h1, ring_hom.map_one, ring_hom.map_one, one_mul],
      rw prod_X_sub_C_coeff,
      swap, rwa hcd,
      rw [norm_mul, (by norm_num : ∥(-1 : K) ^ (card (map f p).roots - i)∥=  1), one_mul],
      apply le_trans (le_sum_of_subadditive norm _ _ _ ),
      rotate, exact norm_zero, exact norm_add_le,
      rw multiset.map_map,
      suffices : ∀ r ∈ multiset.map (norm_hom ∘ prod)
        (powerset_len (card (map f p).roots - i) (map f p).roots), r ≤ B^(p.nat_degree - i),
      { convert sum_le_sum_sum _ this,
        simp only [hi, hcd, multiset.map_const, card_map, card_powerset_len, nat.choose_symm,
          sum_repeat, nsmul_eq_mul, mul_comm], },
      { intros r hr,
        obtain ⟨t, ht⟩ := multiset.mem_map.mp hr,
        have hbounds : ∀ x ∈ (multiset.map norm_hom t), 0 ≤ x ∧ x ≤ B,
        { intros x hx,
          obtain ⟨z, hz⟩ := multiset.mem_map.mp hx,
          rw ←hz.right,
          exact ⟨norm_nonneg z,
            h3 z (mem_of_le (mem_powerset_len.mp ht.left).left hz.left)⟩, },
        lift B to ℝ≥0 using hB,
        lift (multiset.map norm_hom t) to (multiset ℝ≥0) using (λ x hx, (hbounds x hx).left)
          with normt hn,
        rw (by rw_mod_cast [←ht.right, function.comp_apply, ←prod_hom t norm_hom, ←hn] :
          r = normt.prod),
        convert multiset.prod_le_pow_card normt _ _,
        { rw (_ : card normt = card (multiset.map coe normt)),
          rwa [hn, ←hcd, card_map, (mem_powerset_len.mp ht.left).right.symm],
          rwa card_map, },
        { intros x hx,
          have xmem : (x : ℝ) ∈ multiset.map coe normt := mem_map_of_mem _ hx,
          exact (hbounds x xmem).right, }}},
    { push_neg at hi,
      rw [nat.choose_eq_zero_of_lt hi, coeff_eq_zero_of_nat_degree_lt, norm_zero],
      rw_mod_cast mul_zero,
      { rwa monic.nat_degree_map h1,
        apply_instance, }}},
  { push_neg at hB,
    have noroots : (map f p).roots = 0,
    { contrapose! hB,
      obtain ⟨z, hz⟩ := exists_mem_of_ne_zero hB,
      exact le_trans (norm_nonneg z) (h3 z hz), },
    suffices : p.nat_degree = 0,
    { by_cases hi : i = 0,
      { rw [this, hi, (monic.nat_degree_eq_zero_iff_eq_one h1).mp this],
        simp only [polynomial.map_one, coeff_one_zero, norm_one, pow_zero, nat.choose_self,
          nat.cast_one, mul_one], },
      { replace hi := zero_lt_iff.mpr hi,
        rw ←this at hi,
        rw [nat.choose_eq_zero_of_lt hi, coeff_eq_zero_of_nat_degree_lt, norm_zero],
        rw_mod_cast mul_zero,
        { rwa monic.nat_degree_map h1,
          apply_instance, }}},
    rw [←hcd, noroots, card_zero], },
end

end roots

end polynomial
