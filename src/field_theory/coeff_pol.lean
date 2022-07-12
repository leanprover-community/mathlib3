/-
Copyright (c) 2022 X.-F. Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: X-F. Roblot
-/

import analysis.normed.field.basic
import field_theory.splitting_field

/-!
# Roots and coeffs

This is a temporary file containing the proof that, if the roots of a polynomials are bounded,
then its coefficients are also bounded. It relies on PR15008.
-/

section admit
namespace multiset

variables {R : Type*} [comm_ring R]

/-- import from PR15008 -/
def esymm (s : multiset R) (n : ℕ) : R := ((s.powerset_len n).map multiset.prod).sum

/-- import from PR15008 -/
lemma prod_X_sub_C_coeff (s : multiset R) {k : ℕ} (h : k ≤ s.card):
    polynomial.coeff (s.map (λ r, polynomial.X - polynomial.C r)).prod k =
    (-1)^k * s.esymm (s.card - k) :=
begin
  sorry,
end

end multiset
end admit

open_locale polynomial
open_locale nnreal

variables {F K : Type*} [field F] [nontrivial K] [normed_field K]

namespace polynomial

lemma coeff_le_of_roots_le {p : F[X]} {f : F →+* K} {B : ℝ} (i : ℕ)
  (h1 : p.monic) (h2 : splits f p) (h3 : ∀ z ∈ (map f p).roots, ∥z∥ ≤ B) :
  ∥ (map f p).coeff i ∥ ≤ B^(p.nat_degree - i) * p.nat_degree.choose i  :=
begin
  have hcd :  multiset.card (map f p).roots = p.nat_degree := (nat_degree_eq_card_roots h2).symm,
  by_cases hB : 0 ≤ B,
  {
  by_cases hi : i ≤ p.nat_degree,
  { rw eq_prod_roots_of_splits h2,
    rw [monic.def.mp h1, ring_hom.map_one, ring_hom.map_one, one_mul],
    rw multiset.prod_X_sub_C_coeff,
    swap, rwa hcd,
    rw [norm_mul, (by norm_num : ∥(-1 : K) ^ i∥=  1), one_mul],
    apply le_trans (multiset.le_sum_of_subadditive norm _ _ _ ),
    rotate, exact norm_zero, exact norm_add_le,
    rw multiset.map_map,
    suffices : ∀ r ∈ multiset.map (norm_hom ∘ multiset.prod)
      (multiset.powerset_len (multiset.card (map f p).roots - i) (map f p).roots),
      r ≤ B^(p.nat_degree - i),
    { convert multiset.sum_le_sum_sum _ this,
      simp only [hi, hcd, multiset.map_const, multiset.card_map, multiset.card_powerset_len,
        nat.choose_symm, multiset.sum_repeat, nsmul_eq_mul, mul_comm], },
    intros r hr,
    obtain ⟨t, ht⟩ := multiset.mem_map.mp hr,
    lift B to ℝ≥0 using hB,
    lift (multiset.map norm_hom t) to (multiset ℝ≥0) with normt,
    swap, { intros x hx,
      obtain ⟨z, hz⟩ := multiset.mem_map.mp hx,
      rw ←hz.right,
      exact norm_nonneg z, },
    suffices : ∀ r ∈ normt, r ≤ B,
    { convert multiset.prod_le_sum_prod _ this using 1,
      { rw_mod_cast [←ht.right, function.comp_apply, ←multiset.prod_hom t norm_hom, ←h], },
      { rw [multiset.map_const, multiset.prod_repeat, nnreal.coe_pow],
        congr,
        have card_eq : _, from congr_arg (λ (t : multiset ℝ), t.card) h,
        rw [multiset.card_map, multiset.card_map] at card_eq,
        rw [card_eq, ←hcd],
        exact (multiset.mem_powerset_len.mp ht.left).right.symm, }},
    intros r hr,
    suffices : ∃ z ∈ t, norm z = r,
    { obtain ⟨z, hzt, hzr⟩ := this,
      have zleB : ∥z∥ ≤ B,
      { exact h3 z (multiset.mem_of_le (multiset.mem_powerset_len.mp ht.left).left hzt) },
      rwa hzr at zleB, },
    have rmem : (r : ℝ) ∈ multiset.map coe normt, from multiset.mem_map_of_mem _ hr,
    rw h at rmem,
    obtain ⟨z, hz⟩ := multiset.mem_map.mp rmem,
    use z, exact hz, },
  { push_neg at hi,
    rw [nat.choose_eq_zero_of_lt hi, coeff_eq_zero_of_nat_degree_lt, norm_zero],
    rw_mod_cast mul_zero,
    { rwa monic.nat_degree_map h1,
      apply_instance, }}},
  { push_neg at hB,
    have : (map f p).roots = 0,
    { contrapose! hB,
      obtain ⟨z, hz⟩ := multiset.exists_mem_of_ne_zero hB,
      exact le_trans (norm_nonneg z) (h3 z hz), },
    have hdg : p.nat_degree = 0,
    { rw this at hcd,
      rw multiset.card_zero at hcd,
      exact hcd.symm, },
    by_cases hi : i = 0,
    { rw [hdg, hi, (monic.nat_degree_eq_zero_iff_eq_one h1).mp hdg],
      simp only [polynomial.map_one, coeff_one_zero, norm_one, pow_zero, nat.choose_self,
        nat.cast_one, mul_one], },
    { replace hi := zero_lt_iff.mpr hi,
      rw ←hdg at hi,
      rw [nat.choose_eq_zero_of_lt hi, coeff_eq_zero_of_nat_degree_lt, norm_zero],
      rw_mod_cast mul_zero,
      { rwa monic.nat_degree_map h1,
        apply_instance, }}},
end

end polynomial
