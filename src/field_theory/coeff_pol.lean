/-
Copyright (c) 2022 X.-F. Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: X-F. Roblot
-/

import analysis.normed.field.basic
import field_theory.splitting_field
import ring_theory.polynomial.vieta

/-!
# Roots and coeffs

This is a temporary file containing the proof that, if the roots of a polynomials are bounded,
then its coefficients are also bounded. It relies on PR15008.
-/

open_locale polynomial
open_locale nnreal

variables {F K : Type*} [field F] [nontrivial K] [normed_field K]

open multiset

namespace polynomial

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
        simp only [hi, hcd, map_const, card_map, card_powerset_len, nat.choose_symm, sum_repeat,
          nsmul_eq_mul, mul_comm], },
      { intros r hr,
        obtain ⟨t, ht⟩ := mem_map.mp hr,
        have hbounds : ∀ x ∈ (multiset.map norm_hom t), 0 ≤ x ∧ x ≤ B,
        { intros x hx,
          obtain ⟨z, hz⟩ := mem_map.mp hx,
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

end polynomial
