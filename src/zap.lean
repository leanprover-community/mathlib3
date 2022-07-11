/-
Copyright (c) 2022 X.-F. Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: X-F. Roblot
-/

import number_theory.number_field
import analysis.complex.polynomial

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

open set finite_dimensional complex
open_locale classical
open_locale big_operators
open_locale polynomial
open_locale nnreal

variables {K : Type*} [field K] [number_field K] {n : ℕ} (x : K)
open polynomial

noncomputable theory

example (s t : multiset ℝ) :
  s = t → s.prod = t.prod :=
begin
  exact congr_arg (λ (s : multiset ℝ), s.prod),
end

lemma bounded_coeffs_of_bounded_roots {p : ℂ[X]} {B : ℝ} (i : ℕ)
  (h0 : p.monic) (h1 : 0 ≤ B) (h2 : ∀ z ∈ p.roots, abs z ≤ B) :
  abs (p.coeff i) ≤ B^(p.nat_degree - i) * p.nat_degree.choose i  :=
begin
  have hsp : splits (ring_hom.id ℂ) p := is_alg_closed.splits_codomain p,
  have hcd :  multiset.card p.roots = p.nat_degree,
  { nth_rewrite 0 ←@polynomial.map_id ℂ _ p,
    exact (nat_degree_eq_card_roots hsp).symm, },
  by_cases hi : i ≤ p.nat_degree,
  { have hsp : splits (ring_hom.id ℂ) p := is_alg_closed.splits_codomain p,
    nth_rewrite 0 ←@polynomial.map_id ℂ _ p,
    rw eq_prod_roots_of_splits hsp,
    rw polynomial.map_id,
    rw ring_hom.id_apply,
    rw monic.def.mp h0,
    rw ring_hom.map_one,
    rw one_mul,
    rw multiset.prod_X_sub_C_coeff,
    swap, rwa hcd,
    rw [complex.abs_mul, (by norm_num : abs ((-1 : ℂ) ^ i) =  1), one_mul],
    apply le_trans (multiset.le_sum_of_subadditive complex.abs _ _ _ ),
    rotate, exact abs_zero, exact abs_add,
    rw multiset.map_map,
    suffices : ∀ r ∈ multiset.map (complex.abs ∘ multiset.prod)
      (multiset.powerset_len (multiset.card p.roots - i) p.roots), r ≤ B^(p.nat_degree - i),
    { convert multiset.sum_le_sum_sum _ this,
      simp only [hi, hcd, multiset.map_const, multiset.card_map, multiset.card_powerset_len,
        nat.choose_symm, multiset.sum_repeat, nsmul_eq_mul, mul_comm], },


    intros r hr,
    obtain ⟨t, ht⟩ := multiset.mem_map.mp hr,
    rw ←ht.right,
    lift B to ℝ≥0 using h1,
    lift (multiset.map complex.abs_hom t) to (multiset ℝ≥0) with t₀,
    swap,
    { intros x hx,
      obtain ⟨z, hz⟩ := multiset.mem_map.mp hx,
      rw ←hz.right,
      exact complex.abs_nonneg z, },
    have a1 : ∀ r ∈ t₀, r ≤ B,
    { intros r hr,
      have : (r : ℝ) ∈ multiset.map coe t₀, from multiset.mem_map_of_mem _ hr,
      rw h at this,
      obtain ⟨z, hz⟩ := multiset.mem_map.mp this,

      have : _, from multiset.mem_of_le (multiset.mem_powerset_len.mp ht.left).left hz.left,

      have : abs_hom z ≤ B, from h2 z this,
      simp only [*, nnreal.coe_le_coe] at *,
    },

    convert multiset.prod_le_sum_prod _ a1 using 1,
    { have : _, from congr_arg (λ (t : multiset ℝ), t.prod) h,
      rw multiset.prod_hom t complex.abs_hom at this,
      convert this.symm using 1,
      norm_cast, },
    { simp only [multiset.map_const, multiset.prod_repeat, nnreal.coe_pow, multiset.mem_powerset_len, function.comp_app,
  multiset.mem_map],
      congr,
      have : _, from congr_arg (λ (t : multiset ℝ), t.card) h,
      rw multiset.card_map at this,
      rw multiset.card_map at this,
      rw this,
      rw ←hcd,
      have : _, from multiset.mem_powerset_len.mp ht.left,
      exact this.right.symm, }},
  { push_neg at hi,
    rw [nat.choose_eq_zero_of_lt hi, coeff_eq_zero_of_nat_degree_lt, complex.abs_zero],
    rw_mod_cast mul_zero,
    { exact hi, }},
end

-- local attribute [-instance] algebra_rat
local attribute [-instance] complex.algebra

/- TODO. generalize to |roots| ≤ bound C -/
lemma minpoly_coeff_le_of_all_abs_eq_one (hx : x ∈ {x : K | ∀ (φ : K →+* ℂ), abs (φ x) = 1})
  (hxi : is_integral ℤ x) (i : ℕ) :
  |(minpoly ℤ x).coeff i| ≤ ((minpoly ℤ x).nat_degree.choose i) :=
begin
  have hmp : minpoly ℚ x = map (algebra_map ℤ ℚ) (minpoly ℤ x),
    from minpoly.gcd_domain_eq_field_fractions' ℚ hxi,
  have hdg : (minpoly ℚ x).nat_degree = (minpoly ℤ x).nat_degree,
  { rw hmp, convert nat_degree_map_eq_of_injective _ _,
    exact (algebra_map ℤ ℚ).injective_int, },
  have hsp : splits (algebra_map ℚ ℂ) (minpoly ℚ x) :=
    is_alg_closed.splits_codomain (minpoly ℚ x),
  have hcd :  multiset.card (map (algebra_map ℚ ℂ) (minpoly ℚ x)).roots = (minpoly ℚ x).nat_degree,
  { exact (nat_degree_eq_card_roots hsp).symm, },
  by_cases hi : i ≤ (minpoly ℤ x).nat_degree,
  { suffices : complex.abs ((map (algebra_map ℚ ℂ) (minpoly ℚ x)).coeff i) ≤
          (minpoly ℤ x).nat_degree.choose i,
    -- TODO: still don't like this proof
    { suffices : (|(minpoly ℤ x).coeff i| : ℝ) ≤ ↑((minpoly ℤ x).nat_degree.choose i),
      { exact_mod_cast this, },
      convert this,
      rw hmp,
      simp only [coeff_map, ring_hom.eq_int_cast, ring_hom.map_int_cast, mem_set_of_eq],
      norm_cast, },
    rw eq_prod_roots_of_splits hsp,
    rw monic.def.mp (minpoly.monic (is_separable.is_integral ℚ x)),
    rw [ring_hom.map_one, map_one, one_mul, multiset.prod_X_sub_C_coeff],
    swap, rwa [hcd, hdg],
    rw ( _ : multiset.card (map (algebra_map ℚ ℂ) (minpoly ℚ x)).roots = (minpoly ℚ x).nat_degree),
    swap, { exact_mod_cast (nat_degree_eq_card_roots hsp).symm },
    rw [complex.abs_mul, (by norm_num : abs ((-1 : ℂ) ^ i) =  1), one_mul],
    apply le_trans (multiset.le_sum_of_subadditive complex.abs _ _ _ ),
    rotate, exact abs_zero, exact abs_add,
    rw multiset.map_map,
    suffices : ∀ (t : multiset ℂ), t ∈ multiset.powerset_len ((minpoly ℚ x).nat_degree - i)
      (map (algebra_map ℚ ℂ) (minpoly ℚ x)).roots → complex.abs t.prod = 1,
    { rw multiset.map_congr (eq.refl _) this,
      rw [multiset.map_const, multiset.sum_repeat, multiset.card_powerset_len,
        nat.smul_one_eq_coe, hcd],
      apply eq.le,
      repeat { rw hdg },
      exact_mod_cast nat.choose_symm hi, },
    intros t ht,
    rw ←complex.abs_hom_apply,
    rw (multiset.prod_hom t complex.abs_hom).symm,
    suffices : ∀ (z : ℂ), z ∈ t → abs_hom z = 1,
    { rw multiset.map_congr (eq.refl _) this,
      simp only [multiset.map_const, multiset.prod_repeat, one_pow], },
    intros z hz,
    suffices : ∃ (φ : K →+* ℂ), φ x = z,
    { obtain ⟨φ, hφ⟩ := this, rw ←hφ, exact hx φ, },
    rw [←set.mem_range, number_field.embeddings.eq_roots, mem_root_set_iff _, aeval_def],
    have : _, from multiset.mem_of_le (multiset.mem_powerset_len.mp ht).left hz,
    rw mem_roots_map at this, { exact_mod_cast this, },
    repeat { rw hmp, refine monic.ne_zero _,
      exact monic.map (algebra_map ℤ ℚ) (minpoly.monic hxi), },
    apply_instance, },
  { push_neg at hi,
    rw [nat.choose_eq_zero_of_lt hi, coeff_eq_zero_of_nat_degree_lt],
    { norm_cast, },
    { exact hi, }}
end
