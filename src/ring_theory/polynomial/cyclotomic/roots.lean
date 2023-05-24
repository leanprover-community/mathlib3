/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import ring_theory.polynomial.cyclotomic.basic

/-!
# Roots of cyclotomic polynomials.

We gather results about roots of cyclotomic polynomials. In particular we show in
`polynomial.cyclotomic_eq_minpoly` that `cyclotomic n R` is the minimal polynomial of a primitive
root of unity.

## Main results

* `is_primitive_root.is_root_cyclotomic` : Any `n`-th primitive root of unity is a root of
  `cyclotomic n R`.
* `polynomial.is_root_cyclotomic_iff` : if `ne_zero (n : R)`, then `μ` is a root of `cyclotomic n R`
  if and only if `μ` is a primitive root of unity.
* `polynomial.cyclotomic_eq_minpoly` : `cyclotomic n ℤ` is the minimal polynomial of a primitive
  `n`-th root of unity `μ`.
* `polynomial.cyclotomic.irreducible` : `cyclotomic n ℤ` is irreducible.

## Implementation details

To prove `polynomial.cyclotomic.irreducible`, the irreducibility of `cyclotomic n ℤ`, we show in
`polynomial.cyclotomic_eq_minpoly` that `cyclotomic n ℤ` is the minimal polynomial of any `n`-th
primitive root of unity `μ : K`, where `K` is a field of characteristic `0`.
-/

open_locale big_operators

namespace polynomial

variables {R : Type*} [comm_ring R] {n : ℕ}

lemma is_root_of_unity_of_root_cyclotomic {ζ : R} {i : ℕ}
  (hi : i ∈ n.divisors) (h : (cyclotomic i R).is_root ζ) : ζ ^ n = 1 :=
begin
  rcases n.eq_zero_or_pos with rfl | hn,
  { exact pow_zero _ },
  have := congr_arg (eval ζ) (prod_cyclotomic_eq_X_pow_sub_one hn R).symm,
  rw [eval_sub, eval_pow, eval_X, eval_one] at this,
  convert eq_add_of_sub_eq' this,
  convert (add_zero _).symm,
  apply eval_eq_zero_of_dvd_of_eval_eq_zero _ h,
  exact finset.dvd_prod_of_mem _ hi
end

section is_domain

variable [is_domain R]

lemma _root_.is_root_of_unity_iff (h : 0 < n) [is_domain R]
  {ζ : R} : ζ ^ n = 1 ↔ ∃ i ∈ n.divisors, (cyclotomic i R).is_root ζ :=
by rw [←mem_nth_roots h, nth_roots, mem_roots $ X_pow_sub_C_ne_zero h _,
       C_1, ←prod_cyclotomic_eq_X_pow_sub_one h, is_root_prod]; apply_instance

/-- Any `n`-th primitive root of unity is a root of `cyclotomic n R`.-/
lemma _root_.is_primitive_root.is_root_cyclotomic (hpos : 0 < n) {μ : R}
  (h : is_primitive_root μ n) : is_root (cyclotomic n R) μ :=
begin
  rw [← mem_roots (cyclotomic_ne_zero n R),
      cyclotomic_eq_prod_X_sub_primitive_roots h, roots_prod_X_sub_C, ← finset.mem_def],
  rwa [← mem_primitive_roots hpos] at h,
end

private lemma is_root_cyclotomic_iff' {n : ℕ} {K : Type*} [field K] {μ : K} [ne_zero (n : K)] :
  is_root (cyclotomic n K) μ ↔ is_primitive_root μ n :=
begin
  -- in this proof, `o` stands for `order_of μ`
  have hnpos : 0 < n := (ne_zero.of_ne_zero_coe K).out.bot_lt,
  refine ⟨λ hμ, _, is_primitive_root.is_root_cyclotomic hnpos⟩,
  have hμn : μ ^ n = 1,
  { rw is_root_of_unity_iff hnpos,
    exact ⟨n, n.mem_divisors_self hnpos.ne', hμ⟩,
    all_goals { apply_instance } },
  by_contra hnμ,
  have ho : 0 < order_of μ,
  { apply order_of_pos',
    rw is_of_fin_order_iff_pow_eq_one,
    exact ⟨n, hnpos, hμn⟩ },
  have := pow_order_of_eq_one μ,
  rw is_root_of_unity_iff ho at this,
  obtain ⟨i, hio, hiμ⟩ := this,
  replace hio := nat.dvd_of_mem_divisors hio,
  rw is_primitive_root.not_iff at hnμ,
  rw ←order_of_dvd_iff_pow_eq_one at hμn,
  have key  : i < n := (nat.le_of_dvd ho hio).trans_lt ((nat.le_of_dvd hnpos hμn).lt_of_ne hnμ),
  have key' : i ∣ n := hio.trans hμn,
  rw ←polynomial.dvd_iff_is_root at hμ hiμ,
  have hni : {i, n} ⊆ n.divisors,
  { simpa [finset.insert_subset, key'] using hnpos.ne' },
  obtain ⟨k, hk⟩ := hiμ,
  obtain ⟨j, hj⟩ := hμ,
  have := prod_cyclotomic_eq_X_pow_sub_one hnpos K,
  rw [←finset.prod_sdiff hni, finset.prod_pair key.ne, hk, hj] at this,
  have hn := (X_pow_sub_one_separable_iff.mpr $ ne_zero.nat_cast_ne n K).squarefree,
  rw [←this, squarefree] at hn,
  contrapose! hn,
  refine ⟨X - C μ, ⟨(∏ x in n.divisors \ {i, n}, cyclotomic x K) * k * j, by ring⟩, _⟩,
  simp [polynomial.is_unit_iff_degree_eq_zero],
  all_goals { apply_instance }
end

lemma is_root_cyclotomic_iff [ne_zero (n : R)] {μ : R} :
  is_root (cyclotomic n R) μ ↔ is_primitive_root μ n :=
begin
  have hf : function.injective _ := is_fraction_ring.injective R (fraction_ring R),
  haveI : ne_zero (n : fraction_ring R) := ne_zero.nat_of_injective hf,
  rw [←is_root_map_iff hf, ←is_primitive_root.map_iff_of_injective hf, map_cyclotomic,
      ←is_root_cyclotomic_iff']
end

lemma roots_cyclotomic_nodup [ne_zero (n : R)] : (cyclotomic n R).roots.nodup :=
begin
  obtain h | ⟨ζ, hζ⟩ := (cyclotomic n R).roots.empty_or_exists_mem,
  { exact h.symm ▸ multiset.nodup_zero },
  rw [mem_roots $ cyclotomic_ne_zero n R, is_root_cyclotomic_iff] at hζ,
  refine multiset.nodup_of_le (roots.le_of_dvd (X_pow_sub_C_ne_zero
    (ne_zero.pos_of_ne_zero_coe R) 1) $ cyclotomic.dvd_X_pow_sub_one n R) hζ.nth_roots_nodup,
end

lemma cyclotomic.roots_to_finset_eq_primitive_roots [ne_zero (n : R)] :
    (⟨(cyclotomic n R).roots, roots_cyclotomic_nodup⟩ : finset _) = primitive_roots n R :=
by { ext, simp [cyclotomic_ne_zero n R, is_root_cyclotomic_iff,
                mem_primitive_roots, ne_zero.pos_of_ne_zero_coe R] }

lemma cyclotomic.roots_eq_primitive_roots_val [ne_zero (n : R)] :
  (cyclotomic n R).roots = (primitive_roots n R).val :=
by rw ←cyclotomic.roots_to_finset_eq_primitive_roots

/-- If `R` is of characteristic zero, then `ζ` is a root of `cyclotomic n R` if and only if it is a
primitive `n`-th root of unity. -/
lemma is_root_cyclotomic_iff_char_zero {n : ℕ} {R : Type*} [comm_ring R] [is_domain R]
  [char_zero R] {μ : R} (hn : 0 < n) :
  (polynomial.cyclotomic n R).is_root μ ↔ is_primitive_root μ n :=
by { letI := ne_zero.of_gt hn, exact is_root_cyclotomic_iff }

end is_domain

/-- Over a ring `R` of characteristic zero, `λ n, cyclotomic n R` is injective. -/
lemma cyclotomic_injective [char_zero R] :
  function.injective (λ n, cyclotomic n R) :=
begin
  intros n m hnm,
  simp only at hnm,
  rcases eq_or_ne n 0 with rfl | hzero,
  { rw [cyclotomic_zero] at hnm,
    replace hnm := congr_arg nat_degree hnm,
    rw [nat_degree_one, nat_degree_cyclotomic] at hnm,
    by_contra,
    exact (nat.totient_pos (zero_lt_iff.2 (ne.symm h))).ne hnm },
  { haveI := ne_zero.mk hzero,
    rw [← map_cyclotomic_int _ R, ← map_cyclotomic_int _ R] at hnm,
    replace hnm := map_injective (int.cast_ring_hom R) int.cast_injective hnm,
    replace hnm := congr_arg (map (int.cast_ring_hom ℂ)) hnm,
    rw [map_cyclotomic_int, map_cyclotomic_int] at hnm,
    have hprim := complex.is_primitive_root_exp _ hzero,
    have hroot := is_root_cyclotomic_iff.2 hprim,
    rw hnm at hroot,
    haveI hmzero : ne_zero m := ⟨λ h, by simpa [h] using hroot⟩,
    rw is_root_cyclotomic_iff at hroot,
    replace hprim := hprim.eq_order_of,
    rwa [← is_primitive_root.eq_order_of hroot] at hprim}
end

/-- The minimal polynomial of a primitive `n`-th root of unity `μ` divides `cyclotomic n ℤ`. -/
lemma _root_.is_primitive_root.minpoly_dvd_cyclotomic {n : ℕ} {K : Type*} [field K] {μ : K}
  (h : is_primitive_root μ n) (hpos : 0 < n) [char_zero K] :
  minpoly ℤ μ ∣ cyclotomic n ℤ :=
begin
  apply minpoly.is_integrally_closed_dvd (h.is_integral hpos),
  simpa [aeval_def, eval₂_eq_eval_map, is_root.def] using h.is_root_cyclotomic hpos
end

section minpoly

open is_primitive_root complex

lemma _root_.is_primitive_root.minpoly_eq_cyclotomic_of_irreducible {K : Type*} [field K]
  {R : Type*} [comm_ring R] [is_domain R] {μ : R} {n : ℕ} [algebra K R] (hμ : is_primitive_root μ n)
  (h : irreducible $ cyclotomic n K) [ne_zero (n : K)] : cyclotomic n K = minpoly K μ :=
begin
  haveI := ne_zero.of_no_zero_smul_divisors K R n,
  refine minpoly.eq_of_irreducible_of_monic h _ (cyclotomic.monic n K),
  rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic, ←is_root.def, is_root_cyclotomic_iff]
end

/-- `cyclotomic n ℤ` is the minimal polynomial of a primitive `n`-th root of unity `μ`. -/
lemma cyclotomic_eq_minpoly {n : ℕ} {K : Type*} [field K] {μ : K}
  (h : is_primitive_root μ n) (hpos : 0 < n) [char_zero K] :
  cyclotomic n ℤ = minpoly ℤ μ :=
begin
  refine eq_of_monic_of_dvd_of_nat_degree_le (minpoly.monic (is_integral h hpos))
    (cyclotomic.monic n ℤ) (h.minpoly_dvd_cyclotomic hpos) _,
  simpa [nat_degree_cyclotomic n ℤ] using totient_le_degree_minpoly h
end

/-- `cyclotomic n ℚ` is the minimal polynomial of a primitive `n`-th root of unity `μ`. -/
lemma cyclotomic_eq_minpoly_rat {n : ℕ} {K : Type*} [field K] {μ : K}
  (h : is_primitive_root μ n) (hpos : 0 < n) [char_zero K] :
  cyclotomic n ℚ = minpoly ℚ μ :=
begin
  rw [← map_cyclotomic_int, cyclotomic_eq_minpoly h hpos],
  exact (minpoly.is_integrally_closed_eq_field_fractions' _ (is_integral h hpos)).symm
end

/-- `cyclotomic n ℤ` is irreducible. -/
lemma cyclotomic.irreducible {n : ℕ} (hpos : 0 < n) : irreducible (cyclotomic n ℤ) :=
begin
  rw [cyclotomic_eq_minpoly (is_primitive_root_exp n hpos.ne') hpos],
  apply minpoly.irreducible,
  exact (is_primitive_root_exp n hpos.ne').is_integral hpos,
end

/-- `cyclotomic n ℚ` is irreducible. -/
lemma cyclotomic.irreducible_rat {n : ℕ} (hpos : 0 < n) : irreducible (cyclotomic n ℚ) :=
begin
  rw [← map_cyclotomic_int],
  exact (is_primitive.irreducible_iff_irreducible_map_fraction_map (cyclotomic.is_primitive n ℤ)).1
    (cyclotomic.irreducible hpos),
end

/-- If `n ≠ m`, then `(cyclotomic n ℚ)` and `(cyclotomic m ℚ)` are coprime. -/
lemma cyclotomic.is_coprime_rat {n m : ℕ} (h : n ≠ m) :
  is_coprime (cyclotomic n ℚ) (cyclotomic m ℚ) :=
begin
  rcases n.eq_zero_or_pos with rfl | hnzero,
  { exact is_coprime_one_left },
  rcases m.eq_zero_or_pos with rfl | hmzero,
  { exact is_coprime_one_right },
  rw (irreducible.coprime_iff_not_dvd $ cyclotomic.irreducible_rat $ hnzero),
  exact (λ hdiv, h $ cyclotomic_injective $ eq_of_monic_of_associated (cyclotomic.monic n ℚ)
    (cyclotomic.monic m ℚ) $ irreducible.associated_of_dvd (cyclotomic.irreducible_rat
    hnzero) (cyclotomic.irreducible_rat hmzero) hdiv),
end

end minpoly

end polynomial
