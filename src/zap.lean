import number_theory.number_field
import analysis.complex.polynomial

open polynomial finite_dimensional complex set

open_locale big_operators

namespace number_field

variables (K : Type*) [field K] [number_field K]

variables (A : Type*) [normed_field A] [is_alg_closed A] [normed_algebra ℚ A]

lemma finite_of_abs_le {B : ℝ} (hB : 1 ≤ B) :
  {x : K | is_integral ℤ x ∧ ∀ φ : K →+* A, ∥ φ x ∥  ≤ B}.finite :=
begin
  classical,
  let S := finset.bUnion
    (finset.product (finset.range (finrank ℚ K + 1)) (finset.range (finrank ℚ K + 1)))
    (λ x, ( { B ^ (x.1 - x.2) * (x.1.choose x.2) } : finset ℝ)),
  let C := nat.ceil (S.max' _),
  swap,
  { exact finset.bUnion_nonempty.mpr
    ⟨⟨0 , 0⟩, finset.mem_product.mpr ⟨finset.mem_range_succ_iff.mpr (zero_le _),
      finset.mem_range_succ_iff.mpr (zero_le _)⟩, finset.singleton_nonempty _⟩, },
  suffices :
    (⋃ (f : polynomial ℤ)
       (hf : f.nat_degree ≤ finrank ℚ K ∧ ∀ i, |f.coeff i| ≤ C),
       ((f.map (algebra_map ℤ K)).roots.to_finset : set K)).finite,
  { refine this.subset _,
    clear this,
    intros x hx,
    have h_map_rat_minpoly := minpoly.gcd_domain_eq_field_fractions' ℚ hx.1,
    have h_same_deg_minpoly : (minpoly ℚ x).nat_degree = (minpoly ℤ x).nat_degree,
    { rw h_map_rat_minpoly, convert nat_degree_map_eq_of_injective _ _,
      exact (algebra_map ℤ ℚ).injective_int, },
    have h_bdd_degree : (minpoly ℚ x).nat_degree ≤ finrank ℚ K,
    { refine le_of_eq_of_le
        (intermediate_field.adjoin.finrank (is_integral_of_is_scalar_tower _ hx.1)).symm _,
      exact ℚ⟮x⟯.to_subalgebra.to_submodule.finrank_le, },
    have h_roots_bdd_minpoly : ∀ z ∈ (map (algebra_map ℚ A) (minpoly ℚ x)).roots, ∥ z ∥  ≤ B,
    { intros z hz,
      suffices : ∃ (φ : K →+* A), φ x = z,
      { obtain ⟨φ, rfl⟩ := this, exact (hx.2 φ), },
      rw [← set.mem_range, embeddings.rat_range_eq_roots, mem_root_set_iff, aeval_def],
      refine (mem_roots_map _).mp hz,
      repeat { exact monic.ne_zero (minpoly.monic (is_integral_of_is_scalar_tower _ hx.1)), }},
    rw mem_Union,
    use minpoly ℤ x,
    rw [mem_Union, exists_prop, finset.mem_coe, multiset.mem_to_finset],
    refine ⟨⟨_, _⟩, _⟩,
    { rw ← h_same_deg_minpoly,
      exact h_bdd_degree, },
    { intro i,
      by_cases hi : i < finrank ℚ K + 1,
      { suffices : B ^ ((minpoly ℚ x).nat_degree - i) * ((minpoly ℚ x).nat_degree.choose i) ≤ C,
        { rw ← @int.cast_le ℝ _ _ _ _,
          apply le_trans _ this,
          convert coeff_le_of_roots_le i _ _ h_roots_bdd_minpoly using 1,
          { simp_rw [h_map_rat_minpoly, coeff_map, norm_algebra_map', eq_int_cast,
              int.norm_cast_rat, int.norm_eq_abs], norm_cast, },
          exacts [minpoly.monic (is_integral_of_is_scalar_tower _ hx.1),
            is_alg_closed.splits_codomain _], },
        { apply le_trans _ (nat.le_ceil (S.max' _)),
          refine finset.le_max' S _ _,
          exact finset.mem_bUnion.mpr ⟨⟨(minpoly ℚ x).nat_degree, i⟩,
            finset.mem_product.mpr
            ⟨finset.mem_range_succ_iff.mpr h_bdd_degree, finset.mem_range.mpr hi⟩,
            finset.mem_singleton.mpr rfl⟩, }},
      { rw [coeff_eq_zero_of_nat_degree_lt, _root_.abs_zero],
        exact nat.cast_nonneg _, linarith, }},
    { rw [mem_roots, is_root.def, ← eval₂_eq_eval_map, ← aeval_def],
      { exact minpoly.aeval ℤ x, },
      { exact monic.ne_zero (monic.map (algebra_map ℤ K) (minpoly.monic hx.1)), }}},
  { refine finite.bUnion _ _,
    suffices : inj_on (λ g : polynomial ℤ, λ d : fin (finrank ℚ K + 1), g.coeff d)
      { f | f.nat_degree ≤ finrank ℚ K ∧ ∀ (i : ℕ), |f.coeff i| ≤ C},
    { refine finite.of_finite_image _ this,
      have hfin : (set.pi univ (λ d : fin (finrank ℚ K + 1), Icc (- C : ℤ) C )).finite
        := finite.pi (λ d, finite_Icc _ _),
      refine finite.subset hfin _,
      rw [pi_univ_Icc, image_subset_iff],
      intros f hf,
      rw [mem_preimage, mem_Icc, pi.le_def, pi.le_def, forall_and_distrib.symm],
      exact λ i, abs_le.mp (hf.right i), },
    { intros x hx y hy hxy,
      ext,
      by_cases n < finrank ℚ K + 1,
      { simpa using congr_fun hxy ⟨n, h⟩, },
      { rw [coeff_eq_zero_of_nat_degree_lt, coeff_eq_zero_of_nat_degree_lt],
        { rcases hy with ⟨ _, _⟩, linarith, },
        { rcases hx with ⟨ _, _⟩, linarith, }}},
    { exact λ p _, polynomial.root_set_finite p K, }},
end

/-- Lemma 1.6 of Washington's Introduction to cyclotomic fields -/
lemma mem_roots_of_unity_of_abs_eq_one {x : K}
  (hxi : is_integral ℤ x)  (hx : ∀ φ : K →+* A, ∥ φ x ∥ = 1) :
  ∃ (n : ℕ) (hn : 0 < n), x ^ n = 1 :=
begin
  obtain ⟨a, -, b, -, habne, h⟩ := @set.infinite.exists_ne_map_eq_of_maps_to _ _ _ _
    ((^) x : ℕ → K) set.infinite_univ _ (finite_of_abs_le K A (le_refl 1)),
  { replace habne := habne.lt_or_lt,
    wlog : a < b := habne using [a b],
    refine ⟨b - a, tsub_pos_of_lt habne, _⟩,
    have hxne : x ≠ 0,
    { contrapose! hx,
      simp only [hx, norm_zero, ring_hom.map_zero, ne.def, not_false_iff, zero_ne_one],
      use (is_alg_closed.lift (number_field.is_algebraic K)).to_ring_hom, },
    { rw [pow_sub₀ _ hxne habne.le, h, mul_inv_cancel (pow_ne_zero b hxne)], }},
  { rw set.maps_univ_to,
    refine λ a, ⟨hxi.pow a, λ φ, by simp [hx φ, complex.abs_pow, one_pow]⟩, },
end

end number_field
