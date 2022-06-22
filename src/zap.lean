import number_theory.number_field
import analysis.complex.polynomial

section admit
namespace multiset

variables {R : Type*} [comm_ring R]

def esymm (s : multiset R) (n : ℕ) : R := ((s.powerset_len n).map multiset.prod).sum

lemma prod_X_sub_C_coeff (s : multiset R) {k : ℕ} (h : k ≤ s.card):
    polynomial.coeff (s.map (λ r, polynomial.X - polynomial.C r)).prod k =
    (-1)^k * s.esymm (s.card - k) :=
begin
  sorry,
end

end multiset
end admit

section forward

open_locale nnreal

-- TODO maybe gen to is_R_or_C?
variables {K : Type*} [monoid K] {n : ℕ} (x : K) (hx : x ^ n = 1) (hn : 0 < n)
variables (φ : K →* ℂ)
include hx hn
open complex

-- The clean way to do this is to show that abs of phi is a monoid hom to ℝ≥0, and monoid homs take
-- roots of unity to roots of unity, and that roots of unity ℝ≥0 is trivial
lemma absolute_value_one : abs (φ x) = 1 :=
begin
  have h_pow : (abs (φ x)) ^ n = 1,
  { rw (_ : abs (φ x) ^ n = abs (φ x ^ n)),
    rw (_ : φ x ^ n = φ (x ^ n)),
    simp only [hx, complex.abs_one, monoid_hom.map_one],
    rw monoid_hom.map_pow,
    rw is_absolute_value.abv_pow complex.abs, },
  set t := abs (φ x),
  have : 0 ≤ t, from (φ x).abs_nonneg,
  clear_value t,
  lift t to ℝ≥0 using this,
  norm_cast at *,
  rwa (@pow_eq_one_iff _ _ _ nnreal.covariant_mul _ _ hn.ne') at h_pow,
end

end forward

section backwards

open set finite_dimensional complex
open_locale classical
open_locale big_operators

variables {K : Type*} [field K] [number_field K] {n : ℕ} (x : K)
open polynomial

noncomputable theory

lemma nat_degree_le_finrank {K : Type*} [field K] [number_field K] {x : K} (hx : is_integral ℤ x) :
  (minpoly ℤ x).nat_degree ≤ finrank ℚ K :=
begin
  rw (_ : (minpoly ℤ x).nat_degree = (minpoly ℚ x).nat_degree),
  rw [← intermediate_field.adjoin.finrank (is_separable.is_integral ℚ x),
    ← intermediate_field.finrank_eq_finrank_subalgebra],
  convert submodule.finrank_le (ℚ⟮x⟯.to_subalgebra.to_submodule : submodule _ _),
  have : minpoly ℚ x = (minpoly ℤ x).map (algebra_map ℤ ℚ),
  from minpoly.gcd_domain_eq_field_fractions' ℚ hx,
  rw [this, nat_degree_map_eq_of_injective _],
  exact is_fraction_ring.injective ℤ ℚ,
end

--again the algebra_rat diamond
-- local attribute [-instance] complex.algebra

lemma minpoly_coeff_le_of_all_abs_eq_one (hx : x ∈ {x : K | ∀ (φ : K →+* ℂ), abs (φ x) = 1})
  (hxi : is_integral ℤ x) (i : ℕ) :
  |(minpoly ℤ x).coeff i| ≤ ((minpoly ℤ x).nat_degree.choose i) :=
begin
  by_cases hi : i ≤ (minpoly ℤ x).nat_degree,
  { have h_mins : minpoly ℚ x = (map (algebra_map ℤ ℚ) (minpoly ℤ x)),
    from minpoly.gcd_domain_eq_field_fractions' ℚ hxi,
    have h_degree : (minpoly ℚ x).nat_degree = (minpoly ℤ x).nat_degree,
    { rw ( _ : (minpoly ℤ x).nat_degree = (map (algebra_map ℤ ℚ) (minpoly ℤ x)).nat_degree),
      rwa h_mins,
      have : function.injective (algebra_map ℤ ℚ), { exact (algebra_map ℤ ℚ).injective_int, },
      rw polynomial.nat_degree_map_eq_of_injective this, },
    suffices : abs ((minpoly ℚ x).coeff i : ℂ) ≤ (minpoly ℤ x).nat_degree.choose i,
    { suffices : (|(minpoly ℤ x).coeff i| : ℝ) ≤ ↑((minpoly ℤ x).nat_degree.choose i),
      { exact_mod_cast this, },
      convert this,
      simp only [h_mins, coeff_map, ring_hom.eq_int_cast, rat.cast_coe_int],
      norm_cast, },
    rw (by simp [coeff_map, ring_hom.eq_rat_cast] :
      ((minpoly ℚ x).coeff i : ℂ) = ((minpoly ℚ x).map (algebra_map ℚ ℂ)).coeff i),
    have : splits (algebra_map ℚ ℂ) (minpoly ℚ x),
      from is_alg_closed.splits_codomain (minpoly ℚ x),
    have h_roots : multiset.card (map (algebra_map ℚ ℂ) (minpoly ℚ x)).roots =
      (minpoly ℚ x).nat_degree, { exact (polynomial.nat_degree_eq_card_roots this).symm, },
    rw eq_prod_roots_of_splits this,
    simp only [monic.def.mp (minpoly.monic (is_separable.is_integral ℚ x)),
        one_mul, ring_hom.map_one],

    rw multiset.prod_X_sub_C_coeff,

    swap, rwa [h_roots, h_degree],
    simp only [is_absolute_value.abv_pow complex.abs, complex.abs_mul, complex.abs_neg,
      complex.abs_one, one_pow, one_mul],
    let T := (multiset.powerset_len (multiset.card (map (algebra_map ℚ ℂ) (minpoly ℚ x)).roots - i)
        (map (algebra_map ℚ ℂ) (minpoly ℚ x)).roots),
    suffices : complex.abs (multiset.map multiset.prod T).sum  ≤
      (multiset.map (λ t, (multiset.map complex.abs t).prod) T).sum,
    { apply le_trans this,
      suffices : ∀ t ∈ T, (multiset.map complex.abs t).prod = 1,
      { rw multiset.map_congr (eq.refl T) this,
        have : multiset.card T = ((minpoly ℤ x).nat_degree.choose i),
        { rw ←nat.choose_symm,
          convert multiset.card_powerset_len (multiset.card (map (algebra_map ℚ ℂ)
          (minpoly ℚ x)).roots - i) (map (algebra_map ℚ ℂ) (minpoly ℚ x)).roots,
          { rw h_roots, exact h_degree.symm, },
          { rw h_roots, exact h_degree.symm, },
          exact hi, },
        simp only [this, multiset.map_const, multiset.sum_repeat, nat.smul_one_eq_coe], },
      { intros s hs,
        rw ( _ : (multiset.map complex.abs s) = multiset.repeat 1
          (multiset.card (map (algebra_map ℚ ℂ) (minpoly ℚ x)).roots - i)),
        simp only [multiset.prod_repeat, one_pow],
        suffices hz : ∀ z ∈ s, complex.abs z = 1,
        { rw ( _ : multiset.map complex.abs s = multiset.map (function.const ℂ 1) s),
          { rw multiset.mem_powerset_len at hs,
            simp only [hs.right, multiset.map_const], },
          exact multiset.map_congr (eq.refl s) hz },
        { intros z hz,
          suffices : z ∈ (minpoly ℚ x).root_set ℂ,
          { rw [← number_field.embeddings.eq_roots x] at this,
            rcases set.mem_range.mp this with ⟨φ, hφ⟩,
            rw ←hφ,
            exact (set.mem_set_of.mp hx) φ,
            apply_instance },
          apply multiset.mem_to_finset.mpr,
          refine multiset.mem_of_le _ hz,
          exact (multiset.mem_powerset_len.mp hs).left, }}},
    suffices : complex.abs (multiset.map multiset.prod T).sum ≤
        (multiset.map complex.abs (multiset.map multiset.prod T)).sum,
    { apply le_trans this,
      apply le_of_eq,
      suffices :  ∀ t ∈ T, complex.abs (multiset.prod t) = (multiset.map complex.abs t).prod,
      { simp only [multiset.map_congr (eq.refl T) this, multiset.map_map], },
      intros t ht,
      exact (multiset.prod_hom t complex.abs_hom).symm, },
      refine multiset.le_sum_of_subadditive complex.abs _ _ (multiset.map multiset.prod T),
      exact complex.abs_zero,
      exact (λ a b, complex.abs_add a b), },
  { push_neg at hi,
    rw nat.choose_eq_zero_of_lt hi,
    rw coeff_eq_zero_of_nat_degree_lt,
    norm_cast,
    exact hi, },
end

lemma finite_all_abs_eq_one : {x : K | is_integral ℤ x ∧ ∀ φ : K →+* ℂ, abs (φ x) = 1}.finite :=
begin
  suffices :
    (⋃ (f : polynomial ℤ)
       (hf : f.nat_degree ≤ finrank ℚ K ∧ ∀ i, |f.coeff i| ≤ f.nat_degree.choose i),
       ((f.map (algebra_map ℤ K)).roots.to_finset : set K)).finite,
  { refine this.subset _,
    intros x hx,
    rw mem_Union,
    use minpoly ℤ x,
    simp only [exists_prop, mem_Union, multiset.mem_to_finset, finset.mem_coe],
    refine ⟨⟨_, _⟩, _⟩,
    { exact nat_degree_le_finrank hx.1, },
    { exact minpoly_coeff_le_of_all_abs_eq_one x hx.2 hx.1, },
    rw [mem_roots, is_root.def, ←polynomial.eval₂_eq_eval_map,
      ←aeval_def],
    exact minpoly.aeval ℤ x,
    suffices : (minpoly ℤ x) ≠ 0,
    { contrapose! this,
      simp only [polynomial.ext_iff, coeff_map, coeff_zero] at this ⊢,
      suffices inj : function.injective (algebra_map ℤ K),
      { exact λ n : ℕ, inj (by rw [(this n), (algebra_map ℤ K).map_zero]),},
      exact int.cast_injective, },
      refine minpoly.ne_zero hx.1, },
  refine finite.bUnion _ _,
  { have : inj_on (λ g : polynomial ℤ, λ d : fin (finrank ℚ K + 1), g.coeff d)
      { f | f.nat_degree ≤ finrank ℚ K
            ∧ ∀ (i : ℕ), |f.coeff i| ≤ f.nat_degree.choose i },
    { intros x hx y hy he,
      ext,
      by_cases n < finrank ℚ K + 1,
      { simpa using congr_fun he ⟨n, h⟩, },
      rw [coeff_eq_zero_of_nat_degree_lt, coeff_eq_zero_of_nat_degree_lt],
      { rcases hy with ⟨hy_left, hy_right⟩,
        linarith, },
      { rcases hx with ⟨hx_left, hx_right⟩,
        linarith, }, },
    { refine finite.of_finite_image _ this,
      have : (set.pi univ (λ d : fin (finrank ℚ K + 1), Icc (-(finrank ℚ K).choose d : ℤ)
              ((finrank ℚ K).choose d))).finite := finite.pi (λ d, finite_Icc _ _),
      refine finite.subset this _,
      simp only [pi_univ_Icc, image_subset_iff],
      intros f hf,
      simp only [pi_univ_Icc, mem_preimage, mem_Icc, pi.le_def] at *,
      rw ← forall_and_distrib,
      intro x,
      rw mem_def at hf,
      rcases hf with ⟨hf_left, hf_right⟩,
      specialize hf_right x,
      rw abs_le at hf_right,
      suffices : f.nat_degree.choose x ≤ (finrank ℚ K).choose x,
      { split; linarith, },
      apply nat.choose_mono _ hf_left, }, },
  { intros p hp,
    -- few possibilites here
    exact polynomial.root_set_finite p K, },
end

-- TODO we don't really need K to be a number field here, more general field extensions are fine
-- as long as we keep the condition that x is integral over ℤ
variables (hx : ∀ φ : K →+* ℂ, abs (φ x) = 1) (hxi : is_integral ℤ x)
include hx hxi
/-- Lemma 1.6 of Washington's Introduction to cyclotomic fields -/
lemma mem_roots_of_unity_of_abs_eq_one : ∃ (n : ℕ) (hn : 0 < n), x ^ n = 1 :=
begin
  obtain ⟨a, -, b, -, habne, h⟩ := @infinite.exists_ne_map_eq_of_maps_to _ _ _ _
      ((^) x : ℕ → K) infinite_univ _ (finite_all_abs_eq_one),
  { replace habne := habne.lt_or_lt,
    wlog : a < b := habne using [a b],
    refine ⟨b - a, tsub_pos_of_lt habne, _⟩,
    have hxne : x ≠ 0,
    { contrapose! hx,
      simp only [hx, complex.abs_zero, ring_hom.map_zero, ne.def, not_false_iff, zero_ne_one],
      use (is_alg_closed.lift (number_field.is_algebraic K)).to_ring_hom },
    rw [pow_sub₀ _ hxne habne.le, h, mul_inv_cancel (pow_ne_zero b hxne)] },
  { rw [set.maps_univ_to],
    exact λ a, ⟨hxi.pow a, λ φ, by simp [hx φ, is_absolute_value.abv_pow complex.abs]⟩ },
end
end backwards
