import algebra.big_operators.finsupp
import linear_algebra.free_module
import ring_theory.dedekind_domain
import algebraic_number_theory.class_number.euclidean_absolute_value
import algebraic_number_theory.class_number.norm

open_locale big_operators

section integral_domain

variables {R K L : Type*} [integral_domain R] [field K] [field L]
variables (f : fraction_map R K)
variables [algebra f.codomain L] [finite_dimensional f.codomain L]
variables [algebra R L] [is_scalar_tower R f.codomain L]

/-- If `b` is an `R`-basis for the integral closure of `L`,
then mapping `b` to `L` gives a `K`-basis for `L`. -/
lemma is_basis_coe {ι : Type*} {b : ι → integral_closure R L}
  (hb : is_basis R b) : is_basis f.codomain ((coe : integral_closure R L → L) ∘ b) :=
begin
  haveI := classical.dec_eq ι,
  haveI := classical.dec_eq K,
  split,
  { rw linear_independent_iff'',
    intros s g hg h i,
    obtain ⟨⟨a, a_ne⟩, ha⟩ := f.exist_integer_multiples_of_finset (s.image g),
    set g' : ι → R := λ i,
        if h : i ∈ s
        then classical.some (ha (g i) (finset.mem_image.mpr ⟨i, h, rfl⟩))
        else 0
      with g'_eq,
    have hg' : ∀ i, f.to_map (g' i) = (a • g i : f.codomain),
    { intros i,
      simp only [g'_eq],
      split_ifs with hi,
      { exact (classical.some_spec (ha (g i) _)) },
      { rw [hg _ hi, smul_zero, ring_hom.map_zero] } },
    suffices : g' i = 0,
    { have := congr_arg f.to_map this,
      rw [hg' i, ring_hom.map_zero, algebra.smul_def, f.algebra_map_eq, mul_eq_zero] at this,
      exact this.resolve_left (f.to_map_ne_zero_of_mem_non_zero_divisors ⟨a, a_ne⟩) },
    apply linear_independent_iff''.mp hb.1 s (λ i, g' i),
    { intros i hi, exact dif_neg hi },
    { rw [← submodule.coe_eq_zero, ← subalgebra.coe_val, alg_hom.map_sum, ← smul_zero a, ← h,
          finset.smul_sum, finset.sum_congr rfl],
      intros i hi,
      simp only [subalgebra.coe_val, submodule.coe_smul, function.comp_app],
      rw [← is_scalar_tower.algebra_map_smul f.codomain (g' i) (b i : L), f.algebra_map_eq,
          hg', smul_assoc] } },
  { rw eq_top_iff,
    intros x _,
    set g : fraction_map (integral_closure R L) L :=
      integral_closure.fraction_map_of_finite_extension L f,
    have : algebra.is_algebraic R L := f.comap_is_algebraic_iff.mpr algebra.is_algebraic_of_finite,
    obtain ⟨y, z, z_ne, ha⟩ := exists_integral_multiple (this x)
      ((ring_hom.injective_iff _).mpr (λ x hx, f.to_map_eq_zero_iff.mp
        ((algebra_map f.codomain L).map_eq_zero.mp $
          (is_scalar_tower.algebra_map_apply _ _ _ _).symm.trans hx))),
    have := hb.mem_span y,
    refine (submodule.smul_mem_iff _ (f.map_ne_zero z_ne)).mp _,
    rw [← f.algebra_map_eq, is_scalar_tower.algebra_map_smul f.codomain z x, ha],
    obtain ⟨t, c, rfl⟩ := mem_span_range_iff_exists_sum.mp this,
    show (integral_closure R L).val (∑ (i : ι) in t, c i • b i) ∈
      submodule.span (localization_map.codomain f) (set.range ((integral_closure R L).val ∘ b)),
    simp only [alg_hom.map_sum, alg_hom.map_smul],
    apply submodule.sum_mem _ _,
    intros i hi,
    rw ← is_scalar_tower.algebra_map_smul f.codomain (c i) ((integral_closure R L).val (b i)),
    exact submodule.smul_mem _ _ (submodule.subset_span ⟨i, rfl⟩) }
end

variables (L f)

lemma integral_closure.exists_is_basis
  [is_separable (localization_map.codomain f) L] [is_principal_ideal_ring R] :
  ∃ (n : ℕ) (b : fin n → (integral_closure R L)), is_basis R b :=
begin
  obtain ⟨s, b, hb, hb_int⟩ := is_dedekind_domain.exists_is_basis_integral L f,
  have le := is_dedekind_domain.integral_closure_le_span hb hb_int
    unique_factorization_monoid.integrally_closed,
  refine submodule.exists_is_basis_of_le_span _ le,
  refine linear_independent.of_scalar_tower _
    (show function.injective (algebra_map R f.codomain), from f.injective),
  exact (@is_basis_dual_basis _ _ _ _ _ _ _ (λ _ _, classical.prop_decidable _) _ hb _).1
end

noncomputable def integral_closure.dim
  [is_separable (localization_map.codomain f) L] [is_principal_ideal_ring R] :
  ℕ :=
classical.some (integral_closure.exists_is_basis L f)

noncomputable def integral_closure.basis
  [is_separable (localization_map.codomain f) L] [is_principal_ideal_ring R] :
  fin (integral_closure.dim L f) → integral_closure R L :=
classical.some (classical.some_spec (integral_closure.exists_is_basis L f))

lemma integral_closure.is_basis
  [is_separable (localization_map.codomain f) L] [is_principal_ideal_ring R] :
  is_basis R (integral_closure.basis L f) :=
classical.some_spec (classical.some_spec (integral_closure.exists_is_basis L f))

lemma is_basis_coe_repr_apply {ι : Type*} [decidable_eq ι] [fintype ι]
  {b : ι → integral_closure R L} (hb : is_basis R b)
  (x : integral_closure R L) (i : ι) :
  (is_basis_coe f hb).repr x i = f.to_map (hb.repr x i) :=
begin
  have : ∀ j, (is_basis_coe f hb).repr (b j) i = f.to_map (hb.repr (b j) i),
  { intro j,
    calc (is_basis_coe f hb).repr ((coe ∘ b) j) i = if j = i then 1 else 0 :
      by { rw (is_basis_coe f hb).repr_self_apply j i, congr }
    ... = f.to_map (if j = i then 1 else 0) :
      by rw [apply_ite f.to_map, ring_hom.map_one, ring_hom.map_zero]
    ... = f.to_map (hb.repr (b j) i) : by { rw hb.repr_self_apply j i, congr } },
  show (is_basis_coe f hb).repr (subalgebra.val _ x) i = f.to_map (hb.repr x i),
  rw ← sum_repr hb x,
  simp only [alg_hom.map_sum, linear_map.map_sum, alg_hom.map_smul, linear_map.map_smul,
             ring_hom.map_sum, ring_hom.map_mul,
             smul_eq_mul, finset.sum_apply', finsupp.smul_apply],
  refine finset.sum_congr rfl (λ j _, _),
  rw [map_smul_eq_smul_map (is_basis_coe f hb).repr (hb.repr x j), finsupp.smul_apply',
      subalgebra.coe_val, this j, algebra.smul_def, f.algebra_map_eq],
end

variables {R K L} (f)

lemma to_matrix_is_basis_coe {ι : Type*} [decidable_eq ι] [fintype ι]
  {b : ι → integral_closure R L} (hb : is_basis R b)
  (l : L →ₗ[f.codomain] L) (l' : integral_closure R L →ₗ[R] integral_closure R L)
  (hl : ∀ x : integral_closure R L, l x = l' x) :
  linear_map.to_matrix (is_basis_coe f hb) (is_basis_coe f hb) l =
    (linear_map.to_matrix hb hb l').map (algebra_map _ _) :=
by { ext i j,
     simp only [matrix.map_apply, linear_map.to_matrix_apply, is_basis.equiv_fun_apply,
                function.comp_app, hl, localization_map.algebra_map_eq, is_basis_coe_repr_apply] }

section is_principal_ideal_ring

variables [is_principal_ideal_ring R] [is_separable f.codomain L] (abs : absolute_value R ℤ)

noncomputable def abs_norm [decidable_eq L] (x : integral_closure R L) : ℤ :=
abs (@algebra.norm R (integral_closure R L) _ _ _ _ _ _ _ (integral_closure.is_basis L f) x)

noncomputable def abs_frac_norm [decidable_eq L] (x : L) : ℚ :=
abs.to_frac f (algebra.norm (is_basis_coe f (integral_closure.is_basis L f)) x)

lemma abs_frac_norm_coe [decidable_eq L] (x : integral_closure R L) :
  abs_frac_norm f abs (x : L) = abs_norm f abs x :=
begin
  unfold abs_frac_norm abs_norm algebra.norm,
  rw [monoid_hom.coe_mk,
      to_matrix_is_basis_coe f (integral_closure.is_basis L f)
        (algebra.lmul (f.codomain) L x) (algebra.lmul R (integral_closure R L) x),
      det_map, monoid_hom.coe_mk],
  { exact abs.to_frac_to_map f _ },
  intro y,
  simp
end

end is_principal_ideal_ring

end integral_domain

section euclidean_domain

variables {R K L : Type*} [euclidean_domain R] [field K] [field L]
variables (f : fraction_map R K)
variables [algebra f.codomain L] [algebra R L] [is_scalar_tower R f.codomain L]
variables [finite_dimensional f.codomain L] [is_separable f.codomain L]

/-- If `L` is a finite dimensional extension of the field of fractions of a Euclidean domain `R`,
there is a function mapping each `x : L` to the "closest" value that is integral over `R`. -/
noncomputable def integral_part (x : L) : integral_closure R L :=
∑ i, f.integral_part ((is_basis_coe f (integral_closure.is_basis L f)).repr x i) • i

end euclidean_domain
