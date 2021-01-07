import linear_algebra.free_module
import linear_algebra.matrix
import ring_theory.localization
import ring_theory.trace
import algebraic_number_theory.class_number.is_scalar_tower

open_locale big_operators

section norm

section comm_ring

variables {R A : Type*} [comm_ring R] [ring A] [algebra R A]
variables {ι : Type*} [fintype ι] [decidable_eq ι] {b : ι → A} (hb : is_basis R b)

noncomputable def algebra.norm : A →* R :=
{ to_fun := λ x, matrix.det (linear_map.to_matrix hb hb (algebra.lmul R A x)),
  map_one' := by rw [alg_hom.map_one, show (1 : A →ₗ[R] A) = linear_map.id, from rfl,
                     linear_map.to_matrix_id, matrix.det_one],
  map_mul' := λ x y, by rw [alg_hom.map_mul, linear_map.to_matrix_mul, matrix.det_mul]}

end comm_ring

section integral_domain

open_locale matrix

variables {R A : Type*} [integral_domain R] [integral_domain A] [algebra R A]
variables {ι : Type*} [fintype ι] [decidable_eq ι] {b : ι → A} (hb : is_basis R b)

lemma matrix.det_ne_zero_of_left_inverse {R : Type*} [comm_ring R] [nontrivial R]
  {M N : matrix ι ι R} (h : N ⬝ M = 1) :
  M.det ≠ 0 :=
is_unit.ne_zero (matrix.is_unit_det_of_left_inverse _ _ h)

lemma matrix.det_ne_zero_of_right_inverse {R : Type*} [comm_ring R] [nontrivial R]
  {M N : matrix ι ι R} (h : M ⬝ N = 1) :
  M.det ≠ 0 :=
is_unit.ne_zero (matrix.is_unit_det_of_right_inverse _ _ h)

lemma matrix.ker_to_lin_eq_bot_iff {R : Type*} [comm_ring R] [nontrivial R]
  {M : matrix ι ι R} : M.to_lin'.ker = ⊥ ↔ ∀ v, M.mul_vec v = 0 → v = 0 :=
by simp only [submodule.eq_bot_iff, linear_map.mem_ker, matrix.to_lin'_apply]

/-- This holds for all integral domains, not just fields,
but we need to prove it for the field of fractions first. -/
lemma matrix.det_eq_zero_iff_exists_mul_vec_eq_zero_aux {K : Type*} [field K]
  {M : matrix ι ι K} :
  M.det = 0 ↔ ∃ (v ≠ 0), M.mul_vec v = 0 :=
begin
  split,
  { contrapose!,
    intros h,
    have : M.to_lin'.ker = ⊥,
    { simpa only [matrix.ker_to_lin_eq_bot_iff, not_imp_not] using h },
    have : M ⬝ linear_map.to_matrix'
      ((linear_equiv.of_injective_endo M.to_lin' this).symm : (ι → K) →ₗ[K] (ι → K)) = 1,
    { refine matrix.to_lin'.injective _,
      ext1 v,
      rw [matrix.to_lin'_mul, matrix.to_lin'_one, matrix.to_lin'_to_matrix', linear_map.comp_apply],
      exact (linear_equiv.of_injective_endo M.to_lin' this).apply_symm_apply v },
    exact matrix.det_ne_zero_of_right_inverse this },
  { rintros ⟨v, hv, mul_eq⟩,
    contrapose! hv,
    have := congr_arg M⁻¹.mul_vec mul_eq,
    rwa [matrix.mul_vec_mul_vec, matrix.nonsing_inv_mul _ (is_unit.mk0 _ hv), matrix.mul_vec_zero,
         matrix.mul_vec_one] at this }
end

lemma ring_hom.map_dot_product {R S : Type*} [semiring R] [semiring S]
  (f : R →+* S) (v w : ι → R) :
  f (matrix.dot_product v w) = matrix.dot_product (f ∘ v) (f ∘ w) :=
by simp only [matrix.dot_product, f.map_sum, f.map_mul]

lemma ring_hom.map_mul_vec {R S : Type*} [semiring R] [semiring S]
  (f : R →+* S) (M : matrix ι ι R) (v : ι → R) (i : ι) :
  f (M.mul_vec v i) = ((M.map f).mul_vec (f ∘ v) i) :=
by simp only [matrix.mul_vec, matrix.map_apply, ring_hom.map_dot_product]

lemma ring_hom.comp_mul_vec {R S : Type*} [semiring R] [semiring S]
  (f : R →+* S) (M : matrix ι ι R) (v : ι → R) :
  f ∘ (M.mul_vec v) = (M.map f).mul_vec (f ∘ v) :=
by { ext, apply ring_hom.map_mul_vec }

lemma matrix.mul_vec_smul {R S : Type*} [comm_semiring R] [semiring S] [algebra R S]
  (M : matrix ι ι S) (b : R) (v : ι → S)  :
  M.mul_vec (b • v) = b • M.mul_vec v :=
by { ext i, simp only [matrix.mul_vec, matrix.dot_product, finset.smul_sum, pi.smul_apply,
                       algebra.mul_smul_comm] }

lemma matrix.det_eq_zero_iff_exists_mul_vec_eq_zero {M : matrix ι ι R} :
  M.det = 0 ↔ ∃ (v ≠ 0), M.mul_vec v = 0 :=
begin
  have : (M.map (fraction_ring.of R).to_map).det = 0 ↔ _ :=
    matrix.det_eq_zero_iff_exists_mul_vec_eq_zero_aux,
  rw [det_map, (fraction_ring.of R).to_map_eq_zero_iff] at this,
  refine this.trans _; split; rintro ⟨v, hv, mul_eq⟩,
  { haveI := classical.prop_decidable,
    obtain ⟨b, hb⟩ := (fraction_ring.of R).exist_integer_multiples_of_finset (finset.univ.image v),
    have : ∀ i, (fraction_ring.of R).is_integer ((fraction_ring.of R).to_map b * v i),
    { intro i,
      exact hb _ (finset.mem_image.mpr ⟨i, finset.mem_univ _, rfl⟩) },
    refine ⟨λ i, classical.some (this i), _, _⟩,
    { contrapose! hv,
      ext i,
      have hv := congr_fun hv,
      simp only at hv,
      have := classical.some_spec (this i),
      rw [hv, pi.zero_apply, ring_hom.map_zero, eq_comm, mul_eq_zero] at this,
      exact this.resolve_left ((fraction_ring.of R).to_map_ne_zero_of_mem_non_zero_divisors b) },
    { ext i,
      apply (fraction_ring.of R).injective,
      have : (fraction_ring.of R).to_map ∘ (λ i, classical.some (this i)) =
          λ i, (fraction_ring.of R).to_map b * v i :=
        funext (λ i, classical.some_spec (this i)),
      simp only [pi.zero_apply, ring_hom.map_zero, ring_hom.map_mul_vec, this],
      show (M.map (fraction_ring.of R).to_map).mul_vec ((b : R) • v) i = 0,
      rw [matrix.mul_vec_smul],
      exact mul_eq_zero_of_right ((fraction_ring.of R).to_map b) (congr_fun mul_eq i) } },
  { refine ⟨(fraction_ring.of R).to_map ∘ v, _, _⟩,
    { contrapose! hv,
      ext i,
      have hv := congr_fun hv i,
      exact (fraction_ring.of R).to_map_eq_zero_iff.mp hv },
    { ext i,
      simp [← ring_hom.comp_mul_vec, mul_eq], } },
end

lemma linear_map.to_matrix_mul_vec {l : A →ₗ[R] A} (v : ι → R) :
  (linear_map.to_matrix hb hb l).mul_vec v = hb.repr (l (∑ i, v i • b i)) :=
begin
  show matrix.to_lin' (linear_map.to_matrix' (hb.equiv_fun.arrow_congr hb.equiv_fun l)) v = _,
  ext i,
  rw [matrix.to_lin'_to_matrix', linear_equiv.arrow_congr_apply, hb.equiv_fun_apply,
      hb.equiv_fun_symm_apply]
end

section

include hb

lemma algebra.nonempty_basis : nonempty ι :=
begin
  have : hb.repr 1 ≠ 0,
  { refine mt _ (@zero_ne_one A _ _),
    intro h,
    rw [← hb.total_repr (1 : A), h, linear_map.map_zero] },
  have : ∃ i, hb.repr 1 i ≠ 0,
  { contrapose! this,
    exact finsupp.ext this },
  exact nonempty_of_exists this
end

end

lemma algebra.norm_eq_zero_iff {x : A} : algebra.norm hb x = 0 ↔ x = 0 :=
begin
  split,
  { intro h,
    obtain ⟨v, hv, mul_eq⟩ := matrix.det_eq_zero_iff_exists_mul_vec_eq_zero.mp h,
    have : x * ∑ i, (v i • b i) = 0,
    { simp only [linear_map.to_matrix_mul_vec, linear_map.map_sum, algebra.lmul_apply] at mul_eq,
      have : hb.repr (x * ∑ i, v i • b i) = 0,
      { ext j, exact congr_fun mul_eq j },
      rwa hb.repr_eq_zero at this },
    refine (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right (mt _ hv),
    intro h,
    ext i,
    apply linear_independent_iff'.mp hb.1 _ _ h _ (finset.mem_univ i) },
  { rintro rfl,
    simp [algebra.norm, matrix.det_zero (algebra.nonempty_basis hb)] }
end

lemma algebra.norm_ne_zero {x : A} : algebra.norm hb x ≠ 0 ↔ x ≠ 0 :=
not_iff_not.mpr (algebra.norm_eq_zero_iff hb)

end integral_domain

end norm
