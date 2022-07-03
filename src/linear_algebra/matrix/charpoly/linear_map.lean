/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import linear_algebra.matrix.charpoly.coeff
import linear_algebra.matrix.to_lin

/-!

# Calyley-Hamilton theorem for arbitrary rings and f.g. modules.

-/

variables (ι : Type*) [decidable_eq ι]
variables {M : Type*} [add_comm_group M] {R : Type*} [comm_ring R] [module R M] (I : ideal R)
variables (v : ι → M) (hv : submodule.span R (set.range v) = ⊤)

variables {M' : Type*} [add_comm_monoid M'] [module R M']
variables (v' : ι → M') (hv' : submodule.span R (set.range v') = ⊤)

-- def linear_map.fun_right (f : module.End R M') : (ι → M) →ₗ[R] (ι → M') :=
-- { to_fun := λ x i, f (x i),
--   map_add' := λ x y, funext $ λ i, f.map_add _ _,
--   map_smul' := λ x y, funext $ λ i, f.map_smul _ _ }

variables (M)

open_locale big_operators

noncomputable
def ideal.finsupp_total : (ι →₀ I) →ₗ[R] M :=
(finsupp.total ι M R v).comp (finsupp.map_range.linear_map I.subtype)

variables {ι M v}

@[simp] lemma ideal.finsupp_total_apply (f : ι →₀ I) :
  ideal.finsupp_total ι M I v f = f.sum (λ i x, (x : R) • v i) :=
begin
  dsimp [ideal.finsupp_total],
  rw [finsupp.total_apply, finsupp.sum_map_range_index],
  exact λ _, zero_smul _ _
end

lemma ideal.finsupp_total_apply_eq_of_fintype [fintype ι] (f : ι →₀ I) :
  ideal.finsupp_total ι M I v f = ∑ i, (f i : R) • v i :=
begin
  rw ideal.finsupp_total_apply,
  apply finset.sum_subset (finset.subset_univ _),
  intros x _ hx,
  rw finsupp.not_mem_support_iff.mp hx,
  exact zero_smul _ _
end

lemma ideal.range_finsupp_total :
  (ideal.finsupp_total ι M I v).range = I • (submodule.span R (set.range v)) :=
begin
  apply le_antisymm,
  { rintros x ⟨f, rfl⟩,
    rw ideal.finsupp_total_apply,
    apply sum_mem _, { apply_instance },
    intros c _,
    apply submodule.smul_mem_smul (f c).2,
    apply submodule.subset_span,
    exact set.mem_range_self c },
  { rw submodule.smul_le,
    rintros r hr m hm,
    rw ← set.image_univ at hm,
    obtain ⟨l, hl, rfl⟩ := (finsupp.mem_span_image_iff_total _).mp hm,
    let l' : ι →₀ I := finsupp.map_range (λ x : R, (⟨x * r, I.mul_mem_left _ hr⟩ : I))
      (subtype.ext $ zero_mul _) l,
    use l',
    rw [ideal.finsupp_total_apply, finsupp.total_apply, finsupp.sum, finsupp.sum, finset.smul_sum],
    dsimp,
    simp only [← mul_smul, mul_comm r],
    apply finset.sum_subset,
    { exact finsupp.support_map_range },
    { intros x hx hx',
      have : l x * r = 0 := by injection finsupp.not_mem_support_iff.mp hx',
      rw [this, zero_smul] } }
end

variables (v) [fintype ι]

variables (R M ι)

noncomputable
def fintype.total : (ι → R) →ₗ[R] M :=
(finsupp.total ι M R v).comp (finsupp.linear_equiv_fun_on_fintype R R ι).symm.to_linear_map

variables {M ι v}

lemma fintype.range_total : (fintype.total ι M R v).range = submodule.span R (set.range v) :=
begin
  rw [fintype.total, linear_map.range_comp, linear_equiv.to_linear_map_eq_coe, linear_equiv.range,
    submodule.map_top, finsupp.range_total],
end

lemma fintype.total_apply (f) : fintype.total ι M R v f = ∑ i, f i • v i :=
begin
  apply finset.sum_subset,
  { exact finset.subset_univ _ },
  { intros x _ hx,
    rw finsupp.not_mem_support_iff.mp hx,
    exact zero_smul _ _ }
end

lemma fintype.total_apply_single (i : ι) (r : R) :
  fintype.total ι M R v (pi.single i r) = r • v i :=
begin
  simp_rw [fintype.total_apply, pi.single_apply, ite_smul, zero_smul],
  rw [finset.sum_ite_eq', if_pos (finset.mem_univ _)]
end

variables (v)

/-- Matrices, being endomorphisms of `ι → R`, acts on the projection `(ι → R) →ₗ[R] M` and gives
a new `(ι → R) →ₗ[R] M`.  -/
noncomputable
def pi_to_module.from_matrix : matrix ι ι R →ₗ[R] (ι → R) →ₗ[R] M :=
(linear_map.llcomp R _ _ _ (fintype.total ι M R v)).comp alg_equiv_matrix'.symm.to_linear_map

lemma pi_to_module.from_matrix_apply (A : matrix ι ι R) (w : ι → R) :
  pi_to_module.from_matrix R v A w = fintype.total ι M R v (A.mul_vec w) := rfl

lemma pi_to_module.from_matrix_apply_single_one (A : matrix ι ι R) (i : ι) :
  pi_to_module.from_matrix R v A (pi.single i 1) = ∑ (x : ι), A x i • v x :=
begin
  rw [pi_to_module.from_matrix_apply, fintype.total_apply, matrix.mul_vec_single],
  simp_rw [mul_one]
end

/-- The endomorphisms of `M`, acts on the projection `(ι → R) →ₗ[R] M` and gives a new
`(ι → R) →ₗ[R] M`.  -/
noncomputable
def pi_to_module.from_End : (module.End R M) →ₗ[R] (ι → R) →ₗ[R] M :=
linear_map.lcomp _ _ (fintype.total ι M R v)

lemma pi_to_module.from_End_apply (f : module.End R M) (w : ι → R) :
  pi_to_module.from_End R v f w = f (fintype.total ι M R v w) := rfl

lemma pi_to_module.from_End_apply_single_one (f : module.End R M) (i : ι) :
  pi_to_module.from_End R v f (pi.single i 1) = f (v i) :=
begin
  rw [pi_to_module.from_End_apply, fintype.total_apply_single, one_smul],
end


lemma pi_to_module.from_End_injective (hv : submodule.span R (set.range v) = ⊤) :
  function.injective (pi_to_module.from_End R v) :=
begin
  intros x y e,
  ext m,
  obtain ⟨m, rfl⟩ : m ∈ (fintype.total ι M R v).range,
  { rw (fintype.range_total R).trans hv, trivial },
  exact (linear_map.congr_fun e m : _)
end

variables {R}

/-- We say that a matrix represents an endomorphism of `M` if the matrix acting on `ι → R` is
equal to `f ` via the projection `(ι → R) →ₗ[R] M` given by a fixed (spanning) set.  -/
def matrix_represents (A : matrix ι ι R) (f : module.End R M) : Prop :=
pi_to_module.from_matrix R v A = pi_to_module.from_End R v f

variables {v}

lemma matrix_represents.congr_fun {A : matrix ι ι R} {f : module.End R M}
  (h : matrix_represents v A f) (x) :
  fintype.total ι M R v (A.mul_vec x) = f (fintype.total ι M R v x) :=
linear_map.congr_fun h x

lemma matrix_represents.iff {A : matrix ι ι R} {f : module.End R M} :
  matrix_represents v A f ↔
    ∀ x, fintype.total ι M R v (A.mul_vec x) = f (fintype.total ι M R v x) :=
⟨λ e x, e.congr_fun x, λ H, linear_map.ext $ λ x, H x⟩
.
lemma matrix_represents.iff' {A : matrix ι ι R} {f : module.End R M} :
  matrix_represents v A f ↔ ∀ j, ∑ (i : ι), A i j • v i = f (v j) :=
begin
  split,
  { intros h i,
    have := linear_map.congr_fun h (pi.single i 1),
    rwa [pi_to_module.from_End_apply_single_one,
      pi_to_module.from_matrix_apply_single_one] at this },
  { intros h,
    ext,
    simp_rw [linear_map.comp_apply, linear_map.coe_single, pi_to_module.from_End_apply_single_one,
      pi_to_module.from_matrix_apply_single_one],
    apply h }
end

lemma matrix_represents.mul {A A' : matrix ι ι R} {f f' : module.End R M}
  (h : matrix_represents v A f) (h' : matrix_represents v A' f') :
  matrix_represents v (A * A') (f * f') :=
begin
  delta matrix_represents pi_to_module.from_matrix at ⊢,
  rw [linear_map.comp_apply, alg_equiv.to_linear_map_apply, map_mul],
  ext,
  dsimp [pi_to_module.from_End],
  rw [← h'.congr_fun, ← h.congr_fun],
  refl,
end

lemma matrix_represents.one : matrix_represents v (1 : matrix ι ι R) 1 :=
begin
  delta matrix_represents pi_to_module.from_matrix,
  rw [linear_map.comp_apply, alg_equiv.to_linear_map_apply, map_one],
  ext,
  refl
end

lemma matrix_represents.add {A A' : matrix ι ι R} {f f' : module.End R M}
  (h : matrix_represents v A f) (h' : matrix_represents v A' f') :
  matrix_represents v (A + A') (f + f') :=
begin
  delta matrix_represents at ⊢ h h', rw [map_add, map_add, h, h'],
end

lemma matrix_represents.zero :
  matrix_represents v (0 : matrix ι ι R) 0 :=
begin
  delta matrix_represents, rw [map_zero, map_zero],
end

lemma matrix_represents.smul {A : matrix ι ι R} {f : module.End R M}
  (h : matrix_represents v A f) (r : R) :
  matrix_represents v (r • A) (r • f) :=
begin
  delta matrix_represents at ⊢ h, rw [map_smul, map_smul, h],
end

lemma matrix_represents.eq {A : matrix ι ι R} {f f' : module.End R M}
  (h : matrix_represents v A f) (h' : matrix_represents v A f') : f = f' :=
pi_to_module.from_End_injective R v hv (h.symm.trans h')

variables [decidable_eq ι]

variables (v R)

def matrix_represents_subring : subalgebra R (matrix ι ι R) :=
{ carrier := { A | ∃ f : module.End R M, matrix_represents v A f },
  mul_mem' := λ A₁ A₂ ⟨f₁, e₁⟩ ⟨f₂, e₂⟩, ⟨f₁ * f₂, e₁.mul e₂⟩,
  one_mem' := ⟨1, matrix_represents.one⟩,
  add_mem' := λ A₁ A₂ ⟨f₁, e₁⟩ ⟨f₂, e₂⟩, ⟨f₁ + f₂, e₁.add e₂⟩,
  zero_mem' := ⟨0, matrix_represents.zero⟩,
  algebra_map_mem' := λ r, ⟨r • 1, matrix_represents.one.smul r⟩ }

noncomputable
def matrix_represents_subring.to_End : matrix_represents_subring R v →ₐ[R] module.End R M :=
{ to_fun := λ A, A.2.some,
  map_one' := (1 : matrix_represents_subring R v).2.some_spec.eq hv matrix_represents.one,
  map_mul' := λ A₁ A₂, (A₁ * A₂).2.some_spec.eq hv (A₁.2.some_spec.mul A₂.2.some_spec),
  map_zero' := (0 : matrix_represents_subring R v).2.some_spec.eq hv matrix_represents.zero,
  map_add' := λ A₁ A₂, (A₁ + A₂).2.some_spec.eq hv (A₁.2.some_spec.add A₂.2.some_spec),
  commutes' := λ r, (r • 1 : matrix_represents_subring R v).2.some_spec.eq
    hv (matrix_represents.one.smul r) }

lemma matrix_represents_subring.to_End_represents (A : matrix_represents_subring R v) :
  matrix_represents v (A : matrix ι ι R) (matrix_represents_subring.to_End R v hv A) :=
A.2.some_spec

lemma matrix_represents_subring.eq_to_End_of_represents (A : matrix_represents_subring R v)
  {f : module.End R M} (h : matrix_represents v (A : matrix ι ι R) f) :
    matrix_represents_subring.to_End R v hv A = f :=
A.2.some_spec.eq hv h

lemma matrix_represents_subring.to_End_exists_mem_ideal
  (f : module.End R M) {I : ideal R} (hI : f.range ≤ I • ⊤) :
  ∃ M, matrix_represents_subring.to_End R v hv M = f ∧ ∀ i j, M.1 i j ∈ I :=
begin
  have : ∀ x, f x ∈ (ideal.finsupp_total ι M I v).range,
  { rw [ideal.range_finsupp_total, hv], exact λ x, hI (f.mem_range_self x) },
  choose bM' hbM',
  let A : matrix ι ι R := λ i j, bM' (v j) i,
  have : matrix_represents v A f,
  { rw matrix_represents.iff',
    dsimp [A],
    intro j,
    specialize hbM' (v j),
    rwa ideal.finsupp_total_apply_eq_of_fintype at hbM' },
  exact ⟨⟨A, f, this⟩, matrix_represents_subring.eq_to_End_of_represents R v hv ⟨A, f, this⟩ this,
    λ i j, (bM' (v j) i).prop⟩,
end

lemma exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul [module.finite R M]
  (f : module.End R M) {I : ideal R} (hI : f.range ≤ I • ⊤) :
  ∃ p : polynomial R, p.monic ∧
    (∀ k, p.coeff k ∈ I ^ (p.nat_degree - k)) ∧
      polynomial.aeval f p = 0 :=
begin
  classical,
  cases subsingleton_or_nontrivial R,
  { exactI ⟨0, polynomial.monic_of_subsingleton _, by simp⟩ },
  resetI,
  obtain ⟨s : finset M, hs : submodule.span R (s : set M) = ⊤⟩ := module.finite.out,
  obtain ⟨A, rfl, h⟩ := matrix_represents_subring.to_End_exists_mem_ideal R (coe : s → M)
    (by rw [subtype.range_coe_subtype, finset.set_of_mem, hs]) f hI,
  refine ⟨A.1.charpoly, A.1.charpoly_monic, _, _⟩,
  { rw A.1.charpoly_nat_degree_eq_dim,
    exact coeff_charpoly_mem_ideal_pow h },
  { rw [polynomial.aeval_alg_hom_apply, ← map_zero (matrix_represents_subring.to_End R coe _)],
    congr' 1,
    ext1,
    rw [polynomial.aeval_subalgebra_coe, subtype.val_eq_coe, matrix.aeval_self_charpoly,
      subalgebra.coe_zero] },
  { apply_instance }
end
