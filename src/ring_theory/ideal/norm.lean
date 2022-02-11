/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import data.matrix.notation
import data.zmod.quotient
import linear_algebra.free_module.pid
import ring_theory.dedekind_domain
import ring_theory.norm

/-!
# The ideal norm

This file defines the ideal norm `ideal.norm R I`, where `S` extends the PID `R`, as the
determinant of an isomorphism `S ≃ₗ I`.

-/

universes u v w

section move_me

lemma linear_map.associated_det_of_eq_comp {R M : Type*} [comm_ring R] [is_domain R]
  [add_comm_group M] [module R M] (e : M ≃ₗ[R] M) (f f' : M →ₗ[R] M)
  (h : ∀ x, f x = f' (e x)) : associated f.det f'.det :=
begin
  suffices : associated (f'.comp e.to_linear_map).det f'.det,
  { convert this using 2, ext x, exact h x },
  rw [← mul_one f'.det, linear_map.det_comp],
  exact associated.mul_left _ (associated_one_iff_is_unit.mpr e.is_unit_det')
end

lemma associated_det_comp_equiv {R M N : Type*} [comm_ring R] [is_domain R]
  [add_comm_group M] [module R M] [add_comm_group N] [module R N]
  (f : N →ₗ[R] M) (e e' : M ≃ₗ[R] N) :
  associated (f.comp e.to_linear_map).det (f.comp e'.to_linear_map).det :=
begin
  refine linear_map.associated_det_of_eq_comp (e.trans e'.symm) _ _ _,
  intro x,
  simp only [linear_map.comp_apply, linear_equiv.coe_to_linear_map, linear_equiv.trans_apply,
             linear_equiv.apply_symm_apply],
end

@[simp] lemma normalize_associated_iff
  {R : Type*} [comm_ring R] [is_domain R] [normalization_monoid R] {x y : R} :
  associated (normalize x) y ↔ associated x y :=
⟨λ h, (associated_normalize _).trans h,
 λ h, (normalize_associated _).trans h⟩

@[simp] lemma associated_normalize_iff
  {R : Type*} [comm_ring R] [is_domain R] [normalization_monoid R] {x y : R} :
  associated x (normalize y) ↔ associated x y :=
⟨λ h, h.trans (normalize_associated y),
 λ h, h.trans (associated_normalize y)⟩

@[simp] lemma linear_map.coe_restrict_scalars (R : Type*) {S M M' : Type*}
  [semiring R] [semiring S] [add_comm_monoid M] [add_comm_monoid M']
  [module R M] [module R M'] [module S M] [module S M'] [linear_map.compatible_smul M M' R S]
  (f : M →ₗ[S] M') :
  (f.restrict_scalars R : M → M') = f :=
rfl

@[simp] lemma ideal.coe_restrict_scalars {R S : Type*} [comm_ring R] [comm_ring S] [algebra R S]
  (I : ideal S) : ((I.restrict_scalars R) : set S) = ↑I :=
rfl

/-- The smallest `S`-submodule that contains all `x ∈ I * y ∈ J`
is also the smallest `R`-submodule that does so. -/
@[simp] lemma restrict_scalars_mul {R S : Type*} [comm_ring R] [comm_ring S] [algebra R S]
  (I J : ideal S) : (I * J).restrict_scalars R = I.restrict_scalars R * J.restrict_scalars R :=
begin
  refine le_antisymm (λ x hx, _) (submodule.mul_le.mpr (λ x hx y hy, ideal.mul_mem_mul hx hy)),
  refine submodule.mul_induction_on hx _ _,
  exact (λ x hx y hy, submodule.mul_mem_mul hx hy),
  exact (λ x y, submodule.add_mem _),
end

namespace ideal

variables {R S : Type*} [comm_ring R] [is_domain R] [comm_ring S] [is_domain S] [algebra R S]
variables {ι : Type*} [fintype ι]

/-- A basis on `S` gives a basis on `ideal.span {x}`, by multiplying everything by `x`. -/
noncomputable def basis_span_singleton (b : basis ι R S) {x : S} (hx : x ≠ 0) :
  basis ι R (span ({x} : set S)) :=
b.map $ ((linear_equiv.of_injective (algebra.lmul R S x) (algebra.lmul_injective hx)) ≪≫ₗ
  (linear_equiv.of_eq _ _ (by { ext, simp [mem_span_singleton', mul_comm] })) ≪≫ₗ
  (submodule.restrict_scalars_equiv R S S (ideal.span ({x} : set S))))

@[simp] lemma basis_span_singleton_apply (b : basis ι R S) {x : S} (hx : x ≠ 0) (i : ι) :
  (basis_span_singleton b hx i : S) = x * b i :=
begin
  simp only [basis_span_singleton, basis.map_apply, linear_equiv.trans_apply, subtype.coe_mk,
      restrict_scalars_equiv_apply, linear_equiv.of_injective_apply, algebra.lmul_apply,
      linear_equiv.coe_of_eq_apply]
end

@[simp] lemma constr_basis_span_singleton
  {N : Type*} [semiring N] [module N S] [smul_comm_class R N S]
  (b : basis ι R S) {x : S} (hx : x ≠ 0) :
  b.constr N (coe ∘ basis_span_singleton b hx) = algebra.lmul R S x :=
b.ext (λ i, by rw [basis.constr_basis, function.comp_app, basis_span_singleton_apply,
                   subtype.coe_mk, algebra.lmul_apply])

@[simp] lemma span_zero_singleton : span ({0} : set S) = ⊥ :=
submodule.span_zero_singleton

end ideal

end move_me

namespace ideal

variables {R S : Type*} [comm_ring R] [is_domain R] [comm_ring S] [is_domain S] [algebra R S]
variables {ι : Type*} [fintype ι]

/-- If `I : ideal S` is not `⊥`, it has the same dimension over the PID `R` as `S` itself. -/
noncomputable def basis_of_ne_bot [is_principal_ideal_ring R] (b : basis ι R S)
  (I : ideal S) (hI : I ≠ ⊥) :
  basis ι R I :=
let mc'' := submodule.basis_of_pid b (submodule.restrict_scalars R I),
    c' : basis (fin mc''.1) R I := mc''.2.map
      ((submodule.restrict_scalars_equiv R _ _ I).restrict_scalars _) in
c'.reindex (fintype.equiv_of_card_eq (ideal.rank_eq b hI c'))

variables [normalization_monoid R]

/-- The ideal norm over `R` of an ideal `I : ideal S` is the determinant of an isomorphism `S ≃ₗ I`.

This is uniquely defined up to units in `R`, so we assume `normalization_monoid R`
to choose one of the non-units.

Note that such isomorphisms exist for all nonzero ideals if `S` is finite free over the PID `R`.
See `ideal.norm` for a version that chooses a value in this case.
-/
noncomputable def norm_aux (I : ideal S) (e : S ≃ₗ[R] I) : R :=
normalize $ linear_map.det (((submodule.subtype I).restrict_scalars R) ∘ₗ e.to_linear_map)

@[simp] lemma normalize_norm_aux (I : ideal S) (e : S ≃ₗ[R] I) :
  normalize (norm_aux I e) = norm_aux I e :=
normalize_idem _

/-- `norm_aux` does not depend on the choice of equiv `S ≃ₗ I`, up to units. -/
lemma norm_aux_associated (I : ideal S) (e e' : S ≃ₗ[R] I) :
  associated (norm_aux I e) (linear_map.det ((I.subtype.restrict_scalars R) ∘ₗ e'.to_linear_map)) :=
by { simp only [norm_aux, normalize_associated_iff], apply associated_det_comp_equiv }

/-- `norm_aux` does not depend on the choice of equiv `S ≃ₗ I`, up to units. -/
lemma eq_norm_aux (I : ideal S) (e e' : S ≃ₗ[R] I) :
  normalize (linear_map.det $ (I.subtype.restrict_scalars R).comp e'.to_linear_map) = norm_aux I e :=
begin
  rw ← normalize_norm_aux,
  refine normalize_eq_normalize_iff.mpr ((associated.symm _).dvd_dvd),
  apply norm_aux_associated
end

section

end

/-
lemma norm_aux_mul (I J : ideal S)
  (eI : S ≃ₗ[R] I) (eJ : S ≃ₗ[R] J) (eIJ : S ≃ₗ[R] (I * J : ideal _)) :
  norm_aux (I * J) eIJ = norm_aux I eI * norm_aux J eJ :=
begin
  unfold norm_aux,
  rw [← normalize.map_mul, ← linear_map.det.map_mul, normalize_eq_normalize_iff],
  apply dvd_dvd_of_associated,
  refine linear_map.associated_det_of_eq_comp (linear_equiv.refl _ _) _ _ _,
  intro x,
  simp
end
-/

variables [is_principal_ideal_ring R]

open_locale classical

section

variables (R)

/-- The norm over `R` of an ideal `I` in `S` is the determinant of a basis for `I`.

This requires an `R`-basis on `S`; if there is no such basis the result is always `1`.

We define that the norm of `⊥` is 0.
-/
protected noncomputable def norm (I : ideal S) : R :=
if hI : I = ⊥ then 0
else if hS : ∃ (s : set S) (b : basis s R S), s.finite
     then norm_aux I (hS.some_spec.some.equiv
       (@ideal.basis_of_ne_bot _ _ _ _ _ _ _ _
         hS.some_spec.some_spec.fintype _ hS.some_spec.some _ hI)
       (equiv.refl _))
     else 1

end

@[simp] lemma norm_bot : ideal.norm R (⊥ : ideal S) = 0 := dif_pos rfl

@[simp] lemma normalize_det_equiv {n : Type*} [fintype n]
  (b : basis n R S) (I : ideal S) (hI : I ≠ ⊥)
  (e : S ≃ₗ[R] I := b.equiv (I.basis_of_ne_bot b hI) (equiv.refl _)) :
  normalize ((I.subtype.restrict_scalars R).comp e.to_linear_map).det = I.norm R :=
begin
  unfold ideal.norm,
  rw dif_neg hI,
  have hS : ∃ (s : set S) (b : basis s R S), s.finite,
  { exact ⟨_, b.reindex_range, set.finite_range b⟩ },
  letI : fintype hS.some := hS.some_spec.some_spec.fintype,
  rw dif_pos hS,
  apply eq_norm_aux
end

open submodule

-- TODO: make this `simp` when we have a typeclass like `module.finite_free R S`
/-- The ideal norm agrees with the algebra norm on ideals generated by one element. -/
lemma norm_span_singleton (b : basis ι R S) (x : S) :
  ideal.norm R (span ({x} : set S)) = normalize (algebra.norm R x) :=
begin
  by_cases hx : x = 0,
  { simp [hx, algebra.norm_zero_of_basis b] },
  have : span {x} ≠ ⊥ := mt ideal.span_singleton_eq_bot.mp hx,
  rw [algebra.norm_apply,
      ← normalize_det_equiv b (span {x}) this (b.equiv (basis_span_singleton b hx) (equiv.refl _))],
  congr,
  refine b.ext (λ i, _),
  simp
end

@[simp] lemma span_singleton_one' : span ({1} : set S) = ⊤ :=
span_singleton_one

@[simp] lemma norm_top : ideal.norm R (⊤ : ideal S) = 1 :=
begin
  by_cases hS : ∃ (s : set S) (b : basis s R S), s.finite,
  swap, { exact (dif_neg top_ne_bot).trans (dif_neg hS) },
  letI : fintype hS.some := hS.some_spec.some_spec.some,
  rw [← span_singleton_one', norm_span_singleton hS.some_spec.some, monoid_hom.map_one,
      normalize.map_one]
end

lemma algebra_map_norm_mem (b : basis ι R S) (I : ideal S) :
  algebra_map R S (I.norm R) ∈ I :=
sorry -- TODO: via Lagrange's theorem?

lemma is_unit_norm_iff (b : basis ι R S) (x : S) :
  is_unit (ideal.norm R (span ({x} : set S))) ↔ is_unit x :=
iff.trans
  ⟨λ h, ideal.eq_top_of_is_unit_mem _ (algebra_map_norm_mem b _) ((algebra_map R S).is_unit_map h),
   λ h, have is_unit (1 : R) := is_unit_one, by rwa [h, ideal.norm_top]⟩
  span_singleton_eq_top

end ideal

@[simp] lemma is_unit_normalize [normalization_monoid S] {x : S} :
  is_unit (normalize x) ↔ is_unit x :=
by rw [← @normalize_eq_one _ _ _ _ x, ← normalize_eq_one, normalize_idem]

theorem algebra.is_unit_norm_iff [is_principal_ideal_ring R] [normalization_monoid R]
  (b : basis ι R S) (x : S) :
  is_unit (algebra.norm R x) ↔ is_unit x :=
by rw [← @is_unit_normalize _ _ _ (algebra.norm R _), ← ideal.norm_span_singleton b x, ideal.is_unit_norm_iff b]

section int

/-! ### The ideal norm as an integer

When the base ring is `ℤ`, we can show multiplicity by applying the Chinese Remainder Theorem.
-/

/-- Linear independent families are injective, even if you multiply either side. -/
lemma linear_independent.eq_of_smul_apply_eq_smul_apply {M : Type*} [add_comm_group M] [module R M]
  [nontrivial R] {v : ι → M} (li : linear_independent R v) (c d : R) (i j : ι)
  (hc : c ≠ 0) (h : c • v i = d • v j) : i = j :=
begin
  let l : ι →₀ R := finsupp.single i c - finsupp.single j d,
  have h_total : finsupp.total ι M R v l = 0,
  { simp_rw [linear_map.map_sub, finsupp.total_apply],
    simp [h] },
  have h_single_eq : finsupp.single i c = finsupp.single j d,
  { rw linear_independent_iff at li,
    simp [eq_add_of_sub_eq' (li l h_total)] },
  rcases (finsupp.single_eq_single_iff _ _ _ _).mp h_single_eq with ⟨this, _⟩ | ⟨hc, _⟩,
  { exact this },
  { contradiction },
end

section pid

variables [is_principal_ideal_ring R]

/-- If `S` is a finite free extension of a PID `R`, then any nonzero ideal `I` is free
and we can find a basis for `S` and `I` such that the inclusion map is a diagonal matrix. -/
theorem ideal.smith_normal_form (b : basis ι R S) (I : ideal S) (hI : I ≠ ⊥) :
  ∃ (b' : basis ι R S) (a : ι → R) (ab' : basis ι R I),
  ∀ i, (ab' i : S) = a i • b' i :=
begin
  obtain ⟨n, b', ab', g', a', ab_eq⟩ := submodule.exists_smith_normal_form b (I.restrict_scalars R),
  let ab : basis (fin n) R I := ab'.map I.restrict_scalars_equiv,
  have g'_inj : function.injective g',
  { intros i j h,
    refine ab'.linear_independent.eq_of_smul_apply_eq_smul_apply (a' j) (a' i) i j _ _,
    { rintro ha,
      refine ab'.ne_zero j _,
      ext,
      simp [ab_eq, ha] },
    { ext,
      simp [ab_eq, h, ← mul_action.mul_smul, mul_comm] } },
  have g'_bij := (fintype.bijective_iff_injective_and_card g').mpr ⟨g'_inj, ideal.rank_eq b' hI ab⟩,
  let g : fin n ≃ ι := equiv.of_bijective g' g'_bij,
  have g_apply : ∀ i, g i = g' i := λ i, rfl,
  let a : ι → R := a' ∘ g.symm,
  have a_apply : ∀ i, a i = a' (g.symm i) := λ i, rfl,
  use [b', a, ab.reindex g],
  intro i,
  rw [← g.apply_symm_apply i, a_apply, g.symm_apply_apply, basis.reindex_apply, g.symm_apply_apply],
  simp only [ab_eq, ab'.map_apply, I.restrict_scalars_equiv_apply, equiv.of_bijective_apply],
end

noncomputable def ideal.ring_basis (b : basis ι R S) (I : ideal S) (hI : I ≠ ⊥) :
  basis ι R S := (ideal.smith_normal_form b I hI).some

noncomputable def ideal.self_basis (b : basis ι R S) (I : ideal S) (hI : I ≠ ⊥) :
  basis ι R I := (ideal.smith_normal_form b I hI).some_spec.some_spec.some

noncomputable def ideal.smith_coeffs (b : basis ι R S) (I : ideal S) (hI : I ≠ ⊥) :
  ι → R := (ideal.smith_normal_form b I hI).some_spec.some

@[simp]
lemma ideal.self_basis_def (b : basis ι R S) (I : ideal S) (hI : I ≠ ⊥) :
  ∀ i, (ideal.self_basis b I hI i : S) = ideal.smith_coeffs b I hI i • ideal.ring_basis b I hI i :=
(ideal.smith_normal_form b I hI).some_spec.some_spec.some_spec

end pid

-- TODO: why doesn't this work "normally"?
lemma normalize_prod {ι : Type*} (a : ι → ℤ) (s : finset ι) :
  normalize (∏ i in s, a i) = ∏ i in s, normalize (a i) :=
monoid_hom.map_prod (normalize.to_monoid_hom : ℤ →* ℤ) a s

/-- If `P` is a submodule of `M` and `Q` a submodule of `N`,
and `f : M ≃ₗ N` maps `P` to `Q`, then `M.quotient` is equivalent to `N.quotient`. -/
@[simps] def submodule.quotient.equiv {M N : Type*}
  [add_comm_group M] [module R M] [add_comm_group N] [module R N]
  (P : submodule R M) (Q : submodule R N)
  (f : M ≃ₗ[R] N) (hf : P.map ↑f = Q) : P.quotient ≃ₗ[R] Q.quotient :=
{ to_fun := P.mapq Q ↑f (λ x hx, hf ▸ submodule.mem_map_of_mem hx),
  inv_fun := Q.mapq P ↑f.symm (λ x hx, begin
    rw [← hf, submodule.mem_map] at hx,
    obtain ⟨y, hy, rfl⟩ := hx,
    simpa
  end),
  left_inv := λ x, quotient.induction_on' x (by simp),
  right_inv := λ x, quotient.induction_on' x (by simp),
  .. P.mapq Q ↑f (λ x hx, hf ▸ submodule.mem_map_of_mem hx) }

.

-- TODO: make this the main `submodule.quotient.module` instance
instance submodule.quotient.module'
  {M : Type*} [add_comm_group M] [module R M] [module S M] [is_scalar_tower R S M]
  (P : submodule S M) : module R P.quotient :=
module.of_core { smul := λ c x, algebra_map R S c • x,
                 smul_add := λ c x y, smul_add _ _ _,
                 add_smul := λ c c' x, by simp only [ring_hom.map_add, add_smul],
                 mul_smul := λ c c' x, by simp only [ring_hom.map_mul, mul_action.mul_smul],
                 one_smul := λ x, by simp only [ring_hom.map_one, one_smul] }

@[simp] lemma smul_mk {M : Type*} [add_comm_group M] [module R M] [module S M]
  [is_scalar_tower R S M] (P : submodule S M) (c : R) (x : M) :
  (c • submodule.quotient.mk x : P.quotient) = submodule.quotient.mk (c • x) :=
show submodule.quotient.mk (algebra_map R S c • x) = submodule.quotient.mk (c • x),
by rw algebra_map_smul

instance {M : Type*} [add_comm_group M] [module R M] [module S M] [is_scalar_tower R S M]
  (P : submodule S M) : is_scalar_tower R S P.quotient :=
{ smul_assoc := λ x y z, show (x • y) • z = algebra_map R S x • y • z,
                         by rw [← smul_assoc, algebra_map_smul] }

/-- Restricting the scalars of a submodule doesn't change the quotient you get. -/
@[simps] def submodule.restrict_scalars_quotient_equiv {M : Type*}
  [add_comm_group M] [module R M] [module S M] [is_scalar_tower R S M]
  (P : submodule S M) : (P.restrict_scalars R).quotient ≃ₗ[R] P.quotient :=
{ to_fun := quot.map id (λ x y, id),
  inv_fun := quot.map id (λ x y, id),
  left_inv := λ x, quot.induction_on x (λ x', rfl),
  right_inv := λ x, quot.induction_on x (λ x', rfl),
  map_add' := λ x y, quot.induction_on₂ x y (λ x' y', rfl),
  map_smul' := λ c x, quot.induction_on x (λ x',
    by { rw [submodule.quotient.quot_mk_eq_mk, smul_mk, ← algebra_map_smul S c x'],
         exact submodule.quotient.mk_smul _ }) }

@[simps] def submodule_span_quotient_equiv (s : set S) :
  (submodule.span S s).quotient ≃ₗ[S] (ideal.span s).quotient :=
{ to_fun := quot.map id (λ x y, id),
  inv_fun := quot.map id (λ x y, id),
  left_inv := λ x, quot.induction_on x (λ x', rfl),
  right_inv := λ x, quot.induction_on x (λ x', rfl),
  map_add' := λ x y, quot.induction_on₂ x y (λ x' y', rfl),
  map_smul' := λ c x, quot.induction_on x (λ x', rfl) }

lemma basis.mem_submodule_iff {M : Type*} [add_comm_group M] [module R M] {P : submodule R M}
  (b : basis ι R P) {x : M} :
  x ∈ P ↔ ∃ (c : ι → R), x = ∑ i, c i • b i :=
begin
  split,
  { intro hx, use b.equiv_fun ⟨x, hx⟩,
    show P.subtype ⟨x, hx⟩ = ∑ (i : ι), b.equiv_fun ⟨x, hx⟩ i • P.subtype (b i),
    convert congr_arg P.subtype (b.sum_equiv_fun ⟨x, hx⟩).symm,
    simp only [linear_map.map_sum, linear_map.map_smul] },
  { rintros ⟨c, rfl⟩,
    exact P.sum_mem (λ i _, P.smul_mem _ (b i).2) },
end

lemma basis.mem_ideal_iff {I : ideal S} (b : basis ι R I) {x : S} :
  x ∈ I ↔ ∃ (c : ι → R), x = ∑ i, c i • b i :=
(b.map I.restrict_scalars_equiv.symm).mem_submodule_iff

@[simp] lemma basis.repr_sum_self {M : Type*}
  [add_comm_monoid M] [module R M] (b : basis ι R M) (c : ι → R) :
  ⇑(b.repr (∑ i, c i • b i)) = c :=
begin
  ext j,
  simp only [linear_equiv.map_sum, linear_equiv.map_smul, basis.repr_self, finsupp.smul_single,
             smul_eq_mul, mul_one, finset.sum_apply'],
  rw [finset.sum_eq_single j, finsupp.single_eq_same],
  { rintros i - hi, exact finsupp.single_eq_of_ne hi },
  { intros, have := finset.mem_univ j, contradiction }
end

lemma le_comap_single_pi {ι : Type*} [fintype ι] [decidable_eq ι]
  {M : ι → Type*} [∀ i, add_comm_group (M i)] [∀ i, module R (M i)]
  (p : ∀ i, submodule R (M i)) {i} :
  p i ≤ submodule.comap (single i) (submodule.pi set.univ p) :=
begin
  intros x hx,
  rw [submodule.mem_comap, submodule.mem_pi],
  rintros j -,
  by_cases h : j = i,
  { rwa [h, coe_single, pi.single_eq_same] },
  { rw [coe_single, pi.single_eq_of_ne h], exact (p j).zero_mem }
end

/-- Lift a family of maps to the direct sum of quotients. -/
def submodule.pi_quotient_lift {ι : Type*} [fintype ι] [decidable_eq ι]
  {M : ι → Type*} [∀ i, add_comm_group (M i)] [∀ i, module R (M i)]
  {N : Type*} [add_comm_group N] [module R N]
  (p : ∀ i, submodule R (M i)) (q : submodule R N)
  (f : Π i, M i →ₗ[R] N) (hf : ∀ i, p i ≤ q.comap (f i)) :
  (Π i, (p i).quotient) →ₗ[R] q.quotient :=
linear_map.lsum R (λ i, (p i).quotient) R (λ i, (p i).mapq q (f i) (hf i))

@[simp] lemma submodule.pi_quotient_lift_mk {ι : Type*} [fintype ι] [decidable_eq ι]
  {M : ι → Type*} [∀ i, add_comm_group (M i)] [∀ i, module R (M i)]
  {N : Type*} [add_comm_group N] [module R N]
  (p : ∀ i, submodule R (M i)) (q : submodule R N)
  (f : Π i, M i →ₗ[R] N) (hf : ∀ i, p i ≤ q.comap (f i)) (x : Π i, M i) :
  submodule.pi_quotient_lift p q f hf (λ i, submodule.quotient.mk (x i)) =
    submodule.quotient.mk (linear_map.lsum _ _ R f x) :=
by rw [submodule.pi_quotient_lift, linear_map.lsum_apply, linear_map.sum_apply,
       ← submodule.mkq_apply, linear_map.lsum_apply, linear_map.sum_apply, linear_map.map_sum];
   simp only [linear_map.coe_proj, submodule.mapq_apply, submodule.mkq_apply, linear_map.comp_apply]

@[simp] lemma submodule.pi_quotient_lift_single {ι : Type*} [fintype ι] [decidable_eq ι]
  {M : ι → Type*} [∀ i, add_comm_group (M i)] [∀ i, module R (M i)]
  {N : Type*} [add_comm_group N] [module R N]
  (p : ∀ i, submodule R (M i)) (q : submodule R N)
  (f : Π i, M i →ₗ[R] N) (hf : ∀ i, p i ≤ q.comap (f i)) (i) (x : (p i).quotient) :
  submodule.pi_quotient_lift p q f hf (pi.single i x) =
    submodule.mapq _ _ (f i) (hf i) x :=
begin
  simp_rw [submodule.pi_quotient_lift, linear_map.lsum_apply, linear_map.sum_apply,
           linear_map.comp_apply, linear_map.proj_apply],
  rw finset.sum_eq_single i,
  { rw pi.single_eq_same },
  { rintros j - hj, rw [pi.single_eq_of_ne hj, linear_map.map_zero] },
  { intros, have := finset.mem_univ i, contradiction },
end

/-- Lift a family of maps to a quotient of direct sums. -/
def submodule.quotient_pi_lift {ι : Type*} [fintype ι] [decidable_eq ι]
  {M : ι → Type*} [∀ i, add_comm_group (M i)] [∀ i, module R (M i)]
  {N : ι → Type*} [∀ i, add_comm_group (N i)] [∀ i, module R (N i)]
  (p : ∀ i, submodule R (M i))
  (f : Π i, M i →ₗ[R] N i) (hf : ∀ i, p i ≤ ker (f i)) :
  (submodule.pi set.univ p).quotient →ₗ[R] Π i, N i :=
(submodule.pi set.univ p).liftq (linear_map.pi (λ i, (f i).comp (linear_map.proj i)))
  (λ x hx, mem_ker.mpr (by { ext i, simpa using hf i (submodule.mem_pi.mp hx i (set.mem_univ i)) }))

@[simp] lemma submodule.quotient_pi_lift_mk {ι : Type*} [fintype ι] [decidable_eq ι]
  {M : ι → Type*} [∀ i, add_comm_group (M i)] [∀ i, module R (M i)]
  {N : ι → Type*} [∀ i, add_comm_group (N i)] [∀ i, module R (N i)]
  (p : ∀ i, submodule R (M i))
  (f : Π i, M i →ₗ[R] N i) (hf : ∀ i, p i ≤ ker (f i)) (x : Π i, M i) :
  submodule.quotient_pi_lift p f hf (submodule.quotient.mk x) = λ i, f i (x i) :=
rfl

@[simp] lemma sum_pi_single {ι : Type*} [fintype ι] [decidable_eq ι]
  {M : ι → Type*} [∀ i, add_comm_monoid (M i)] (x : Π i, M i) :
  ∑ i, pi.single i (x i) = x :=
funext (λ j, begin
  rw [finset.sum_apply, finset.sum_eq_single j],
  { simp },
  { rintros i - hi, exact pi.single_eq_of_ne hi.symm _ },
  { simp }
end)

@[simp] lemma linear_map.lsum_single {ι : Type*} [fintype ι] [decidable_eq ι]
  {M : ι → Type*} [∀ i, add_comm_group (M i)] [∀ i, module R (M i)] :
  linear_map.lsum R M R linear_map.single = linear_map.id :=
linear_map.ext (λ x, by simp)

/-- The quotient of a direct sum is the direct sum of quotients -/
@[simps] def submodule.quotient_pi {ι : Type*} [fintype ι] [decidable_eq ι]
  {M : ι → Type*} [∀ i, add_comm_group (M i)] [∀ i, module R (M i)]
  (p : ∀ i, submodule R (M i)) :
  (submodule.pi set.univ p).quotient ≃ₗ[R] Π i, (p i).quotient :=
{ to_fun := submodule.quotient_pi_lift p (λ i, (p i).mkq) (λ i, by simp),
  inv_fun := submodule.pi_quotient_lift p (submodule.pi set.univ p)
    linear_map.single (λ i, le_comap_single_pi p),
  left_inv := λ x, quotient.induction_on' x (λ x',
    by simp_rw [submodule.quotient.mk'_eq_mk, submodule.quotient_pi_lift_mk, submodule.mkq_apply,
                submodule.pi_quotient_lift_mk, linear_map.lsum_single, linear_map.id_apply]),
  right_inv := begin
    rw [function.right_inverse_iff_comp, ← linear_map.coe_comp, ← @linear_map.id_coe R],
    refine congr_arg _ (linear_map.pi_ext (λ i x, quotient.induction_on' x (λ x', funext $ λ j, _))),
    rw [linear_map.comp_apply, submodule.pi_quotient_lift_single, submodule.quotient.mk'_eq_mk,
        submodule.mapq_apply, submodule.quotient_pi_lift_mk, linear_map.id_apply],
    sorry -- Why doesn't Lean see that this is the same?!
  end,
  .. submodule.quotient_pi_lift p (λ i, (p i).mkq) (λ i, by simp) }

.

variables {M : Type*} [add_comm_group M] [module R M]

namespace submodule

section

open_locale classical

/-- The norm of a submodule `S`, defined as the cardinality of `S.quotient`,
if `S.quotient` is finite, and `0` otherwise. -/
noncomputable def card_norm (S : submodule R M) : ℕ :=
if h : nonempty (fintype S.quotient) then @fintype.card S.quotient h.some else 0

@[simp] lemma card_norm_apply (S : submodule R M) [h : fintype S.quotient] :
  card_norm S = fintype.card S.quotient :=
by convert dif_pos (nonempty.intro h) -- `convert` deals with the different `fintype` instances

instance [infinite M] : infinite (⊥ : submodule R M).quotient :=
infinite.of_injective submodule.quotient.mk $ λ x y h, sub_eq_zero.mp $ (quotient.eq ⊥).mp h

@[simp] lemma card_norm_bot [infinite M] : card_norm (⊥ : submodule R M) = 0 :=
dif_neg (by simp; apply_instance)

instance : unique (⊤ : submodule R M).quotient :=
{ default := 0,
  uniq := λ x, quotient.induction_on' x $ λ x, (quotient.eq ⊤).mpr mem_top }

variables (R)

/-- Any two modules that are subsingletons are isomorphic. -/
@[simps] def _root_.linear_equiv.of_subsingleton {N : Type*} [add_comm_monoid N] [module R N]
  [subsingleton M] [subsingleton N] : M ≃ₗ[R] N :=
{ to_fun := λ _, 0,
  inv_fun := λ _, 0,
  left_inv := λ x, subsingleton.elim _ _,
  right_inv := λ x, subsingleton.elim _ _,
  .. (0 : M →ₗ[R] N)}

variables {R}

instance quotient_top.fintype : fintype (⊤ : submodule R M).quotient :=
fintype.of_equiv punit $ equiv_of_subsingleton_of_subsingleton 0 0

@[simp] lemma card_norm_top : card_norm (⊤ : submodule R M) = 1 :=
calc card_norm ⊤ = fintype.card (submodule.quotient ⊤) : card_norm_apply _
... = fintype.card punit : fintype.card_eq.mpr ⟨equiv_of_subsingleton_of_subsingleton 0 0⟩
... = 1 : fintype.card_punit

.

noncomputable instance [fintype M] (S : submodule R M) [decidable_pred (∈ S)] :
  fintype S.quotient :=
quotient.fintype _

/-- A (non-canonical) bijection between a module `M` and the product `(M / S) × S` -/
noncomputable def module_equiv_quotient_times_submodule (S : submodule R M) :
  M ≃ quotient S × S :=
calc M ≃ Σ L : quotient S, {x : M // quotient.mk x = L} :
  (equiv.sigma_preimage_equiv S.mkq).symm
    ... ≃ Σ L : quotient S, {x : M // x - quotient.out' L ∈ S} :
  equiv.sigma_congr_right (λ L, (equiv.refl M).subtype_equiv (λ x,
    by { conv_lhs { rw ← quotient.out_eq' L },
      rw [submodule.quotient.mk'_eq_mk, submodule.quotient.eq, equiv.refl_apply] }))
    ... ≃ Σ L : quotient S, S :
  equiv.sigma_congr_right (λ L,
    ⟨λ x, ⟨x.1 - quotient.out' L, x.2⟩,
     λ x, ⟨x.1 + quotient.out' L, by simp⟩,
     λ ⟨x, hx⟩, subtype.eq $ by simp,
     λ ⟨g, hg⟩, subtype.eq $ by simp⟩)
    ... ≃ quotient S × S :
  equiv.sigma_equiv_prod _ _

lemma submodule.card_eq_card_quotient_mul_card [fintype M] (S : submodule R M) [decidable_pred (∈ S)]  :
  fintype.card M = fintype.card S * fintype.card S.quotient :=
by { rw [mul_comm, ← fintype.card_prod],
     exact fintype.card_congr (module_equiv_quotient_times_submodule S) }

/-- `[S : T] [M : S] = [M : T]` -/
lemma card_quotient_mul_card_quotient (S T : submodule R M) (hST : T ≤ S)
  [fintype S.quotient] [fintype T.quotient] :
  fintype.card (S.map T.mkq) * fintype.card S.quotient = fintype.card T.quotient :=
by rw [submodule.card_eq_card_quotient_mul_card (map T.mkq S),
       fintype.card_eq.mpr ⟨(quotient_quotient_equiv_quotient T S hST).to_equiv⟩]

end

end submodule

open submodule

/-- We can write the quotient of an ideal over a PID as a product of quotients by principal ideals. -/
noncomputable def ideal.quotient_equiv_pi_span [is_principal_ideal_ring R] [decidable_eq ι]
  (I : ideal S) (b : basis ι R S) (hI : I ≠ ⊥) :
  I.quotient ≃ₗ[R] Π i, (ideal.span ({I.smith_coeffs b hI i} : set R)).quotient :=
begin
  -- Choose `e : S ≃ₗ I` and a basis `b'` for `S` that turns the map
  -- `f := ((submodule.subtype I).restrict_scalars R).comp e` into a diagonal matrix:
  -- there is an `a : ι → ℤ` such that `f (b' i) = a i • b' i`.
  let a := I.smith_coeffs b hI,
  let b' := I.ring_basis b hI,
  let ab := I.self_basis b hI,
  have ab_eq := I.self_basis_def b hI,
  let e : S ≃ₗ[R] I := b'.equiv ab (equiv.refl _),
  let f : S →ₗ[R] S := (I.subtype.restrict_scalars R).comp e,
  let f_apply : ∀ x, f x = b'.equiv ab (equiv.refl _) x := λ x, rfl,
  have ha : ∀ i, f (b' i) = a i • b' i,
  { intro i, rw [f_apply, b'.equiv_apply, equiv.refl_apply, ab_eq] },
  have mem_I_iff : ∀ x, x ∈ I ↔ ∀ i, a i ∣ b'.repr x i,
  { intro x, simp_rw [ab.mem_ideal_iff, ab_eq],
    have : ∀ (c : ι → R) i, b'.repr (∑ (j : ι), c j • a j • b' j) i = a i * c i,
    { intros c i,
      simp only [← mul_action.mul_smul, b'.repr_sum_self, mul_comm] },
    split,
    { rintro ⟨c, rfl⟩ i, exact ⟨c i, this c i⟩ },
    { rintros ha,
      choose c hc using ha, exact ⟨c, b'.ext_elem (λ i, trans (hc i) (this c i).symm)⟩ } },

  -- Now we map everything through the linear equiv `S ≃ₗ (ι → R)`,
  -- which maps `I` to `I' := Π i, a i ℤ`.
  let I' : submodule R (ι → R) := submodule.pi set.univ (λ i, ideal.span ({a i} : set R)),
  have : submodule.map ↑b'.equiv_fun (I.restrict_scalars R) = I',
  { ext x,
    simp only [submodule.mem_map, submodule.mem_pi, ideal.mem_span_singleton, set.mem_univ,
               submodule.restrict_scalars_mem, mem_I_iff, smul_eq_mul, forall_true_left,
               linear_equiv.coe_coe, basis.equiv_fun_apply],
    split,
    { rintros ⟨y, hy, rfl⟩ i, exact hy i },
    { rintros hdvd,
      refine ⟨∑ i, x i • b' i, λ i, _, _⟩; rwa b'.repr_sum_self,
      { exact hdvd i } } },
  exact I.restrict_scalars_quotient_equiv.symm.trans
    ((submodule.quotient.equiv (I.restrict_scalars R) I' b'.equiv_fun this).trans
    (submodule.quotient_pi _))
end

-- TODO: do we want to strengthen the equiv (e.g. ring equiv?)
/-- Ideal quotients over a free finite extension of `ℤ` are isomorphic to a direct product of `zmod`. -/
noncomputable def ideal.quotient_equiv_pi_zmod [decidable_eq ι]
  (I : ideal S) (b : basis ι ℤ S) (hI : I ≠ ⊥) :
  I.quotient ≃ Π i, (zmod (I.smith_coeffs b hI i).nat_abs) :=
begin
  let a := I.smith_coeffs b hI,
  let e := I.quotient_equiv_pi_span b hI,
  let e' : (Π (i : ι), (ideal.span ({a i} : set ℤ)).quotient) ≃ Π (i : ι), zmod (a i).nat_abs :=
    equiv.Pi_congr (equiv.refl _) (λ i, (int.quotient_span_equiv_zmod (a i)).to_equiv),
  refine (_ : I.quotient ≃ₗ[ℤ] _).to_equiv.trans e',
  -- TODO: probably from the `module _ I.quotient` instance assuming `is_scalar_tower`
  haveI : unique (module ℤ I.quotient) := add_comm_group.int_module.unique,
  convert e
end

/-- A nonzero ideal over a free finite extension of `ℤ` has a finite quotient. -/
noncomputable def ideal.fintype_quotient_of_free_of_ne_bot [decidable_eq ι]
  (I : ideal S) (b : basis ι ℤ S) (hI : I ≠ ⊥) :
  fintype I.quotient :=
begin
  let a := I.smith_coeffs b hI,
  let e := I.quotient_equiv_pi_zmod b hI,
  haveI : ∀ i, fact (0 < (a i).nat_abs) := sorry,
  exact fintype.of_equiv (Π i, zmod (a i).nat_abs) e.symm,
end

.

#print ideal.quotient

variables [infinite S] -- TODO: should be provable from [integral_domain S] and `basis ι ℤ S`

local attribute [reducible] ideal.quotient

-- TODO: can we generalize this to other PIDs than ℤ?
theorem ideal.card_norm_eq_norm (b : basis ι ℤ S) (I : ideal S) :
  ideal.norm ℤ I = card_norm I :=
begin
  -- If `I` is the zero ideal, both sides are defined to equal 0.
  by_cases hI : I = ⊥,
  { rw [hI, ideal.norm_bot, card_norm_bot, int.coe_nat_zero] },

  -- Otherwise, `I.quotient` is isomorphic to a product of `zmod`s, so it is a fintype.
  letI := classical.dec_eq ι,
  let a := I.smith_coeffs b hI,
  let b' := I.ring_basis b hI,
  let ab := I.self_basis b hI,
  have ab_eq := I.self_basis_def b hI,
  let e : S ≃ₗ[ℤ] I := b'.equiv ab (equiv.refl _),
  let f : S →ₗ[ℤ] S := (I.subtype.restrict_scalars ℤ).comp e,
  let f_apply : ∀ x, f x = b'.equiv ab (equiv.refl _) x := λ x, rfl,
  have ha : ∀ i, f (b' i) = a i • b' i,
  { intro i, rw [f_apply, b'.equiv_apply, equiv.refl_apply, ab_eq] },
  have mem_I_iff : ∀ x, x ∈ I ↔ ∀ i, a i ∣ b'.repr x i,
  { intro x, simp_rw [ab.mem_ideal_iff, ab_eq],
    have : ∀ (c : ι → ℤ) i, b'.repr (∑ (j : ι), c j • a j • b' j) i = a i * c i,
    { intros c i,
      simp only [← mul_action.mul_smul, b'.repr_sum_self, mul_comm] },
    split,
    { rintro ⟨c, rfl⟩ i, exact ⟨c i, this c i⟩ },
    { rintros ha,
      choose c hc using ha, exact ⟨c, b'.ext_elem (λ i, trans (hc i) (this c i).symm)⟩ } },
  letI := ideal.fintype_quotient_of_free_of_ne_bot I b hI,

  -- Note that `ideal.norm ℤ I = det f` is equal to `∏ i, a i`,
  letI := classical.dec_eq ι,
  calc ideal.norm ℤ I
      = normalize (linear_map.det f) : (I.normalize_det_equiv b' hI e).symm
  ... = normalize (linear_map.to_matrix b' b' f).det : by rw det_to_matrix
  ... = normalize (matrix.diagonal a).det : _
  ... = normalize (∏ i, a i) : by rw det_diagonal
  ... = ∏ i, normalize (a i) : normalize_prod a finset.univ
  ... = fintype.card I.quotient : _
  ... = card_norm I : by rw card_norm_apply I,
  -- since `linear_map.to_matrix b' b' f` is the diagonal matrix with `a` along the diagonal.
  { congr, ext i j,
    rw [to_matrix_apply, ha, linear_equiv.map_smul, basis.repr_self, finsupp.smul_single,
        smul_eq_mul, mul_one],
    by_cases h : i = j,
    { rw [h, diagonal_apply_eq, finsupp.single_eq_same] },
    { rw [diagonal_apply_ne h, finsupp.single_eq_of_ne (ne.symm h)] } },

  -- Now we map everything through the linear equiv `S ≃ₗ (ι → ℤ)`,
  -- which maps `I.quotient` to `Π i, zmod (a i).nat_abs`.
  haveI : ∀ i, fact (0 < (a i).nat_abs) := sorry,
  simp_rw [fintype.card_eq.mpr ⟨ideal.quotient_equiv_pi_zmod I b hI⟩, fintype.card_pi, zmod.card],
  sorry -- TODO: `normalize = (↑) ∘ nat_abs`
end

.

/-- Chinese remainder theorem, specialized to two ideals. -/
def ideal.quotient_mul_equiv_quotient_prod (I J : ideal S) (coprime : I ⊔ J = ⊤) :
  (I * J).quotient ≃+* I.quotient × J.quotient :=
let f : fin 2 → ideal S := ![I, J] in
have hf : ∀ (i j : fin 2), i ≠ j → f i ⊔ f j = ⊤,
{ intros i j h, fin_cases i; fin_cases j; sorry },
sorry

/-- Multiplicity of the ideal norm, for coprime ideals.

This is essentially just a repackaging of the Chinese Remainder Theorem.
-/
lemma card_norm_mul_of_coprime (b : basis ι ℤ S) (I J : ideal S) (coprime : I ⊔ J = ⊤) :
  card_norm (I * J) = card_norm I * card_norm J :=
begin
  by_cases hI : I = ⊥,
  { rw [hI, submodule.bot_mul, card_norm_bot, zero_mul] },
  by_cases hJ : J = ⊥,
  { rw [hJ, submodule.mul_bot, card_norm_bot, mul_zero] },
  have hIJ : I * J ≠ ⊥ := mt ideal.mul_eq_bot.mp (not_or hI hJ),

  letI := classical.dec_eq ι,
  letI := I.fintype_quotient_of_free_of_ne_bot b hI,
  letI := J.fintype_quotient_of_free_of_ne_bot b hJ,
  letI := (I * J).fintype_quotient_of_free_of_ne_bot b hIJ,

  rw [card_norm_apply, card_norm_apply, card_norm_apply,
      fintype.card_eq.mpr ⟨(ideal.quotient_mul_equiv_quotient_prod I J coprime).to_equiv⟩,
      fintype.card_prod]
end

variables [is_dedekind_domain S]

lemma unique_factorization_monoid.pow_eq_pow_iff {M : Type*}
  [comm_cancel_monoid_with_zero M] [unique_factorization_monoid M]
  {a : M} (ha0 : a ≠ 0) (ha1 : ¬ is_unit a) {i j : ℕ} : a ^ i = a ^ j ↔ i = j :=
begin
  letI := classical.dec_eq M,
  split,
  { intros hij,
    letI : nontrivial M := ⟨⟨a, 0, ha0⟩⟩,
    letI : normalization_monoid M := unique_factorization_monoid.normalization_monoid,
    obtain ⟨p', hp', dvd'⟩ := wf_dvd_monoid.exists_irreducible_factor ha1 ha0,
    obtain ⟨p, mem, _⟩ := unique_factorization_monoid.exists_mem_factors_of_dvd ha0 hp' dvd',
    have := congr_arg (λ x, multiset.count p (unique_factorization_monoid.factors x)) hij,
    simp only [unique_factorization_monoid.factors_pow, multiset.count_nsmul] at this,
    exact mul_right_cancel' (multiset.count_ne_zero.mpr mem) this },
  { rintros rfl, refl }
end

lemma ideal.pow_succ_lt_pow {P : ideal S} [P_prime : P.is_prime] (hP : P ≠ ⊥) (i : ℕ) :
  P ^ (i + 1) < P ^ i :=
lt_of_le_of_ne (ideal.pow_le_pow (nat.le_succ _))
  (mt (unique_factorization_monoid.pow_eq_pow_iff hP
    (mt ideal.is_unit_iff.mp P_prime.ne_top)).mp
    i.succ_ne_self)

lemma ideal.mem_span_singleton_sup {x y : S} {I : ideal S} :
  x ∈ ideal.span {y} ⊔ I ↔ ∃ (a : S) (b ∈ I), y * a + b = x :=
begin
  rw mem_sup,
  split,
  { rintro ⟨ya, hya, b, hb, rfl⟩,
    obtain ⟨a, ha, rfl⟩ := ideal.mem_span_singleton.mp hya,
    exact ⟨a, b, hb, rfl⟩ },
  { rintro ⟨a, b, hb, rfl⟩,
    exact ⟨y * a, ideal.mem_span_singleton.mpr (dvd_mul_right _ _), b, hb, rfl⟩ }
end

open unique_factorization_monoid

lemma multiset.nsmul_singleton {α : Type*} (n : ℕ) (x : α) :
  n • (x ::ₘ 0) = multiset.repeat x n :=
begin
  refine multiset.eq_repeat.mpr ⟨by simp, λ y hy, _⟩,
  cases n with n,
  { simpa using hy },
  { exact multiset.mem_singleton.mp ((multiset.mem_nsmul n.succ_ne_zero).mp hy) }
end

lemma multiset.lt_repeat_succ {α : Type*} {m : multiset α} {x : α} {n : ℕ} :
  m < multiset.repeat x (n + 1) ↔ m ≤ multiset.repeat x n :=
begin
  rw multiset.lt_iff_cons_le,
  split,
  { rintros ⟨x', hx'⟩,
    have := multiset.eq_of_mem_repeat (multiset.mem_of_le hx' (multiset.mem_cons_self _ _)),
    rwa [this, multiset.repeat_succ, multiset.cons_le_cons_iff] at hx' },
  { intro h,
    rw multiset.repeat_succ,
    exact ⟨x, multiset.cons_le_cons _ h⟩ }
end

lemma dvd_of_factor {α : Type*} [nontrivial α] [decidable_eq α]
  [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [normalization_monoid α]
  {x y : α} (hx : x ∈ factors y) : x ∣ y :=
have hy : y ≠ 0 := λ hy, by simpa [hy] using hx,
dvd_trans (multiset.dvd_prod hx) (dvd_of_associated (factors_prod hy))

lemma exists_mem_factors {α : Type*} [nontrivial α] [decidable_eq α]
  [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [normalization_monoid α]
  {x : α} (hx : x ≠ 0) (h : ¬ is_unit x) : ∃ p, p ∈ factors x :=
begin
  obtain ⟨p', hp', hp'x⟩ := wf_dvd_monoid.exists_irreducible_factor h hx,
  obtain ⟨p, hp, hpx⟩ := exists_mem_factors_of_dvd hx hp' hp'x,
  exact ⟨p, hp⟩
end

@[simp] lemma factors_pos {α : Type*} [nontrivial α] [decidable_eq α]
  [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [normalization_monoid α]
  (x : α) (hx : x ≠ 0) : 0 < factors x ↔ ¬ is_unit x :=
begin
  split,
  { intros h hx,
    obtain ⟨p, hp⟩ := multiset.exists_mem_of_ne_zero h.ne',
    exact (prime_of_factor _ hp).not_unit (is_unit_of_dvd_unit (dvd_of_factor hp) hx) },
  { intros h,
    obtain ⟨p, hp⟩ := exists_mem_factors hx h,
    exact bot_lt_iff_ne_bot.mpr (mt multiset.eq_zero_iff_forall_not_mem.mp
      (not_forall.mpr ⟨p, not_not.mpr hp⟩)) },
end

lemma dvd_not_unit_iff_factors_lt_factors {α : Type*} [nontrivial α] [decidable_eq α]
  [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [normalization_monoid α]
  {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) : dvd_not_unit x y ↔ factors x < factors y :=
begin
  split,
  { rintro ⟨_, c, hc, rfl⟩,
    simp [hx, right_ne_zero_of_mul hy, hc] },
  { intro h,
    exact dvd_not_unit_of_dvd_of_not_dvd ((dvd_iff_factors_le_factors hx hy).mpr h.le)
            (mt (dvd_iff_factors_le_factors hy hx).mp h.not_le) }
end


lemma ideal.eq_prime_pow_of_succ_lt_of_le
  {P I : ideal S} [P_prime : P.is_prime] (hP : P ≠ ⊥) {i : ℕ}
  (hlt : P ^ (i + 1) < I) (hle : I ≤ P ^ i) : I = P ^ i :=
begin
  refine le_antisymm hle _,
  letI := classical.dec_eq (ideal S),
  letI : normalization_monoid (ideal S) := unique_factorization_monoid.normalization_monoid,
  have irr_P : irreducible P := sorry,
  have : I ≠ ⊥ := (lt_of_le_of_lt bot_le hlt).ne',
  have := pow_ne_zero i hP,
  have := pow_ne_zero (i + 1) hP,
  rw [← ideal.dvd_not_unit_iff_lt, dvd_not_unit_iff_factors_lt_factors, factors_pow,
      factors_irreducible irr_P, multiset.nsmul_singleton, multiset.lt_repeat_succ] at hlt,
  rw [← ideal.dvd_iff_le, dvd_iff_factors_le_factors, factors_pow, factors_irreducible irr_P,
      multiset.nsmul_singleton],
  all_goals { assumption }
end

/-- If `a ∈ P^i \ P^(i+1) c ∈ P^i`, then `a * d + e = c` for `e ∈ P^(i+1)`.
`ideal.mul_add_mem_pow_succ_unique` shows the choice of `d` is unique, up to `P`.

Inspired by [Neukirch], proposition 6.1 -/
lemma ideal.exists_mul_add_mem_pow_succ
  (P : ideal S) [P_prime : P.is_prime] (hP : P ≠ ⊥) {i : ℕ}
  (a c : S) (a_mem : a ∈ P ^ i) (a_not_mem : a ∉ P ^ (i + 1)) (c_mem : c ∈ P ^ i) :
  ∃ (d : S) (e ∈ P ^ (i + 1)), a * d + e = c :=
begin
  suffices eq_b : P ^ i = ideal.span {a} ⊔ P ^ (i + 1),
  { exact ideal.mem_span_singleton_sup.mp (eq_b ▸ c_mem) },
  refine (ideal.eq_prime_pow_of_succ_lt_of_le hP
    (lt_of_le_of_ne le_sup_right _)
    (sup_le (ideal.span_le.mpr (set.singleton_subset_iff.mpr a_mem))
      (ideal.pow_succ_lt_pow hP i).le)).symm,
  contrapose! a_not_mem with this,
  rw this,
  exact mem_sup.mpr ⟨a, mem_span_singleton_self a, 0, by simp, by simp⟩
end

lemma ideal.span_singleton_le_iff_mem {a : S} {I : ideal S} :
  ideal.span {a} ≤ I ↔ a ∈ I :=
submodule.span_singleton_le_iff_mem _ _

lemma prime_pow_succ_dvd_mul {α : Type*} [comm_cancel_monoid_with_zero α]
  [unique_factorization_monoid α]
  {p x y : α} (h : prime p) {i : ℕ} (hxy : p ^ (i + 1) ∣ x * y) :
  p ^ (i + 1) ∣ x ∨ p ∣ y :=
begin
  rw or_iff_not_imp_right,
  intro hy,
  induction i with i ih generalizing x,
  { simp only [zero_add, pow_one] at *,
    exact (h.div_or_div hxy).resolve_right hy },
  rw pow_succ at hxy ⊢,
  obtain ⟨x', rfl⟩ := (h.div_or_div (dvd_of_mul_right_dvd hxy)).resolve_right hy,
  rw mul_assoc at hxy,
  exact mul_dvd_mul_left p (ih ((mul_dvd_mul_iff_left h.ne_zero).mp hxy)),
end

lemma ideal.prime (P : ideal S) [P.is_prime] : prime P :=
sorry

lemma ideal.mem_prime_of_mul_mem_pow
  {P : ideal S} [P_prime : P.is_prime] (hP : P ≠ ⊥) {i : ℕ}
  {a b : S} (a_mem : a ∈ P ^ i) (a_not_mem : a ∉ P ^ (i + 1))
  (ab_mem : a * b ∈ P ^ (i + 1)) : b ∈ P :=
begin
  simp only [← ideal.span_singleton_le_iff_mem, ← ideal.dvd_iff_le, pow_succ,
       ← ideal.span_singleton_mul_span_singleton] at a_mem a_not_mem ab_mem ⊢,
  exact (prime_pow_succ_dvd_mul P.prime ab_mem).resolve_left a_not_mem
end

/-- The choice of `d` in `ideal.exists_mul_add_mem_pow_succ` is unique, up to `P`.

Inspired by [Neukirch], proposition 6.1 -/
lemma ideal.mul_add_mem_pow_succ_unique
  (P : ideal S) [P_prime : P.is_prime] (hP : P ≠ ⊥) {i : ℕ}
  (a d d' e e' : S) (a_mem : a ∈ P ^ i) (a_not_mem : a ∉ P ^ (i + 1))
  (e_mem : e ∈ P ^ (i + 1)) (e'_mem : e' ∈ P ^ (i + 1))
  (h : (a * d + e) - (a * d' + e') ∈ P ^ (i + 1)) : d - d' ∈ P :=
begin
  have : e' - e ∈ P ^ (i + 1) := ideal.sub_mem _ e'_mem e_mem,
  have h' : a * (d - d') ∈ P ^ (i + 1),
  { convert ideal.add_mem _ h (ideal.sub_mem _ e'_mem e_mem),
    ring },
  exact ideal.mem_prime_of_mul_mem_pow hP a_mem a_not_mem h'
end

/-- If the `d` from `ideal.exists_mul_add_mem_pow_succ` is unique, up to `P`,
then so are the `c`s, up to `P ^ (i + 1)`.

Inspired by [Neukirch], proposition 6.1 -/
lemma ideal.mul_add_mem_pow_succ_inj
  (P : ideal S) [P_prime : P.is_prime] (hP : P ≠ ⊥) {i : ℕ}
  (a d d' e e' : S) (a_mem : a ∈ P ^ i) (a_not_mem : a ∉ P ^ (i + 1))
  (e_mem : e ∈ P ^ (i + 1)) (e'_mem : e' ∈ P ^ (i + 1))
  (h : d - d' ∈ P) : (a * d + e) - (a * d' + e') ∈ P ^ (i + 1) :=
begin
  have : a * d - a * d' ∈ P ^ (i + 1),
  { convert ideal.mul_mem_mul a_mem h; simp [mul_sub, pow_succ, mul_comm] },
  convert ideal.add_mem _ this (ideal.sub_mem _ e_mem e'_mem),
  ring,
end

set_option pp.proofs true

/-- Multiplicity of the ideal norm, for powers of prime ideals. -/
lemma card_norm_pow_of_prime (b : basis ι ℤ S)
  (P : ideal S) [P_prime : P.is_prime] (hP : P ≠ ⊥) {i : ℕ} :
  card_norm (P ^ i) = card_norm P ^ i :=
begin
  letI := classical.dec_eq ι,
  induction i with i ih,
  { simp },
letI := ideal.fintype_quotient_of_free_of_ne_bot (P ^ i.succ) b (pow_ne_zero _ hP),
  letI := ideal.fintype_quotient_of_free_of_ne_bot (P ^ i) b (pow_ne_zero _ hP),
  letI := ideal.fintype_quotient_of_free_of_ne_bot P b hP,
  have : P ^ (i + 1) < P ^ i := ideal.pow_succ_lt_pow hP i,
  suffices hquot : map (P ^ i.succ).mkq (P ^ i) ≃ quotient P,
  { rw [pow_succ (card_norm P), ← ih, card_norm_apply (P ^ i.succ),
      ← card_quotient_mul_card_quotient (P ^ i) (P ^ i.succ) this.le,
      card_norm_apply (P ^ i), card_norm_apply P],
    congr' 1,
    rw fintype.card_eq,
    exact ⟨hquot⟩ },
  choose a a_mem a_not_mem using set_like.exists_of_lt this,
  -- TODO: can we do this with less repetition?
  refine equiv.of_bijective (λ c', quotient.mk' _) ⟨_, _⟩,
  { cases c' with c' hc',
    choose c hc eq_c' using submodule.mem_map.mp hc',
    exact (ideal.exists_mul_add_mem_pow_succ P hP a c a_mem a_not_mem hc).some },
  { intros c₁' c₂' h,
    cases c₁' with c₁' hc₁',
    cases c₂' with c₂' hc₂',
    rw subtype.mk_eq_mk,
    replace h := (submodule.quotient.eq _).mp h,
    simp only [mkq_apply, ideal.quotient.mk_eq_mk, mem_map] at h,
    obtain ⟨hc₁, eq_c₁'⟩ := classical.some_spec (submodule.mem_map.mp hc₁'),
    obtain ⟨hc₂, eq_c₂'⟩ := classical.some_spec (submodule.mem_map.mp hc₂'),
    intro h,
    rw [← eq_c₁', ← eq_c₂', mkq_apply, mkq_apply, submodule.quotient.eq],
    obtain ⟨he₁, hd₁⟩ := (ideal.exists_mul_add_mem_pow_succ P hP a _ a_mem a_not_mem hc₁).some_spec.some_spec,
    obtain ⟨he₂, hd₂⟩ := (ideal.exists_mul_add_mem_pow_succ P hP a _ a_mem a_not_mem hc₂).some_spec.some_spec,
    rw [← hd₁, ← hd₂],
    exact ideal.mul_add_mem_pow_succ_inj P hP a _ _ _ _ a_mem a_not_mem he₁ he₂ h },
  { intros d',
    refine quotient.induction_on' d' (λ d, _),
    have hc' := ideal.mul_mem_right d _ a_mem,
    have hd' := mem_map.mpr ⟨a * d, hc', rfl⟩,
    refine ⟨⟨_, hd'⟩, _⟩,
    simp only [mkq_apply, quotient.mk'_eq_mk, submodule.quotient.eq],
    obtain ⟨he, hd'⟩ := (ideal.exists_mul_add_mem_pow_succ P hP a _ a_mem a_not_mem hc').some_spec.some_spec,
    refine ideal.mul_add_mem_pow_succ_unique P hP a _ _ 0 _ a_mem a_not_mem _ he _,
    { exact (P ^ (i + 1)).zero_mem },
    convert submodule.neg_mem _ (ideal.add_mem _ he he), -- Come on, Lean!
    rw add_zero,
    conv_lhs { congr, skip, congr, rw ← hd' },
    rw [eq_neg_iff_add_eq_zero, add_assoc, ← sub_sub, sub_add_cancel],
    convert sub_self _,  -- Come on, Lean!!
    sorry }
end

/-- If `P` holds units and powers of primes,
and `P x ∧ P y` for coprime `x, y` implies `P (x * y)`,
then `P` holds on a product of prime powers. -/
@[elab_as_eliminator]
theorem unique_factorization_monoid.induction_on_prime_power {α : Type*}
  [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α]
  {P : α → Prop} (s : finset α) (i : α → ℕ)
  (is_prime : ∀ p ∈ s, prime p) (is_coprime : ∀ p q ∈ s, p ∣ q → p = q)
  (h1 : ∀ {x}, is_unit x → P x) (hpr : ∀ {p} (i : ℕ), prime p → P (p ^ i))
  (hcp : ∀ {x y}, (∀ p, p ∣ x → p ∣ y → is_unit p) → P x → P y → P (x * y)) :
  P (∏ p in s, p ^ (i p)) :=
begin
  letI := classical.dec_eq α,
  induction s using finset.induction_on with p f' hpf' ih,
  { simpa using h1 is_unit_one },
  rw finset.prod_insert hpf',
  have hp := is_prime _ (finset.mem_insert_self _ _),
  refine hcp _ (hpr (i p) hp) (ih (λ q hq, is_prime _ (finset.mem_insert_of_mem hq))
    (λ q q' hq hq', is_coprime _ _ (finset.mem_insert_of_mem hq) (finset.mem_insert_of_mem hq'))),
  refine λ _, no_factors_of_no_prime_factors (pow_ne_zero _ hp.ne_zero) _,
  intros d hdp hdprod hd,
  apply hpf',
  replace hdp := hd.dvd_of_dvd_pow hdp,
  obtain ⟨q, q_mem', hdq⟩ := exists_mem_multiset_dvd_of_prime hd hdprod,
  obtain ⟨q, q_mem, rfl⟩ := multiset.mem_map.mp q_mem',
  replace hdq := hd.dvd_of_dvd_pow hdq,
  have : p ∣ q := dvd_trans
    (dvd_symm_of_irreducible (irreducible_of_prime hd) (irreducible_of_prime hp) hdp)
    hdq,
  convert q_mem,
  exact is_coprime _ _ (finset.mem_insert_self p f') (finset.mem_insert_of_mem q_mem) this,
end

/-- If `P` holds for `0`, units and powers of primes,
and `P x ∧ P y` for coprime `x, y` implies `P (x * y)`,
then `P` holds on all `a : α`. -/
@[elab_as_eliminator]
theorem unique_factorization_monoid.induction_on_coprime {α : Type*}
  [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α]
  {P : α → Prop} (a : α) (h0 : P 0) (h1 : ∀ {x}, is_unit x → P x)
  (hpr : ∀ {p} (i : ℕ), prime p → P (p ^ i))
  (hcp : ∀ {x y}, (∀ p, p ∣ x → p ∣ y → is_unit p) → P x → P y → P (x * y)) :
  P a :=
begin
  letI := classical.dec_eq α,
  have P_of_associated : ∀ {x y}, associated x y → P x → P y,
  { rintros x y ⟨u, rfl⟩ hx,
    exact hcp (λ p _ hpx, is_unit_of_dvd_unit hpx u.is_unit) hx (h1 u.is_unit) },
  by_cases ha0 : a = 0, { rwa ha0 },
  haveI : nontrivial α := ⟨⟨_, _, ha0⟩⟩,
  letI : normalization_monoid α := unique_factorization_monoid.normalization_monoid,
  refine P_of_associated (factors_prod ha0) _,
  rw [← (factors a).map_id, finset.prod_multiset_map_count],
  refine unique_factorization_monoid.induction_on_prime_power _ _ _ _ @h1 @hpr @hcp;
    simp only [multiset.mem_to_finset],
  { apply prime_of_factor },
  rintro p q hp hq hdvd,
  convert normalize_eq_normalize hdvd
    (dvd_symm_of_irreducible
      (irreducible_of_prime (prime_of_factor _ hp))
      (irreducible_of_prime (prime_of_factor _ hq)) hdvd);
    apply (normalize_factor _ _).symm; assumption
end

/-- If `f` maps `p ^ i` to `(f p) ^ i` for primes `p`, and `f`
is multiplicative on coprime elements, then `f` is multiplicative on all products of primes. -/
@[elab_as_eliminator]
theorem unique_factorization_monoid.multiplicative_prime_power {α β : Type*}
  [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [comm_cancel_monoid_with_zero β]
  {f : α → β} (s : finset α) (i j : α → ℕ)
  (is_prime : ∀ p ∈ s, prime p) (is_coprime : ∀ p q ∈ s, p ∣ q → p = q)
  (h1 : ∀ {x y}, is_unit y → f (x * y) = f x * f y)
  (hpr : ∀ {p} (i : ℕ), prime p → f (p ^ i) = (f p) ^ i)
  (hcp : ∀ {x y}, (∀ p, p ∣ x → p ∣ y → is_unit p) → f (x * y) = f x * f y) :
  f (∏ p in s, p ^ (i p + j p)) = f (∏ p in s, p ^ i p) * f (∏ p in s, p ^ j p) :=
begin
  letI := classical.dec_eq α,
  induction s using finset.induction_on with p f' hpf' ih,
  { simpa using h1 is_unit_one },
  simp only [finset.prod_insert hpf'],
  have hp := is_prime _ (finset.mem_insert_self _ _),
  suffices red : ∀ (i' : α → ℕ) (q : α), q ∣ p ^ i' p → q ∣ ∏ q' in f', q' ^ i' q' → is_unit q,
  { rw [hcp (red _), hpr (i p + j p) hp, hcp (red _), hpr (i p) hp, hcp (red _), hpr (j p) hp,
        ih (λ q hq, is_prime _ (finset.mem_insert_of_mem hq))
          (λ q q' hq hq', is_coprime _ _ (finset.mem_insert_of_mem hq) (finset.mem_insert_of_mem hq')),
        pow_add, mul_assoc, mul_left_comm (f p ^ j p), mul_assoc] },
  -- TODO: unify this and the analogous argument for `induction_on_coprime`
  refine λ i' _, no_factors_of_no_prime_factors (pow_ne_zero _ hp.ne_zero) _,
  intros d hdp hdprod hd,
  apply hpf',
  replace hdp := hd.dvd_of_dvd_pow hdp,
  obtain ⟨q, q_mem', hdq⟩ := exists_mem_multiset_dvd_of_prime hd hdprod,
  obtain ⟨q, q_mem, rfl⟩ := multiset.mem_map.mp q_mem',
  replace hdq := hd.dvd_of_dvd_pow hdq,
  have : p ∣ q := dvd_trans
    (dvd_symm_of_irreducible (irreducible_of_prime hd) (irreducible_of_prime hp) hdp)
    hdq,
  convert q_mem,
  exact is_coprime _ _ (finset.mem_insert_self p f') (finset.mem_insert_of_mem q_mem) this,
end

/-- If `f` maps `p ^ i` to `(f p) ^ i` for primes `p`, and `f`
is multiplicative on coprime elements, then `f` is multiplicative everywhere. -/
theorem unique_factorization_monoid.multiplicative_of_coprime {α β : Type*}
  [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [comm_cancel_monoid_with_zero β]
  (f : α → β) (a b : α) (h0 : f 0 = 0) (h1 : ∀ {x y}, is_unit y → f (x * y) = f x * f y)
  (hpr : ∀ {p} (i : ℕ), prime p → f (p ^ i) = (f p) ^ i)
  (hcp : ∀ {x y}, (∀ p, p ∣ x → p ∣ y → is_unit p) → f (x * y) = f x * f y) :
  f (a * b) = f a * f b :=
begin
  by_cases ha0 : a = 0, { rw [ha0, zero_mul, h0, zero_mul] },
  by_cases hb0 : b = 0, { rw [hb0, mul_zero, h0, mul_zero] },
  by_cases hf1 : f 1 = 0,
  { calc f (a * b) = f ((a * b) * 1) : by rw mul_one
               ... = 0 : by simp only [h1 is_unit_one, hf1, mul_zero]
               ... = f a * f (b * 1) : by simp only [h1 is_unit_one, hf1, mul_zero]
               ... = f a * f b : by rw mul_one },
  have h1' : f 1 = 1 := (mul_left_inj' hf1).mp (by rw [← h1 is_unit_one, one_mul, one_mul]),
  letI := classical.dec_eq α,
  haveI : nontrivial α := ⟨⟨_, _, ha0⟩⟩,
  letI : normalization_monoid α := unique_factorization_monoid.normalization_monoid,
  obtain ⟨ua, a_eq⟩ := factors_prod ha0,
  obtain ⟨ub, b_eq⟩ := factors_prod hb0,
  rw [← a_eq, ← b_eq, mul_right_comm _ ↑ua, h1 ua.is_unit, h1 ub.is_unit, h1 ua.is_unit,
      ← mul_assoc, h1 ub.is_unit, mul_right_comm _ (f ua), ← mul_assoc],
  congr,
  rw [← (factors a).map_id, ← (factors b).map_id,
      finset.prod_multiset_map_count, finset.prod_multiset_map_count,
      finset.prod_subset (finset.subset_union_left _ (factors b).to_finset),
      finset.prod_subset (finset.subset_union_right (factors a).to_finset (factors b).to_finset),
      ← finset.prod_mul_distrib],
  simp_rw [id.def, ← pow_add],
  refine unique_factorization_monoid.multiplicative_prime_power _ _ _ _ _ @h1 @hpr @hcp,
  all_goals { simp only [multiset.mem_to_finset, finset.mem_union] },
  { rintros p (hpa | hpb); apply prime_of_factor; assumption },
  { rintro p q (hp | hp) (hq | hq) hdvd;
      rw [← normalize_factor _ hp, ← normalize_factor _ hq];
      exact normalize_eq_normalize hdvd
        (dvd_symm_of_irreducible
          (irreducible_of_prime (prime_of_factor _ hp))
          (irreducible_of_prime (prime_of_factor _ hq)) hdvd) },
  { intros p hpab hpb,
    simp [hpb] },
  { intros p hpab hpa,
    simp [hpa] }
end

/-- Multiplicativity of the ideal norm in number rings. -/
theorem card_norm_mul (b : basis ι ℤ S) (I J : ideal S) :
  card_norm (I * J) = card_norm I * card_norm J :=
unique_factorization_monoid.multiplicative_of_coprime card_norm I J
  card_norm_bot
  (λ I J hI, by simp [ideal.is_unit_iff.mp hI, ideal.mul_top])
  (λ I i hI, have ideal.is_prime I := sorry, by exactI card_norm_pow_of_prime b _ hI.ne_zero)
  (λ I J hIJ, card_norm_mul_of_coprime b I J sorry)

end int
