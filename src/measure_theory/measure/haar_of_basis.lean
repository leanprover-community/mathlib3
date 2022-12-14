/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import measure_theory.measure.haar
import analysis.inner_product_space.pi_L2

/-!
# Additive Haar measure constructed from a basis

Given a basis of a finite-dimensional real vector space, we define the corresponding Lebesgue
measure, which gives measure `1` to the parallelepiped spanned by the basis.

## Main definitions

* `parallelepiped v` is the parallelepiped spanned by a finite family of vectors.
* `basis.parallelepiped` is the parallelepiped associated to a basis, seen as a compact set with
nonempty interior.
* `basis.add_haar` is the Lebesgue measure associated to a basis, giving measure `1` to the
corresponding parallelepiped.

In particular, we declare a `measure_space` instance on any finite-dimensional inner product space,
by using the Lebesgue measure associated to some orthonormal basis (which is in fact independent
of the basis).
-/

open set topological_space measure_theory measure_theory.measure finite_dimensional
open_locale big_operators

noncomputable theory

variables {ι ι' E F : Type*} [fintype ι] [fintype ι']

section add_comm_group

variables [add_comm_group E] [module ℝ E] [add_comm_group F] [module ℝ F]

/-- The closed parallelepiped spanned by a finite family of vectors. -/
def parallelepiped (v : ι → E) : set E :=
(λ (t : ι → ℝ), ∑ i, t i • v i) '' (Icc 0 1)

lemma mem_parallelepiped_iff (v : ι → E) (x : E) :
  x ∈ parallelepiped v ↔ ∃ (t : ι → ℝ) (ht : t ∈ Icc (0 : ι → ℝ) 1), x = ∑ i, t i • v i :=
by simp [parallelepiped, eq_comm]

lemma image_parallelepiped (f : E →ₗ[ℝ] F) (v : ι → E) :
  f '' (parallelepiped v) = parallelepiped (f ∘ v) :=
begin
  simp only [parallelepiped, ← image_comp],
  congr' 1 with t,
  simp only [function.comp_app, linear_map.map_sum, linear_map.map_smulₛₗ, ring_hom.id_apply],
end

/-- Reindexing a family of vectors does not change their parallelepiped. -/
@[simp] lemma parallelepiped_comp_equiv (v : ι → E) (e : ι' ≃ ι) :
  parallelepiped (v ∘ e) = parallelepiped v :=
begin
  simp only [parallelepiped],
  let K : (ι' → ℝ) ≃ (ι → ℝ) := equiv.Pi_congr_left' (λ (a : ι'), ℝ) e,
  have : Icc (0 : (ι → ℝ)) 1 = K '' (Icc (0 : (ι' → ℝ)) 1),
  { rw ← equiv.preimage_eq_iff_eq_image,
    ext x,
    simp only [mem_preimage, mem_Icc, pi.le_def, pi.zero_apply, equiv.Pi_congr_left'_apply,
      pi.one_apply],
    refine ⟨λ h, ⟨λ i, _, λ i, _⟩, λ h, ⟨λ i, h.1 (e.symm i), λ i, h.2 (e.symm i)⟩⟩,
    { simpa only [equiv.symm_apply_apply] using h.1 (e i) },
    { simpa only [equiv.symm_apply_apply] using h.2 (e i) } },
  rw [this, ← image_comp],
  congr' 1 with x,
  simpa only [orthonormal_basis.coe_reindex, function.comp_app, equiv.symm_apply_apply,
    equiv.Pi_congr_left'_apply, equiv.apply_symm_apply]
      using (e.symm.sum_comp (λ (i : ι'), x i • v (e i))).symm,
end

/- The parallelepiped associated to an orthonormal basis of `ℝ` is either `[0, 1]` or `[-1, 0]`. -/
lemma parallelepiped_orthonormal_basis_one_dim (b : orthonormal_basis ι ℝ ℝ) :
  parallelepiped b = Icc 0 1 ∨ parallelepiped b = Icc (-1) 0 :=
begin
  have e : ι ≃ fin 1,
  { apply fintype.equiv_fin_of_card_eq,
    simp only [← finrank_eq_card_basis b.to_basis, finrank_self] },
  have B : parallelepiped (b.reindex e) = parallelepiped b,
  { convert parallelepiped_comp_equiv b e.symm,
    ext i,
    simp only [orthonormal_basis.coe_reindex] },
  rw ← B,
  let F : ℝ → (fin 1 → ℝ) := λ t, (λ i, t),
  have A : Icc (0 : fin 1 → ℝ) 1 = F '' (Icc (0 : ℝ) 1),
  { apply subset.antisymm,
    { assume x hx,
      refine ⟨x 0, ⟨hx.1 0, hx.2 0⟩, _⟩,
      ext j,
      simp only [subsingleton.elim j 0] },
    { rintros x ⟨y, hy, rfl⟩,
      exact ⟨λ j, hy.1, λ j, hy.2⟩ } },
  rcases orthonormal_basis_one_dim (b.reindex e) with H|H,
  { left,
    simp only [H, parallelepiped, algebra.id.smul_eq_mul, mul_one, A,
      finset.sum_singleton, ←image_comp, image_id', finset.univ_unique], },
  { right,
    simp only [H, parallelepiped, algebra.id.smul_eq_mul, mul_one],
    rw A,
    simp only [←image_comp, mul_neg, mul_one, finset.sum_singleton, image_neg, preimage_neg_Icc,
      neg_zero, finset.univ_unique] },
end

end add_comm_group

section normed_space

variables [normed_add_comm_group E] [normed_space ℝ E]

/-- The parallelepiped spanned by a basis, as a compact set with nonempty interior. -/
def basis.parallelepiped (b : basis ι ℝ E) : positive_compacts E :=
{ carrier := parallelepiped b,
  is_compact' := is_compact_Icc.image (continuous_finset_sum finset.univ
    (λ (i : ι) (H : i ∈ finset.univ), (continuous_apply i).smul continuous_const)),
  interior_nonempty' :=
    begin
      suffices H : set.nonempty (interior (b.equiv_funL.symm.to_homeomorph '' (Icc 0 1))),
      { dsimp only [parallelepiped],
        convert H,
        ext t,
        exact (b.equiv_fun_symm_apply t).symm },
      have A : set.nonempty (interior (Icc (0 : ι → ℝ) 1)),
      { rw [← pi_univ_Icc, interior_pi_set (@finite_univ ι _)],
        simp only [univ_pi_nonempty_iff, pi.zero_apply, pi.one_apply, interior_Icc, nonempty_Ioo,
          zero_lt_one, implies_true_iff] },
      rwa [← homeomorph.image_interior, nonempty_image_iff],
    end }

variables [measurable_space E] [borel_space E]

/-- The Lebesgue measure associated to a basis, giving measure `1` to the parallelepiped spanned
by the basis. -/
@[irreducible] def basis.add_haar (b : basis ι ℝ E) : measure E :=
measure.add_haar_measure b.parallelepiped

instance is_add_haar_measure_basis_add_haar (b : basis ι ℝ E) :
  is_add_haar_measure b.add_haar :=
by { rw basis.add_haar, exact measure.is_add_haar_measure_add_haar_measure _ }

lemma basis.add_haar_self (b : basis ι ℝ E) : b.add_haar (parallelepiped b) = 1 :=
by { rw [basis.add_haar], exact add_haar_measure_self }

end normed_space

/-- A finite dimensional inner product space has a canonical measure, the Lebesgue measure giving
volume `1` to the parallelepiped spanned by any orthonormal basis. We define the measure using
some arbitrary choice of orthonormal basis. The fact that it works with any orthonormal basis
is proved in `orthonormal_basis.volume_parallelepiped`. -/
@[priority 100] instance measure_space_of_inner_product_space
  [inner_product_space ℝ E] [finite_dimensional ℝ E] [measurable_space E] [borel_space E] :
  measure_space E :=
{ volume := (std_orthonormal_basis ℝ E).to_basis.add_haar }

/- This instance should not be necessary, but Lean has difficulties to find it in product
situations if we do not declare it explicitly. -/
instance real.measure_space : measure_space ℝ := by apply_instance
