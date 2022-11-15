/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import measure_theory.measure.haar
import analysis.inner_product_space.pi_L2

/-!
# Haar measure constructed from a basis

Given a basis of a finite-dimensional real vector space, we define the corresponding Lebesgue
measure, which gives measure `1` to the parallelogram spanned by the basis.
-/

open set topological_space measure_theory measure_theory.measure finite_dimensional
open_locale big_operators

noncomputable theory

variables {ι E F : Type*} [fintype ι]

section add_comm_group

variables [add_comm_group E] [module ℝ E] [add_comm_group F] [module ℝ F]

/-- The parallelogram spanned by a finite family of vectors. -/
def parallelogram (v : ι → E) : set E :=
(λ (t : ι → ℝ), ∑ i, t i • v i) '' (Icc 0 1)

lemma image_parallelogram (f : E →ₗ[ℝ] F) (v : ι → E) :
  f '' (parallelogram v) = parallelogram (f ∘ v) :=
begin
  simp only [parallelogram, ← image_comp],
  congr' 1,
  ext t,
  simp only [function.comp_app, linear_map.map_sum, linear_map.map_smulₛₗ, ring_hom.id_apply],
end

end add_comm_group

section normed_space

variables [normed_add_comm_group E] [normed_space ℝ E]

/-- The parallelogram spanned by a basis, as a compact set with nonempty interior. -/
def basis.parallelogram_positive_compacts (b : basis ι ℝ E) : positive_compacts E :=
{ carrier := parallelogram b,
  is_compact' := is_compact_Icc.image $ continuous_finset_sum finset.univ
    (λ (i : ι) (H : i ∈ finset.univ), (continuous_apply i).smul continuous_const),
  interior_nonempty' :=
    begin
      suffices H : set.nonempty (interior (b.equiv_funL.symm.to_homeomorph '' (Icc 0 1))),
      { dsimp only [parallelogram],
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

/-- The Lebesgue measure associated to a basis, given measure `1` to the parallelogram spanned
by the basis. -/
@[irreducible] def basis.add_haar (b : basis ι ℝ E) : measure E :=
measure.add_haar_measure b.parallelogram_positive_compacts

instance is_add_haar_measure_basis_add_haar (b : basis ι ℝ E) :
  is_add_haar_measure (b.add_haar) :=
by { rw basis.add_haar, apply measure.is_add_haar_measure_add_haar_measure }

end normed_space

section inner_product_space

variables [inner_product_space ℝ E] [finite_dimensional ℝ E] [measurable_space E] [borel_space E]

instance measure_space_of_inner_product_space : measure_space E :=
{ volume := (std_orthonormal_basis ℝ E).to_basis.add_haar }

end inner_product_space
