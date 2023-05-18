/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Frédéric Dupuis
-/
import algebra.star.module
import topology.algebra.module.basic
import topology.algebra.star

/-!
# The star operation, bundled as a continuous star-linear equiv
-/

/-- If `A` is a topological module over a commutative `R` with compatible actions,
then `star` is a continuous semilinear equivalence. -/
@[simps]
def starL (R : Type*) {A : Type*}
  [comm_semiring R] [star_ring R] [add_comm_monoid A] [star_add_monoid A] [module R A]
  [star_module R A] [topological_space A] [has_continuous_star A] :
    A ≃L⋆[R] A :=
{ to_linear_equiv := star_linear_equiv R,
  continuous_to_fun := continuous_star,
  continuous_inv_fun := continuous_star }

variables (R : Type*) (A : Type*)
  [semiring R] [star_semigroup R] [has_trivial_star R]
  [add_comm_group A] [module R A] [star_add_monoid A] [star_module R A]
  [invertible (2 : R)]
  [topological_space A] [has_continuous_star A]
  [has_continuous_const_smul R A]

lemma continuous_self_adjoint_part [has_continuous_add A] :
  continuous (@self_adjoint_part R A _ _ _ _ _ _ _ _) :=
((continuous_const_smul _).comp $ continuous_id.add continuous_star).subtype_mk _

lemma continuous_skew_adjoint_part [has_continuous_sub A] :
  continuous (@skew_adjoint_part R A _ _ _ _ _ _ _ _) :=
((continuous_const_smul _).comp $ continuous_id.sub continuous_star).subtype_mk _

lemma continuous_decompose_prod_adjoint [topological_add_group A] :
  continuous (@star_module.decompose_prod_adjoint R A _ _ _ _ _ _ _ _) :=
(continuous_self_adjoint_part R A).prod_mk (continuous_skew_adjoint_part R A)

lemma continuous_decompose_prod_adjoint_symm [topological_add_group A] :
  continuous (@star_module.decompose_prod_adjoint R A _ _ _ _ _ _ _ _).symm :=
(continuous_subtype_coe.comp continuous_fst).add (continuous_subtype_coe.comp continuous_snd)

/-- The self-adjoint part of an element of a star module, as a continuous linear map. -/
@[simps] def self_adjoint_partL [has_continuous_add A] : A →L[R] self_adjoint A :=
{ to_linear_map := self_adjoint_part R,
  cont := continuous_self_adjoint_part _ _ }

/-- The skew-adjoint part of an element of a star module, as a continuous linear map. -/
@[simps] def skew_adjoint_partL [has_continuous_sub A] : A →L[R] skew_adjoint A :=
{ to_linear_map := skew_adjoint_part R,
  cont := continuous_skew_adjoint_part _ _ }

/-- The decomposition of elements of a star module into their self- and skew-adjoint parts,
as a continuous linear equivalence. -/
@[simps] def star_module.decompose_prod_adjointL [topological_add_group A] :
  A ≃L[R] self_adjoint A × skew_adjoint A :=
{ to_linear_equiv := star_module.decompose_prod_adjoint R A,
  continuous_to_fun := continuous_decompose_prod_adjoint _ _,
  continuous_inv_fun := continuous_decompose_prod_adjoint_symm _ _ }
