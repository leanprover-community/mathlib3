/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.abelian

/-!
# Tensor products of Lie modules

Tensor products of Lie modules carry natural Lie module structures.

## Tags

lie module, tensor product, universal property
-/

universes u v w w₁ w₂

variables {R : Type u} [comm_ring R]

namespace tensor_product

open_locale tensor_product

namespace lie_module

open lie_module

variables {L : Type v} {M : Type w} {N : Type w₁} {P : Type w₂}
variables [lie_ring L] [lie_algebra R L]
variables [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M]
variables [add_comm_group N] [module R N] [lie_ring_module L N] [lie_module R L N]
variables [add_comm_group P] [module R P] [lie_ring_module L P] [lie_module R L P]

/-- It is useful to define the bracket via this auxiliary function so that we have a type-theoretic
expression of the fact that `L` acts by linear endomorphisms. It simplifies the proofs in
`lie_ring_module` below. -/
def has_bracket_aux (x : L) : module.End R (M ⊗[R] N) :=
  (to_endomorphism R L M x).rtensor N + (to_endomorphism R L N x).ltensor M

/-- The tensor product of two Lie modules is a Lie ring module. -/
instance lie_ring_module : lie_ring_module L (M ⊗[R] N) :=
{ bracket     := λ x, has_bracket_aux x,
  add_lie     := λ x y t, by
    { simp only [has_bracket_aux, linear_map.ltensor_add, linear_map.rtensor_add, lie_hom.map_add,
        linear_map.add_apply], abel, },
  lie_add     := λ x, linear_map.map_add _,
  leibniz_lie := λ x y t, by
    { suffices : (has_bracket_aux x).comp (has_bracket_aux y) =
                  has_bracket_aux ⁅x,y⁆ + (has_bracket_aux y).comp (has_bracket_aux x),
      { simp only [← linear_map.comp_apply, ← linear_map.add_apply], rw this, },
      ext m n,
      simp only [has_bracket_aux, lie_ring.of_associative_ring_bracket, linear_map.mul_apply,
        mk_apply, linear_map.ltensor_sub, linear_map.compr₂_apply, function.comp_app,
        linear_map.coe_comp, linear_map.rtensor_tmul, lie_hom.map_lie,
        to_endomorphism_apply_apply, linear_map.add_apply, linear_map.map_add,
        linear_map.rtensor_sub, linear_map.sub_apply, linear_map.ltensor_tmul],
      abel, }, }

/-- The tensor product of two Lie modules is a Lie module. -/
instance lie_module : lie_module R L (M ⊗[R] N) :=
{ smul_lie := λ c x t, by
  { change has_bracket_aux (c • x) _ = c • has_bracket_aux _ _,
    simp only [has_bracket_aux, smul_add, linear_map.rtensor_smul, linear_map.smul_apply,
      linear_map.ltensor_smul, lie_hom.map_smul, linear_map.add_apply], },
  lie_smul := λ c x, linear_map.map_smul _ c, }

@[simp] lemma lie_tensor_right (x : L) (m : M) (n : N) :
  ⁅x, m ⊗ₜ[R] n⁆ = ⁅x, m⁆ ⊗ₜ n + m ⊗ₜ ⁅x, n⁆ :=
show has_bracket_aux x (m ⊗ₜ[R] n) = _,
by simp only [has_bracket_aux, linear_map.rtensor_tmul, to_endomorphism_apply_apply,
  linear_map.add_apply, linear_map.ltensor_tmul]

variables (R L M N P)

/-- The universal property for tensor product of modules of a Lie algebra: the `R`-linear
tensor-hom adjunction is equivariant with respect to the `L` action. -/
def lift : (M →ₗ[R] N →ₗ[R] P) ≃ₗ⁅R,L⁆ (M ⊗[R] N →ₗ[R] P) :=
{ map_lie'  := λ x f, by
    { ext m n, simp only [mk_apply, linear_map.compr₂_apply, lie_tensor_right, linear_map.sub_apply,
        lift.equiv_apply, linear_equiv.to_fun_eq_coe, lie_hom.lie_apply, linear_map.map_add],
      abel, },
  ..tensor_product.lift.equiv R M N P }

@[simp] lemma lift_apply (f : M →ₗ[R] N →ₗ[R] P) (m : M) (n : N) :
  lift R L M N P f (m ⊗ₜ n) = f m n :=
lift.equiv_apply R M N P f m n

/-- A weaker form of the universal property for tensor product of modules of a Lie algebra.

Note that maps `f` of type `M →ₗ⁅R,L⁆ N →ₗ[R] P` are exactly those `R`-bilinear maps satisfying
`⁅x, f m n⁆ = f ⁅x, m⁆ n + f m ⁅x, n⁆` for all `x, m, n` (see e.g, `lie_module_hom.map_lie₂`). -/
def lift_lie : (M →ₗ⁅R,L⁆ N →ₗ[R] P) ≃ₗ[R] (M ⊗[R] N →ₗ⁅R,L⁆ P) :=
(maximal_trivial_linear_map_equiv_lie_module_hom.symm.trans
↑(maximal_trivial_equiv (lift R L M N P))).trans
maximal_trivial_linear_map_equiv_lie_module_hom

@[simp] lemma coe_lift_lie_eq_lift_coe (f : M →ₗ⁅R,L⁆ N →ₗ[R] P) :
  ⇑(lift_lie R L M N P f) = lift R L M N P f :=
begin
  suffices : (lift_lie R L M N P f : M ⊗[R] N →ₗ[R] P) = lift R L M N P f,
  { rw [← this, lie_module_hom.coe_to_linear_map], },
  ext m n,
  simp only [lift_lie, linear_equiv.trans_apply, lie_module_equiv.coe_to_linear_equiv,
    coe_maximal_trivial_linear_map_equiv_lie_module_hom_apply, coe_maximal_trivial_equiv_apply,
    coe_maximal_trivial_linear_map_equiv_lie_module_hom_symm_apply],
end

lemma lift_lie_apply (f : M →ₗ⁅R,L⁆ N →ₗ[R] P) (m : M) (n : N) :
  lift_lie R L M N P f (m ⊗ₜ n) = f m n :=
by simp only [coe_lift_lie_eq_lift_coe, lie_module_hom.coe_to_linear_map, lift_apply]

end lie_module

end tensor_product

namespace lie_module

open_locale tensor_product

variables (R) (L : Type v) (M : Type w)
variables [lie_ring L] [lie_algebra R L]
variables [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M]

/-- The action of the Lie algebra on one of its modules, regarded as a morphism of Lie modules. -/
def to_module_hom : L ⊗[R] M →ₗ⁅R,L⁆ M :=
tensor_product.lie_module.lift_lie R L L M M
{ map_lie' := λ x m, by { ext n, simp [lie_ring.of_associative_ring_bracket], },
  ..(to_endomorphism R L M : L →ₗ[R] M →ₗ[R] M), }

@[simp] lemma to_module_hom_apply (x : L) (m : M) :
  to_module_hom R L M (x ⊗ₜ m) = ⁅x, m⁆ :=
by simp only [to_module_hom, tensor_product.lie_module.lift_lie_apply, to_endomorphism_apply_apply,
  lie_hom.coe_to_linear_map, lie_module_hom.coe_mk, linear_map.to_fun_eq_coe]

end lie_module
