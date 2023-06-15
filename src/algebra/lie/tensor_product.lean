/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.abelian

/-!
# Tensor products of Lie modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Tensor products of Lie modules carry natural Lie module structures.

## Tags

lie module, tensor product, universal property
-/

universes u v w w₁ w₂ w₃

variables {R : Type u} [comm_ring R]

open lie_module

namespace tensor_product

open_locale tensor_product

namespace lie_module

variables {L : Type v} {M : Type w} {N : Type w₁} {P : Type w₂} {Q : Type w₃}
variables [lie_ring L] [lie_algebra R L]
variables [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M]
variables [add_comm_group N] [module R N] [lie_ring_module L N] [lie_module R L N]
variables [add_comm_group P] [module R P] [lie_ring_module L P] [lie_module R L P]
variables [add_comm_group Q] [module R Q] [lie_ring_module L Q] [lie_module R L Q]
local attribute [ext] tensor_product.ext

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
      { simp only [← linear_map.add_apply], rw [← linear_map.comp_apply, this], refl },
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

@[simp] lemma lie_tmul_right (x : L) (m : M) (n : N) :
  ⁅x, m ⊗ₜ[R] n⁆ = ⁅x, m⁆ ⊗ₜ n + m ⊗ₜ ⁅x, n⁆ :=
show has_bracket_aux x (m ⊗ₜ[R] n) = _,
by simp only [has_bracket_aux, linear_map.rtensor_tmul, to_endomorphism_apply_apply,
  linear_map.add_apply, linear_map.ltensor_tmul]

variables (R L M N P Q)

/-- The universal property for tensor product of modules of a Lie algebra: the `R`-linear
tensor-hom adjunction is equivariant with respect to the `L` action. -/
def lift : (M →ₗ[R] N →ₗ[R] P) ≃ₗ⁅R,L⁆ (M ⊗[R] N →ₗ[R] P) :=
{ map_lie'  := λ x f, by
    { ext m n, simp only [mk_apply, linear_map.compr₂_apply, lie_tmul_right, linear_map.sub_apply,
        lift.equiv_apply, linear_equiv.to_fun_eq_coe, lie_hom.lie_apply, linear_map.map_add],
      abel, },
  ..tensor_product.lift.equiv R M N P }

@[simp] lemma lift_apply (f : M →ₗ[R] N →ₗ[R] P) (m : M) (n : N) :
  lift R L M N P f (m ⊗ₜ n) = f m n :=
rfl

/-- A weaker form of the universal property for tensor product of modules of a Lie algebra.

Note that maps `f` of type `M →ₗ⁅R,L⁆ N →ₗ[R] P` are exactly those `R`-bilinear maps satisfying
`⁅x, f m n⁆ = f ⁅x, m⁆ n + f m ⁅x, n⁆` for all `x, m, n` (see e.g, `lie_module_hom.map_lie₂`). -/
def lift_lie : (M →ₗ⁅R,L⁆ N →ₗ[R] P) ≃ₗ[R] (M ⊗[R] N →ₗ⁅R,L⁆ P) :=
(max_triv_linear_map_equiv_lie_module_hom.symm ≪≫ₗ
↑(max_triv_equiv (lift R L M N P))) ≪≫ₗ
max_triv_linear_map_equiv_lie_module_hom

@[simp] lemma coe_lift_lie_eq_lift_coe (f : M →ₗ⁅R,L⁆ N →ₗ[R] P) :
  ⇑(lift_lie R L M N P f) = lift R L M N P f :=
begin
  suffices : (lift_lie R L M N P f : M ⊗[R] N →ₗ[R] P) = lift R L M N P f,
  { rw [← this, lie_module_hom.coe_to_linear_map], },
  ext m n,
  simp only [lift_lie, linear_equiv.trans_apply, lie_module_equiv.coe_to_linear_equiv,
    coe_linear_map_max_triv_linear_map_equiv_lie_module_hom, coe_max_triv_equiv_apply,
    coe_linear_map_max_triv_linear_map_equiv_lie_module_hom_symm],
end

lemma lift_lie_apply (f : M →ₗ⁅R,L⁆ N →ₗ[R] P) (m : M) (n : N) :
  lift_lie R L M N P f (m ⊗ₜ n) = f m n :=
by simp only [coe_lift_lie_eq_lift_coe, lie_module_hom.coe_to_linear_map, lift_apply]

variables {R L M N P Q}

/-- A pair of Lie module morphisms `f : M → P` and `g : N → Q`, induce a Lie module morphism:
`M ⊗ N → P ⊗ Q`. -/
def map (f : M →ₗ⁅R,L⁆ P) (g : N →ₗ⁅R,L⁆ Q) : M ⊗[R] N →ₗ⁅R,L⁆ P ⊗[R] Q :=
{ map_lie' := λ x t, by
    { simp only [linear_map.to_fun_eq_coe],
      apply t.induction_on,
      { simp only [linear_map.map_zero, lie_zero], },
      { intros m n, simp only [lie_module_hom.coe_to_linear_map, lie_tmul_right,
          lie_module_hom.map_lie, map_tmul, linear_map.map_add], },
      { intros t₁ t₂ ht₁ ht₂, simp only [ht₁, ht₂, lie_add, linear_map.map_add], }, },
  .. map (f : M →ₗ[R] P) (g : N →ₗ[R] Q), }

@[simp] lemma coe_linear_map_map (f : M →ₗ⁅R,L⁆ P) (g : N →ₗ⁅R,L⁆ Q) :
  (map f g : M ⊗[R] N →ₗ[R] P ⊗[R] Q) = tensor_product.map (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :=
rfl

@[simp] lemma map_tmul (f : M →ₗ⁅R,L⁆ P) (g : N →ₗ⁅R,L⁆ Q) (m : M) (n : N) :
  map f g (m ⊗ₜ n) = (f m) ⊗ₜ (g n) :=
map_tmul f g m n

/-- Given Lie submodules `M' ⊆ M` and `N' ⊆ N`, this is the natural map: `M' ⊗ N' → M ⊗ N`. -/
def map_incl (M' : lie_submodule R L M) (N' : lie_submodule R L N) :
  M' ⊗[R] N' →ₗ⁅R,L⁆ M ⊗[R] N :=
map M'.incl N'.incl

@[simp] lemma map_incl_def (M' : lie_submodule R L M) (N' : lie_submodule R L N) :
  map_incl M' N' = map M'.incl N'.incl :=
rfl

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
  lie_hom.coe_to_linear_map, lie_module_hom.coe_mk, linear_map.coe_mk, linear_map.to_fun_eq_coe]

end lie_module

namespace lie_submodule

open_locale tensor_product

open tensor_product.lie_module
open lie_module

variables {L : Type v} {M : Type w}
variables [lie_ring L] [lie_algebra R L]
variables [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M]
variables (I : lie_ideal R L) (N : lie_submodule R L M)

/-- A useful alternative characterisation of Lie ideal operations on Lie submodules.

Given a Lie ideal `I ⊆ L` and a Lie submodule `N ⊆ M`, by tensoring the inclusion maps and then
applying the action of `L` on `M`, we obtain morphism of Lie modules `f : I ⊗ N → L ⊗ M → M`.

This lemma states that `⁅I, N⁆ = range f`. -/
lemma lie_ideal_oper_eq_tensor_map_range :
  ⁅I, N⁆ = ((to_module_hom R L M).comp (map_incl I N : ↥I ⊗ ↥N →ₗ⁅R,L⁆ L ⊗ M)).range :=
begin
  rw [← coe_to_submodule_eq_iff, lie_ideal_oper_eq_linear_span, lie_module_hom.coe_submodule_range,
    lie_module_hom.coe_linear_map_comp, linear_map.range_comp, map_incl_def, coe_linear_map_map,
    tensor_product.map_range_eq_span_tmul, submodule.map_span],
  congr, ext m, split,
  { rintros ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩, use x ⊗ₜ n, split,
    { use [⟨x, hx⟩, ⟨n, hn⟩], simp, },
    { simp, }, },
  { rintros ⟨t, ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩, h⟩, rw ← h, use [⟨x, hx⟩, ⟨n, hn⟩], simp, },
end

end lie_submodule
