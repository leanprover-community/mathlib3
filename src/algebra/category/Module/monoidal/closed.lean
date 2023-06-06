/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Scott Morrison, Jakob von Raumer
-/
import category_theory.closed.monoidal
import algebra.category.Module.monoidal.symmetric

/-!
# The monoidal closed structure on `Module R`.
-/

universes v w x u

open category_theory
open opposite

namespace Module

variables {R : Type u} [comm_ring R]

local attribute [ext] tensor_product.ext

/--
Auxiliary definition for the `monoidal_closed` instance on `Module R`.
(This is only a separate definition in order to speed up typechecking. )
-/
@[simps]
def monoidal_closed_hom_equiv (M N P : Module.{u} R) :
  ((monoidal_category.tensor_left M).obj N ⟶ P) ≃
    (N ⟶ ((linear_coyoneda R (Module R)).obj (op M)).obj P) :=
{ to_fun := λ f, linear_map.compr₂ (tensor_product.mk R N M) ((β_ N M).hom ≫ f),
  inv_fun := λ f, (β_ M N).hom ≫ tensor_product.lift f,
  left_inv := λ f, begin ext m n,
    simp only [tensor_product.mk_apply, tensor_product.lift.tmul, linear_map.compr₂_apply,
      function.comp_app, coe_comp, monoidal_category.braiding_hom_apply],
  end,
  right_inv := λ f, begin ext m n,
    simp only [tensor_product.mk_apply, tensor_product.lift.tmul, linear_map.compr₂_apply,
      symmetric_category.symmetry_assoc],
  end, }

instance : monoidal_closed (Module.{u} R) :=
{ closed' := λ M,
  { is_adj :=
    { right := (linear_coyoneda R (Module.{u} R)).obj (op M),
      adj := adjunction.mk_of_hom_equiv
      { hom_equiv := λ N P, monoidal_closed_hom_equiv M N P, } } } }

lemma ihom_map_apply {M N P : Module.{u} R} (f : N ⟶ P) (g : Module.of R (M ⟶ N)) :
  (ihom M).map f g = g ≫ f := rfl

-- I can't seem to express the function coercion here without writing `@coe_fn`.
@[simp]
lemma monoidal_closed_curry {M N P : Module.{u} R} (f : M ⊗ N ⟶ P) (x : M) (y : N) :
  @coe_fn _ _ linear_map.has_coe_to_fun ((monoidal_closed.curry f : N →ₗ[R] (M →ₗ[R] P)) y) x =
    f (x ⊗ₜ[R] y) :=
rfl

@[simp]
lemma monoidal_closed_uncurry {M N P : Module.{u} R}
  (f : N ⟶ (M ⟶[Module.{u} R] P)) (x : M) (y : N) :
  monoidal_closed.uncurry f (x ⊗ₜ[R] y) = (@coe_fn _ _ linear_map.has_coe_to_fun (f y)) x :=
rfl

/-- Describes the counit of the adjunction `M ⊗ - ⊣ Hom(M, -)`. Given an `R`-module `N` this
should give a map `M ⊗ Hom(M, N) ⟶ N`, so we flip the order of the arguments in the identity map
`Hom(M, N) ⟶ (M ⟶ N)` and uncurry the resulting map `M ⟶ Hom(M, N) ⟶ N.` -/
lemma ihom_ev_app (M N : Module.{u} R) :
  (ihom.ev M).app N = tensor_product.uncurry _ _ _ _ linear_map.id.flip :=
begin
  ext,
  exact Module.monoidal_closed_uncurry _ _ _,
end

/-- Describes the unit of the adjunction `M ⊗ - ⊣ Hom(M, -)`. Given an `R`-module `N` this should
define a map `N ⟶ Hom(M, M ⊗ N)`, which is given by flipping the arguments in the natural
`R`-bilinear map `M ⟶ N ⟶ M ⊗ N`. -/
lemma ihom_coev_app (M N : Module.{u} R) :
  (ihom.coev M).app N = (tensor_product.mk _ _ _).flip :=
rfl

lemma monoidal_closed_pre_app {M N : Module.{u} R} (P : Module.{u} R) (f : N ⟶ M) :
  (monoidal_closed.pre f).app P = linear_map.lcomp R _ f :=
rfl

end Module
