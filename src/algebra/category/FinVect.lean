/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import category_theory.monoidal.rigid
import linear_algebra.tensor_product_basis
import linear_algebra.coevaluation
import algebra.category.Module.monoidal

/-!
# The category of finite dimensional vector spaces

This introduces `FinVect K`, the category of finite dimensional vector spaces on a field `K`.
It is implemented as a full subcategory on a subtype of  `Module K`.
We first create the instance as a category, then as a monoidal category and then as a rigid monoidal
category.

## Future work

* Show that `FinVect K` is a symmetric monoidal category.

-/
noncomputable theory

open category_theory Module.monoidal_category
open_locale classical big_operators

universes u

variables (K : Type u) [field K]

/-- Define `FinVect` as the subtype of `Module.{u} K` of finite dimensional vector spaces. -/
@[derive [category, has_coe_to_sort]]
def FinVect := { V : Module.{u} K // finite_dimensional K V }

namespace FinVect

instance finite_dimensional (V : FinVect K): finite_dimensional K V := V.prop

instance : inhabited (FinVect K) := ⟨⟨Module.of K K, finite_dimensional.finite_dimensional_self K⟩⟩

instance : has_coe (FinVect.{u} K) (Module.{u} K) := { coe := λ V, V.1, }

protected lemma coe_comp {U V W : FinVect K} (f : U ⟶ V) (g : V ⟶ W) :
  ((f ≫ g) : U → W) = (g : V → W) ∘ (f : U → V) := rfl

instance monoidal_category : monoidal_category (FinVect K) :=
monoidal_category.full_monoidal_subcategory
  (λ V, finite_dimensional K V)
  (finite_dimensional.finite_dimensional_self K)
  (λ X Y hX hY, by exactI finite_dimensional_tensor_product X Y)

variables (V : FinVect K)

/-- The dual module is the dual in the rigid monoidal category `FinVect K`. -/
def FinVect_dual : FinVect K :=
⟨Module.of K (module.dual K V), subspace.module.dual.finite_dimensional⟩

instance : has_coe_to_fun (FinVect_dual K V) :=
{ F := λ v, V → K,
  coe := λ v, by { change V →ₗ[K] K at v, exact v, }, }

open category_theory.monoidal_category

/-- The coevaluation map is defined in `linear_algebra.coevaluation`. -/
def FinVect_coevaluation : 𝟙_ (FinVect K) ⟶ V ⊗ (FinVect_dual K V) :=
by apply coevaluation K V

lemma FinVect_coevaluation_apply_one : FinVect_coevaluation K V (1 : K) =
   ∑ (i : basis.of_vector_space_index K V),
    (basis.of_vector_space K V) i ⊗ₜ[K] (basis.of_vector_space K V).coord i :=
by apply coevaluation_apply_one K V

/-- The evaluation morphism is given by the contraction map. -/
def FinVect_evaluation : (FinVect_dual K V) ⊗ V ⟶ 𝟙_ (FinVect K) :=
by apply contract_left K V

@[simp]
lemma FinVect_evaluation_apply (f : (FinVect_dual K V)) (x : V) :
  (FinVect_evaluation K V) (f ⊗ₜ x) = f x :=
by apply contract_left_apply f x

private theorem coevaluation_evaluation :
  let V' : FinVect K := FinVect_dual K V in
  (𝟙 V' ⊗ (FinVect_coevaluation K V)) ≫ (α_ V' V V').inv ≫ (FinVect_evaluation K V ⊗ 𝟙 V')
  = (ρ_ V').hom ≫ (λ_ V').inv :=
by apply contract_left_assoc_coevaluation K V

private theorem evaluation_coevaluation :
  (FinVect_coevaluation K V ⊗ 𝟙 V)
  ≫ (α_ V (FinVect_dual K V) V).hom ≫ (𝟙 V ⊗ FinVect_evaluation K V)
  = (λ_ V).hom ≫ (ρ_ V).inv :=
by apply contract_left_assoc_coevaluation' K V

instance exact_pairing : exact_pairing V (FinVect_dual K V) :=
{ coevaluation := FinVect_coevaluation K V,
  evaluation := FinVect_evaluation K V,
  coevaluation_evaluation' := coevaluation_evaluation K V,
  evaluation_coevaluation' := evaluation_coevaluation K V }

instance right_dual : has_right_dual V := ⟨FinVect_dual K V⟩

instance right_rigid_category : right_rigid_category (FinVect K) := { }

end FinVect
