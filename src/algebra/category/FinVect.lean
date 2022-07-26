/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import category_theory.monoidal.rigid.basic
import category_theory.monoidal.subcategory
import linear_algebra.tensor_product_basis
import linear_algebra.coevaluation
import algebra.category.Module.monoidal

/-!
# The category of finite dimensional vector spaces

This introduces `FinVect K`, the category of finite dimensional vector spaces over a field `K`.
It is implemented as a full subcategory on a subtype of `Module K`.

We first create the instance as a `K`-linear category,
then as a `K`-linear monoidal category and then as a right-rigid monoidal category.

## Future work

* Show that `FinVect K` is a symmetric monoidal category (it is already monoidal).
* Show that `FinVect K` is abelian.
* Show that `FinVect K` is rigid (it is already right rigid).

-/
noncomputable theory

open category_theory Module.monoidal_category
open_locale classical big_operators

universes u

variables (K : Type u) [field K]

instance monoidal_predicate_finite_dimensional :
  monoidal_category.monoidal_predicate (λ V : Module.{u} K, finite_dimensional K V) :=
{ prop_id' := finite_dimensional.finite_dimensional_self K,
  prop_tensor' := λ X Y hX hY, by exactI module.finite.tensor_product K X Y }

/-- Define `FinVect` as the subtype of `Module.{u} K` of finite dimensional vector spaces. -/
@[derive [large_category, λ α, has_coe_to_sort α (Sort*), concrete_category, preadditive, linear K,
  monoidal_category, symmetric_category, monoidal_preadditive, monoidal_linear K]]
def FinVect := { V : Module.{u} K // finite_dimensional K V }

namespace FinVect

instance finite_dimensional (V : FinVect K) : finite_dimensional K V := V.prop

instance : inhabited (FinVect K) := ⟨⟨Module.of K K, finite_dimensional.finite_dimensional_self K⟩⟩

instance : has_coe (FinVect.{u} K) (Module.{u} K) := { coe := λ V, V.1, }

protected lemma coe_comp {U V W : FinVect K} (f : U ⟶ V) (g : V ⟶ W) :
  ((f ≫ g) : U → W) = (g : V → W) ∘ (f : U → V) := rfl

/-- Lift an unbundled vector space to `FinVect K`. -/
def of (V : Type u) [add_comm_group V] [module K V] [finite_dimensional K V] : FinVect K :=
⟨Module.of K V, by { change finite_dimensional K V, apply_instance }⟩

instance (V W : FinVect K) : finite_dimensional K (V ⟶ W) :=
(by apply_instance : finite_dimensional K (V →ₗ[K] W))

instance : has_forget₂ (FinVect.{u} K) (Module.{u} K) :=
by { dsimp [FinVect], apply_instance, }

instance : full (forget₂ (FinVect K) (Module.{u} K)) :=
{ preimage := λ X Y f, f, }

/-- The forgetful functor `FinVect K ⥤ Module K` as a monoidal functor. -/
def forget₂_monoidal : monoidal_functor (FinVect K) (Module.{u} K) :=
monoidal_category.full_monoidal_subcategory_inclusion _

instance forget₂_monoidal_faithful : faithful (forget₂_monoidal K).to_functor :=
by { dsimp [forget₂_monoidal], apply_instance, }

instance forget₂_monoidal_additive : (forget₂_monoidal K).to_functor.additive :=
by { dsimp [forget₂_monoidal], apply_instance, }

instance forget₂_monoidal_linear : (forget₂_monoidal K).to_functor.linear K :=
by { dsimp [forget₂_monoidal], apply_instance, }

variables (V : FinVect K)

/-- The dual module is the dual in the rigid monoidal category `FinVect K`. -/
def FinVect_dual : FinVect K :=
⟨Module.of K (module.dual K V), subspace.module.dual.finite_dimensional⟩

instance : has_coe_to_fun (FinVect_dual K V) (λ _, V → K) :=
{ coe := λ v, by { change V →ₗ[K] K at v, exact v, } }

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

variables {K V} (W : FinVect K)

/-- Converts and isomorphism in the category `FinVect` to a `linear_equiv` between the underlying
vector spaces. -/
def iso_to_linear_equiv {V W : FinVect K} (i : V ≅ W) : V ≃ₗ[K] W :=
  ((forget₂ (FinVect.{u} K) (Module.{u} K)).map_iso i).to_linear_equiv

lemma iso.conj_eq_conj {V W : FinVect K} (i : V ≅ W) (f : End V) :
  iso.conj i f = linear_equiv.conj (iso_to_linear_equiv i) f := rfl

end FinVect

variables {K}

/-- Converts a `linear_equiv` to an isomorphism in the category `FinVect`. -/
@[simps] def linear_equiv.to_FinVect_iso
  {V W : Type u} [add_comm_group V] [module K V] [finite_dimensional K V]
  [add_comm_group W] [module K W] [finite_dimensional K W]
  (e : V ≃ₗ[K] W) :
  FinVect.of K V ≅ FinVect.of K W :=
{ hom := e.to_linear_map,
  inv := e.symm.to_linear_map,
  hom_inv_id' := by {ext, exact e.left_inv x},
  inv_hom_id' := by {ext, exact e.right_inv x} }
