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
It is implemented as a full subcategory on a subtype of `Module K`, which inherits monoidal and
symmetric structure as `finite_dimensional K` is a monoidal predicate.
We also provide a right rigid monoidal category instance.
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

instance closed_predicate_finite_dimensional :
  monoidal_category.closed_predicate (λ V : Module.{u} K, finite_dimensional K V) :=
{ prop_ihom' := λ X Y hX hY, by exactI @linear_map.finite_dimensional K _ X _ _ hX Y _ _ hY }

/-- Define `FinVect` as the subtype of `Module.{u} K` of finite dimensional vector spaces. -/
@[derive [large_category, concrete_category, monoidal_category, symmetric_category,
monoidal_closed]]
def FinVect := full_subcategory (λ (V : Module.{u} K), finite_dimensional K V)

namespace FinVect

instance finite_dimensional (V : FinVect K) : finite_dimensional K V.obj := V.property

instance : inhabited (FinVect K) := ⟨⟨Module.of K K, finite_dimensional.finite_dimensional_self K⟩⟩

/-- Lift an unbundled vector space to `FinVect K`. -/
def of (V : Type u) [add_comm_group V] [module K V] [finite_dimensional K V] : FinVect K :=
⟨Module.of K V, by { change finite_dimensional K V, apply_instance }⟩

instance : has_forget₂ (FinVect.{u} K) (Module.{u} K) :=
by { dsimp [FinVect], apply_instance, }

instance : full (forget₂ (FinVect K) (Module.{u} K)) :=
{ preimage := λ X Y f, f, }

variables (V W : FinVect K)

@[simp] lemma ihom_obj : (ihom V).obj W = FinVect.of K (V.obj →ₗ[K] W.obj) := rfl

/-- The dual module is the dual in the rigid monoidal category `FinVect K`. -/
def FinVect_dual : FinVect K :=
⟨Module.of K (module.dual K V.obj), subspace.module.dual.finite_dimensional⟩

open category_theory.monoidal_category

/-- The coevaluation map is defined in `linear_algebra.coevaluation`. -/
def FinVect_coevaluation : 𝟙_ (FinVect K) ⟶ V ⊗ (FinVect_dual K V) :=
by apply coevaluation K V.obj

lemma FinVect_coevaluation_apply_one : FinVect_coevaluation K V (1 : K) =
   ∑ (i : basis.of_vector_space_index K V.obj),
    (basis.of_vector_space K V.obj) i ⊗ₜ[K] (basis.of_vector_space K V.obj).coord i :=
by apply coevaluation_apply_one K V.obj

/-- The evaluation morphism is given by the contraction map. -/
def FinVect_evaluation : (FinVect_dual K V) ⊗ V ⟶ 𝟙_ (FinVect K) :=
by apply contract_left K V.obj

@[simp]
lemma FinVect_evaluation_apply (f : (FinVect_dual K V).obj) (x : V.obj) :
  (FinVect_evaluation K V) (f ⊗ₜ x) = f.to_fun x :=
by apply contract_left_apply f x

private theorem coevaluation_evaluation :
  let V' : FinVect K := FinVect_dual K V in
  (𝟙 V' ⊗ (FinVect_coevaluation K V)) ≫ (α_ V' V V').inv ≫ (FinVect_evaluation K V ⊗ 𝟙 V')
  = (ρ_ V').hom ≫ (λ_ V').inv :=
by apply contract_left_assoc_coevaluation K V.obj

private theorem evaluation_coevaluation :
  (FinVect_coevaluation K V ⊗ 𝟙 V)
  ≫ (α_ V (FinVect_dual K V) V).hom ≫ (𝟙 V ⊗ FinVect_evaluation K V)
  = (λ_ V).hom ≫ (ρ_ V).inv :=
by apply contract_left_assoc_coevaluation' K V.obj

instance exact_pairing : exact_pairing V (FinVect_dual K V) :=
{ coevaluation := FinVect_coevaluation K V,
  evaluation := FinVect_evaluation K V,
  coevaluation_evaluation' := coevaluation_evaluation K V,
  evaluation_coevaluation' := evaluation_coevaluation K V }

instance right_dual : has_right_dual V := ⟨FinVect_dual K V⟩

instance right_rigid_category : right_rigid_category (FinVect K) := { }

variables {K V}

/-- Converts and isomorphism in the category `FinVect` to a `linear_equiv` between the underlying
vector spaces. -/
def iso_to_linear_equiv {V W : FinVect K} (i : V ≅ W) : V.obj ≃ₗ[K] W.obj :=
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
