/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import category_theory.monoidal.rigid.basic
import category_theory.monoidal.subcategory
import linear_algebra.coevaluation
import algebra.category.Module.monoidal

/-!
# The category of finitely generated modules over a ring

This introduces `fgModule R`, the category of finitely generated modules over a ring `R`.
It is implemented as a full subcategory on a subtype of `Module R`.

When `K` is a field, `fgModule K` is the category of finite dimensional vector spaces over `K`.

We first create the instance as a preadditive category.
When `R` is commutative we then give the structure as an `R`-linear monoidal category.
When `R` is a field we give it the structure of a closed monoidal category
and then as a right-rigid monoidal category.

## Future work

* Show that `fgModule R` is abelian when `R` is (left)-noetherian.

-/
noncomputable theory

open category_theory Module.monoidal_category
open_locale classical big_operators

universes u


section ring
variables (R : Type u) [ring R]

/-- Define `fgModule` as the subtype of `Module.{u} R` of finitely generated modules. -/
@[derive [large_category, concrete_category, preadditive]]
def fgModule := full_subcategory (λ (V : Module.{u} R), module.finite R V)

end ring

namespace fgModule

section ring
variables (R : Type u) [ring R]

instance finite (V : fgModule R) : module.finite R V.obj := V.property

instance : inhabited (fgModule R) := ⟨⟨Module.of R R, module.finite.self R⟩⟩

/-- Lift an unbundled finitely generated module to `fgModule R`. -/
def of (V : Type u) [add_comm_group V] [module R V] [module.finite R V] : fgModule R :=
⟨Module.of R V, by { change module.finite R V, apply_instance }⟩

instance (V : fgModule R) : module.finite R V.obj := V.property

instance : has_forget₂ (fgModule.{u} R) (Module.{u} R) :=
by { dsimp [fgModule], apply_instance, }

instance : full (forget₂ (fgModule R) (Module.{u} R)) :=
{ preimage := λ X Y f, f, }

variables {R}

/-- Converts and isomorphism in the category `fgModule R` to a `linear_equiv` between the underlying
modules. -/
def iso_to_linear_equiv {V W : fgModule R} (i : V ≅ W) : V.obj ≃ₗ[R] W.obj :=
  ((forget₂ (fgModule.{u} R) (Module.{u} R)).map_iso i).to_linear_equiv

/-- Converts a `linear_equiv` to an isomorphism in the category `fgModule R`. -/
@[simps] def _root_.linear_equiv.to_fgModule_iso
  {V W : Type u} [add_comm_group V] [module R V] [module.finite R V]
  [add_comm_group W] [module R W] [module.finite R W]
  (e : V ≃ₗ[R] W) :
  fgModule.of R V ≅ fgModule.of R W :=
{ hom := e.to_linear_map,
  inv := e.symm.to_linear_map,
  hom_inv_id' := by {ext, exact e.left_inv x},
  inv_hom_id' := by {ext, exact e.right_inv x} }


end ring

section comm_ring
variables (R : Type u) [comm_ring R]

instance : linear R (fgModule R) := by dsimp_result { dsimp [fgModule], apply_instance, }

instance monoidal_predicate_module_finite :
  monoidal_category.monoidal_predicate (λ V : Module.{u} R, module.finite R V) :=
{ prop_id' := module.finite.self R,
  prop_tensor' := λ X Y hX hY, by exactI module.finite.tensor_product R X Y }

instance : monoidal_category (fgModule R) :=
by dsimp_result { dsimp [fgModule], apply_instance, }
instance : symmetric_category (fgModule R) :=
by dsimp_result { dsimp [fgModule], apply_instance, }
instance : monoidal_preadditive (fgModule R) :=
by dsimp_result { dsimp [fgModule], apply_instance, }
instance : monoidal_linear R (fgModule R) :=
by dsimp_result { dsimp [fgModule], apply_instance, }

/-- The forgetful functor `fgModule R ⥤ Module R` as a monoidal functor. -/
def forget₂_monoidal : monoidal_functor (fgModule R) (Module.{u} R) :=
monoidal_category.full_monoidal_subcategory_inclusion _

instance forget₂_monoidal_faithful : faithful (forget₂_monoidal R).to_functor :=
by { dsimp [forget₂_monoidal], apply_instance, }

instance forget₂_monoidal_additive : (forget₂_monoidal R).to_functor.additive :=
by { dsimp [forget₂_monoidal], apply_instance, }

instance forget₂_monoidal_linear : (forget₂_monoidal R).to_functor.linear R :=
by { dsimp [forget₂_monoidal], apply_instance, }


lemma iso.conj_eq_conj {V W : fgModule R} (i : V ≅ W) (f : End V) :
  iso.conj i f = linear_equiv.conj (iso_to_linear_equiv i) f := rfl

end comm_ring

section field
variables (K : Type u) [field K]

instance (V W : fgModule K) : module.finite K (V ⟶ W) :=
(by apply_instance : module.finite K (V.obj →ₗ[K] W.obj))

instance closed_predicate_module_finite :
  monoidal_category.closed_predicate (λ V : Module.{u} K, module.finite K V) :=
{ prop_ihom' := λ X Y hX hY, by exactI @linear_map.finite_dimensional K _ X _ _ hX Y _ _ hY }

instance : monoidal_closed (fgModule K) := by dsimp_result { dsimp [fgModule], apply_instance, }

variables (V W : fgModule K)

@[simp] lemma ihom_obj : (ihom V).obj W = fgModule.of K (V.obj →ₗ[K] W.obj) := rfl

/-- The dual module is the dual in the rigid monoidal category `fgModule K`. -/
def fgModule_dual : fgModule K :=
⟨Module.of K (module.dual K V.obj), subspace.module.dual.finite_dimensional⟩

open category_theory.monoidal_category

/-- The coevaluation map is defined in `linear_algebra.coevaluation`. -/
def fgModule_coevaluation : 𝟙_ (fgModule K) ⟶ V ⊗ (fgModule_dual K V) :=
by apply coevaluation K V.obj

lemma fgModule_coevaluation_apply_one : fgModule_coevaluation K V (1 : K) =
   ∑ (i : basis.of_vector_space_index K V.obj),
    (basis.of_vector_space K V.obj) i ⊗ₜ[K] (basis.of_vector_space K V.obj).coord i :=
by apply coevaluation_apply_one K V.obj

/-- The evaluation morphism is given by the contraction map. -/
def fgModule_evaluation : (fgModule_dual K V) ⊗ V ⟶ 𝟙_ (fgModule K) :=
by apply contract_left K V.obj

@[simp]
lemma fgModule_evaluation_apply (f : (fgModule_dual K V).obj) (x : V.obj) :
  (fgModule_evaluation K V) (f ⊗ₜ x) = f.to_fun x :=
by apply contract_left_apply f x

private theorem coevaluation_evaluation :
  let V' : fgModule K := fgModule_dual K V in
  (𝟙 V' ⊗ (fgModule_coevaluation K V)) ≫ (α_ V' V V').inv ≫ (fgModule_evaluation K V ⊗ 𝟙 V')
  = (ρ_ V').hom ≫ (λ_ V').inv :=
by apply contract_left_assoc_coevaluation K V.obj

private theorem evaluation_coevaluation :
  (fgModule_coevaluation K V ⊗ 𝟙 V)
  ≫ (α_ V (fgModule_dual K V) V).hom ≫ (𝟙 V ⊗ fgModule_evaluation K V)
  = (λ_ V).hom ≫ (ρ_ V).inv :=
by apply contract_left_assoc_coevaluation' K V.obj

instance exact_pairing : exact_pairing V (fgModule_dual K V) :=
{ coevaluation := fgModule_coevaluation K V,
  evaluation := fgModule_evaluation K V,
  coevaluation_evaluation' := coevaluation_evaluation K V,
  evaluation_coevaluation' := evaluation_coevaluation K V }

instance right_dual : has_right_dual V := ⟨fgModule_dual K V⟩

instance right_rigid_category : right_rigid_category (fgModule K) := { }

end field

end fgModule
