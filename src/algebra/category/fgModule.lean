/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Scott Morrison
-/
import category_theory.monoidal.rigid.basic
import linear_algebra.tensor_product_basis
import linear_algebra.coevaluation
import algebra.category.Module.monoidal

/-!
# The category of finitely generated modules over a ring

This introduces `fgModule R`, the category of finitely generated modules over a ring `R`.
It is implemented as a full subcategory on a subtype of `Module R`.

When `K` is a field, `fgModule K` is the category of finite dimensional vector spaces over `K`.

We first create the instance as a preadditive category.
When `R` is commutative we then give the structure as an `R`-linear category.
When `R` is a field we give it the structure of a monoidal category
and then as a right-rigid monoidal category.

## Future work

* Show that `fgModule R` is abelian when `R` is (left)-noetherian.
* Generalize the `monoidal_category` instance to any commutative ring.
* Show that `fgModule R` is a symmetric monoidal category when `R` is commutative.
* Show that `fgModule R` is rigid (it is already right rigid) when `R` is a field.

-/
noncomputable theory

open category_theory Module.monoidal_category
open_locale classical big_operators

universes u

section
variables (R : Type u) [ring R]

/-- Define `fgModule` as the subtype of `Module.{u} K` of finitely generated modules. -/
@[derive [large_category, λ α, has_coe_to_sort α (Sort*), concrete_category, preadditive]]
def fgModule := { V : Module.{u} R // module.finite R V }

end

namespace fgModule

section ring
variables (R : Type u) [ring R]

instance finite (V : fgModule R) : module.finite K V := V.prop

instance : inhabited (fgModule R) := ⟨⟨Module.of K K, module.finite.self K⟩⟩

instance : has_coe (fgModule.{u} R) (Module.{u} R) := { coe := λ V, V.1, }

protected lemma coe_comp {U V W : fgModule R} (f : U ⟶ V) (g : V ⟶ W) :
  ((f ≫ g) : U → W) = (g : V → W) ∘ (f : U → V) := rfl

/-- Lift an unbundled finitely generated module to `fgModule R`. -/
def of (V : Type u) [add_comm_group V] [module R V] [module.finite R V] : fgModule R :=
⟨Module.of R V, by { change module.finite R V, apply_instance }⟩

instance : has_forget₂ (fgModule.{u} R) (Module.{u} R) :=
by { dsimp [fgModule], apply_instance, }

instance : full (forget₂ (fgModule R) (Module.{u} R)) :=
{ preimage := λ X Y f, f, }

end ring

section comm_ring
variables (K : Type u) [comm_ring K]

instance : linear R (fgModule R) := by { dsimp [fgModule], apply_instance, }

end comm_ring

section field
variables (K : Type u) [field K]

instance (V W : fgModule K) : finite_dimensional K (V ⟶ W) :=
(by apply_instance : finite_dimensional K (V →ₗ[K] W))

-- TODO this instance works for any commutative ring, but we don't have `finite_tensor_product` yet.
instance monoidal_category : monoidal_category (fgModule K) :=
monoidal_category.full_monoidal_subcategory
  (λ V, module.finite K V)
  (module.finite.self K)
  (λ X Y hX hY, by exactI finite_dimensional_tensor_product X Y)

/-- The forgetful functor `fgModule K ⥤ Module K` as a monoidal functor. -/
def forget₂_monoidal : monoidal_functor (fgModule K) (Module.{u} K) :=
{ to_functor := forget₂ (fgModule K) (Module.{u} K),
  ε := 𝟙 _,
  μ := λ X Y, 𝟙 _, }

instance forget₂_monoidal_faithful : faithful (forget₂_monoidal K).to_functor :=
by { dsimp [forget₂_monoidal], apply_instance, }

instance forget₂_monoidal_additive : (forget₂_monoidal K).to_functor.additive :=
functor.full_subcategory_inclusion_additive _

instance : monoidal_preadditive (fgModule K) :=
monoidal_preadditive_of_faithful (forget₂_monoidal K)

instance forget₂_monoidal_linear : (forget₂_monoidal K).to_functor.linear K :=
functor.full_subcategory_inclusion_linear K _

instance : monoidal_linear K (fgModule K) :=
monoidal_linear_of_faithful K (forget₂_monoidal K)

variables (V : fgModule K)

/-- The dual module is the dual in the rigid monoidal category `fgModule K`. -/
def fgModule_dual : fgModule K :=
⟨Module.of K (module.dual K V), subspace.module.dual.finite_dimensional⟩

instance : has_coe_to_fun (fgModule_dual K V) (λ _, V → K) :=
{ coe := λ v, by { change V →ₗ[K] K at v, exact v, } }

open category_theory.monoidal_category

/-- The coevaluation map is defined in `linear_algebra.coevaluation`. -/
def fgModule_coevaluation : 𝟙_ (fgModule K) ⟶ V ⊗ (fgModule_dual K V) :=
by apply coevaluation K V

lemma fgModule_coevaluation_apply_one : fgModule_coevaluation K V (1 : K) =
   ∑ (i : basis.of_vector_space_index K V),
    (basis.of_vector_space K V) i ⊗ₜ[K] (basis.of_vector_space K V).coord i :=
by apply coevaluation_apply_one K V

/-- The evaluation morphism is given by the contraction map. -/
def fgModule_evaluation : (fgModule_dual K V) ⊗ V ⟶ 𝟙_ (fgModule K) :=
by apply contract_left K V

@[simp]
lemma fgModule_evaluation_apply (f : (fgModule_dual K V)) (x : V) :
  (fgModule_evaluation K V) (f ⊗ₜ x) = f x :=
by apply contract_left_apply f x

private theorem coevaluation_evaluation :
  let V' : fgModule K := fgModule_dual K V in
  (𝟙 V' ⊗ (fgModule_coevaluation K V)) ≫ (α_ V' V V').inv ≫ (fgModule_evaluation K V ⊗ 𝟙 V')
  = (ρ_ V').hom ≫ (λ_ V').inv :=
by apply contract_left_assoc_coevaluation K V

private theorem evaluation_coevaluation :
  (fgModule_coevaluation K V ⊗ 𝟙 V)
  ≫ (α_ V (fgModule_dual K V) V).hom ≫ (𝟙 V ⊗ fgModule_evaluation K V)
  = (λ_ V).hom ≫ (ρ_ V).inv :=
by apply contract_left_assoc_coevaluation' K V

instance exact_pairing : exact_pairing V (fgModule_dual K V) :=
{ coevaluation := fgModule_coevaluation K V,
  evaluation := fgModule_evaluation K V,
  coevaluation_evaluation' := coevaluation_evaluation K V,
  evaluation_coevaluation' := evaluation_coevaluation K V }

instance right_dual : has_right_dual V := ⟨fgModule_dual K V⟩

instance right_rigid_category : right_rigid_category (fgModule K) := { }

end field

end fgModule
