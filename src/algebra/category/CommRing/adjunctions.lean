/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl
-/
import algebra.category.CommRing.basic
import category_theory.adjunction.basic
import data.mv_polynomial

/-!
Multivariable polynomials on a type is the left adjoint of the
forgetful functor from commutative rings to types.
-/

noncomputable theory

universe u

open mv_polynomial
open category_theory

namespace CommRing

open_locale classical

private def free_obj (α : Type u) : CommRing.{u} := ⟨mv_polynomial α ℤ⟩

def free : Type u ⥤ CommRing.{u} :=
{ obj := free_obj,
  map := λ α β f, ⟨rename f, by apply_instance⟩, }

@[simp] lemma free_obj_α {α : Type u} :
  (free.obj α).α = mv_polynomial α ℤ := rfl

@[simp] lemma free_map_val {α β : Type u} {f : α → β} :
  (free.map f).val = rename f := rfl

def hom_equiv (α : Type u) (R : CommRing.{u}) : (free.obj α ⟶ R) ≃ (α ⟶ forget.obj R) :=
{ to_fun    := λ f, f ∘ X,
  inv_fun   := λ f, ⟨eval₂ (λ n : ℤ, (n : R)) f, by { unfold_coes, apply_instance }⟩,
  left_inv  := λ f, bundled.hom_ext (@eval₂_hom_X _ _ _ _ _ f.val _),
  right_inv := λ x, by { ext1, unfold_coes, simp only [function.comp_app, eval₂_X] } }

def adj : free ⊣ (forget : CommRing ⥤ Type u) :=
adjunction.mk_of_hom_equiv
{ hom_equiv := hom_equiv,
  hom_equiv_naturality_left_symm' :=
  λ X X' Y f g, by { ext1, dsimp, apply eval₂_cast_comp } }.

end CommRing
