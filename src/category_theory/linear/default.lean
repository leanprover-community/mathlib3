/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.preadditive
import algebra.module.linear_map
import algebra.invertible
import linear_algebra.basic
import algebra.algebra.basic

/-!
# Linear categories

An `R`-linear category is a category in which `X ⟶ Y` is an `R`-module in such a way that
composition of morphisms is `R`-linear in both variables.

## Implementation

Corresponding to the fact that we need to have an `add_comm_group X` structure in place
to talk about a `module R X` structure,
we need `preadditive C` as a prerequisite typeclass for `linear R C`.
This makes for longer signatures than would be ideal.

## Future work

It would be nice to have a usable framework of enriched categories in which this just became
a category enriched in `Module R`.

-/

universes w v u

open category_theory.limits
open linear_map

namespace category_theory

/-- A category is called `R`-linear if `P ⟶ Q` is an `R`-module such that composition is
    `R`-linear in both variables. -/
class linear (R : Type w) [semiring R] (C : Type u) [category.{v} C] [preadditive C] :=
(hom_module : Π X Y : C, module R (X ⟶ Y) . tactic.apply_instance)
(smul_comp' : ∀ (X Y Z : C) (r : R) (f : X ⟶ Y) (g : Y ⟶ Z),
  (r • f) ≫ g = r • (f ≫ g) . obviously)
(comp_smul' : ∀ (X Y Z : C) (f : X ⟶ Y) (r : R) (g : Y ⟶ Z),
  f ≫ (r • g) = r • (f ≫ g) . obviously)

attribute [instance] linear.hom_module
restate_axiom linear.smul_comp'
restate_axiom linear.comp_smul'
attribute [simp,reassoc] linear.smul_comp
attribute [reassoc, simp] linear.comp_smul -- (the linter doesn't like `simp` on the `_assoc` lemma)

end category_theory

open category_theory

namespace category_theory.linear

variables {C : Type u} [category.{v} C] [preadditive C]

instance preadditive_nat_linear : linear ℕ C :=
{ smul_comp' := λ X Y Z r f g, (preadditive.right_comp X g).map_nsmul f r,
  comp_smul' := λ X Y Z f r g, (preadditive.left_comp Z f).map_nsmul g r, }

instance preadditive_int_linear : linear ℤ C :=
{ smul_comp' := λ X Y Z r f g, (preadditive.right_comp X g).map_zsmul f r,
  comp_smul' := λ X Y Z f r g, (preadditive.left_comp Z f).map_zsmul g r, }

section End

variables {R : Type w} [comm_ring R] [linear R C]

instance (X : C) : module R (End X) := by { dsimp [End], apply_instance, }

instance (X : C) : algebra R (End X) :=
algebra.of_module (λ r f g, comp_smul _ _ _ _ _ _) (λ r f g, smul_comp _ _ _ _ _ _)

end End

section
variables {R : Type w} [semiring R] [linear R C]

section induced_category
universes u'
variables {C} {D : Type u'} (F : D → C)

instance induced_category.category : linear.{w v} R (induced_category C F) :=
{ hom_module := λ X Y, @linear.hom_module R _ C _ _ _ (F X) (F Y),
  smul_comp' := λ P Q R f f' g, smul_comp' _ _ _ _ _ _,
  comp_smul' := λ P Q R f g g', comp_smul' _ _ _ _ _ _, }

end induced_category

variables (R)

/-- Composition by a fixed left argument as an `R`-linear map. -/
@[simps]
def left_comp {X Y : C} (Z : C) (f : X ⟶ Y) : (Y ⟶ Z) →ₗ[R] (X ⟶ Z) :=
{ to_fun := λ g, f ≫ g,
  map_add' := by simp,
  map_smul' := by simp, }

/-- Composition by a fixed right argument as an `R`-linear map. -/
@[simps]
def right_comp (X : C) {Y Z : C} (g : Y ⟶ Z) : (X ⟶ Y) →ₗ[R] (X ⟶ Z) :=
{ to_fun := λ f, f ≫ g,
  map_add' := by simp,
  map_smul' := by simp, }

instance {X Y : C} (f : X ⟶ Y) [epi f] (r : R) [invertible r] : epi (r • f) :=
⟨λ R g g' H, begin
  rw [smul_comp, smul_comp, ←comp_smul, ←comp_smul, cancel_epi] at H,
  simpa [smul_smul] using congr_arg (λ f, ⅟r • f) H,
end⟩

instance {X Y : C} (f : X ⟶ Y) [mono f] (r : R) [invertible r] : mono (r • f) :=
⟨λ R g g' H, begin
  rw [comp_smul, comp_smul, ←smul_comp, ←smul_comp, cancel_mono] at H,
  simpa [smul_smul] using congr_arg (λ f, ⅟r • f) H,
end⟩

end

section
variables {S : Type w} [comm_semiring S] [linear S C]

/-- Composition as a bilinear map. -/
@[simps]
def comp (X Y Z : C) : (X ⟶ Y) →ₗ[S] ((Y ⟶ Z) →ₗ[S] (X ⟶ Z)) :=
{ to_fun := λ f, left_comp S Z f,
  map_add' := by { intros, ext, simp, },
  map_smul' := by { intros, ext, simp, }, }

end

end category_theory.linear
