/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Mon.basic

/-!
-/

namespace category_theory

universes v u

section

variables {C : Type u} [category.{v} C]

class canonical_generalized_element {X : C} (x : Π Y, X ⟶ Y) :=
(comp_iso : ∀ {Y Y' : C} (φ : Y ≅ Y'), x Y ≫ φ.hom = x Y' . obviously)

attribute [simp] canonical_generalized_element.comp_iso

end

section

variables {C : Type (u+1)} [large_category C] [concrete_category C]

local attribute [instance] concrete_category.has_coe_to_sort
local attribute [instance] concrete_category.has_coe_to_fun

-- If `push_hom` lands, we could use that instead of `simp` here.
meta def canonical_auto_param : tactic unit := `[intros, simp] <|> `[obviously]

class canonical (x : Π (Y : C), (Y : Type u)) :=
(iso_apply : ∀ {Y Y' : C} (φ : Y ≅ Y'), (φ.hom : Y → Y') (x Y) = x Y' . canonical_auto_param)

attribute [simp] canonical.iso_apply

end

open tactic

/-- A tactic for synthesizing instances of the form `canonical _`. -/
-- TODO investigate using `abstract` to cache these as declarations,
-- with `apply_instance` used to retrieve
meta def synthesize_canonical : tactic unit :=
do
  t ← target,
  `(canonical _) ← pure t,
  `[exact {}],
  t ← pp t,
  tactic.trace format!"synthesized: {t}"

example : canonical (λ R : Mon, (1 : R)) := by synthesize_canonical

end category_theory
