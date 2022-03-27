/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import category_theory.concrete_category.bundled_hom

/-!
# Category instances for structures that use unbundled homs

This file provides basic infrastructure to define concrete
categories using unbundled homs (see `class unbundled_hom`), and
define forgetful functors between them (see
`unbundled_hom.mk_has_forget₂`).
-/

universes v u

namespace category_theory

/-- A class for unbundled homs used to define a category. `hom` must
take two types `α`, `β` and instances of the corresponding structures,
and return a predicate on `α → β`. -/
class unbundled_hom {c : Type u → Type u} (hom : Π {α β}, c α → c β → (α → β) → Prop) :=
(hom_id [] : ∀ {α} (ia : c α), hom ia ia id)
(hom_comp [] : ∀ {α β γ} {Iα : c α} {Iβ : c β} {Iγ : c γ} {g : β → γ} {f : α → β}
  (hg : hom Iβ Iγ g) (hf : hom Iα Iβ f), hom Iα Iγ (g ∘ f))

namespace unbundled_hom

variables (c : Type u → Type u) (hom : Π ⦃α β⦄, c α → c β → (α → β) → Prop) [𝒞 : unbundled_hom hom]
include 𝒞

instance bundled_hom : bundled_hom (λ α β (Iα : c α) (Iβ : c β), subtype (hom Iα Iβ)) :=
{ to_fun := λ _ _ _ _, subtype.val,
  id := λ α Iα, ⟨id, hom_id hom Iα⟩,
  id_to_fun := by intros; refl,
  comp := λ _ _ _ _ _ _ g f, ⟨g.1 ∘ f.1, hom_comp c g.2 f.2⟩,
  comp_to_fun := by intros; refl,
  hom_ext := by intros; apply subtype.eq }

section has_forget₂

variables {c hom} {c' : Type u → Type u} {hom' : Π ⦃α β⦄, c' α → c' β → (α → β) → Prop}
  [𝒞' : unbundled_hom hom']
include 𝒞'

variables (obj : Π ⦃α⦄, c α → c' α)
  (map : ∀ ⦃α β Iα Iβ f⦄, @hom α β Iα Iβ f → hom' (obj Iα) (obj Iβ) f)

/-- A custom constructor for forgetful functor
between concrete categories defined using `unbundled_hom`. -/
def mk_has_forget₂ : has_forget₂ (bundled c) (bundled c') :=
bundled_hom.mk_has_forget₂ obj (λ X Y f, ⟨f.val, map f.property⟩) (λ _ _ _, rfl)

end has_forget₂

end unbundled_hom

end category_theory
