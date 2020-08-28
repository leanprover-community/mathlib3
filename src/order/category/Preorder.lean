/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import category_theory.concrete_category
import algebra.punit_instances

/-! # Category of preorders -/

open category_theory

/-- The category of preorders. -/
def Preorder := bundled preorder

/-- Bundled monotone (aka, increasing) function -/
structure preorder_hom (α β : Type*) [preorder α] [preorder β] :=
(to_fun   : α → β)
(monotone : monotone to_fun)

namespace preorder_hom
variables {α β γ : Type*} [preorder α] [preorder β] [preorder γ]

instance : has_coe_to_fun (preorder_hom α β) :=
{ F := λ f, α → β,
  coe := preorder_hom.to_fun }

@[ext] lemma ext (f g : preorder_hom α β) (h : ∀ a, f a = g a) : f = g :=
by { cases f, cases g, congr, funext, exact h _ }

lemma coe_inj (f g : preorder_hom α β) (h : (f : α → β) = g) : f = g :=
by { ext, rw h }

/-- The identity function as bundled monotone function. -/
@[simps]
def id : preorder_hom α α :=
⟨id, monotone_id⟩

instance : inhabited (preorder_hom α α) := ⟨id⟩

@[simp] lemma coe_id : (@id α _ : α → α) = id := rfl

/-- The composition of two bundled monotone functions. -/
@[simps]
def comp (g : preorder_hom β γ) (f : preorder_hom α β) : preorder_hom α γ :=
⟨g ∘ f, g.monotone.comp f.monotone⟩

@[simp] lemma comp_id (f : preorder_hom α β) : f.comp id = f :=
by { ext, refl }

@[simp] lemma id_comp (f : preorder_hom α β) : id.comp f = f :=
by { ext, refl }

end preorder_hom

namespace Preorder

instance : bundled_hom @preorder_hom :=
{ to_fun := @preorder_hom.to_fun,
  id := @preorder_hom.id,
  comp := @preorder_hom.comp,
  hom_ext := @preorder_hom.coe_inj }

attribute [derive [has_coe_to_sort, large_category, concrete_category]] Preorder

/-- Construct a bundled Preorder from the underlying type and typeclass. -/
def of (α : Type*) [preorder α] : Preorder := bundled.of α

instance : inhabited Preorder := ⟨of punit⟩

instance (α : Preorder) : preorder α := α.str

end Preorder
