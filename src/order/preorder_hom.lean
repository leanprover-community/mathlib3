/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

# Preorder homomorphisms

Bundled monotone functions, `x ≤ y → f x ≤ f y`.
-/

import order.basic

/-! # Category of preorders -/

/-- Bundled monotone (aka, increasing) function -/
structure preorder_hom (α β : Type*) [preorder α] [preorder β] :=
(to_fun   : α → β)
(monotone : monotone to_fun)

infixr ` →ₘ `:25 := preorder_hom

namespace preorder_hom
variables {α : Type*} {β : Type*} {γ : Type*} [preorder α] [preorder β] [preorder γ]

instance : has_coe_to_fun (preorder_hom α β) :=
{ F := λ f, α → β,
  coe := preorder_hom.to_fun }

@[simp]
lemma coe_fun_mk {f : α → β} (hf : _root_.monotone f) (x : α) : mk f hf x = f x := rfl

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
