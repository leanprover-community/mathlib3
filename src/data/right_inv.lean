/-
Copyright © 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/

import data.equiv.transfer_instance

/-!
# Bundled right inverse (section)
In this file we implement the bundled version of a right inverse function. The final purpose of
this type is to conviniently implement sections of bundles.
-/

/-- Bundled right inverse of a function. Note that here the `nolint` has a true mathematical
meaning: the structure is inhabited iff the function is surjective. -/
@[nolint has_inhabited_instance]
structure right_inv {α: Type*} {β: Type*} (f : α → β) :=
(to_fun : β → α)
(right_inv' : function.right_inverse to_fun f)

namespace right_inv

variables {α: Type*} {β: Type*} {f : α → β} {g h : right_inv f}

instance : has_coe_to_fun (right_inv f) := ⟨_, right_inv.to_fun⟩

@[simp] lemma to_fun_eq_coe (g : right_inv f) : g.to_fun = ⇑g := rfl

lemma coe_injective (H : ⇑g = h) : g = h :=
by { cases g, cases h, congr' }

@[ext] theorem ext (H : ∀ a, g a = h a) : g = h :=
coe_injective $ funext H

lemma right_inv_def {f : α → β} (g : right_inv f) : f ∘ g = id := g.right_inv'.id

lemma right_inverse {f : α → β} (g : right_inv f) : function.right_inverse g f := g.right_inv'

lemma surjective {f : α → β} (g : right_inv f) : function.surjective f := g.right_inverse.surjective

end right_inv
