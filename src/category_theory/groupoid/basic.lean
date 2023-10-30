/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import category_theory.groupoid
import combinatorics.quiver.basic

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a few basic properties of groupoids.
-/

namespace category_theory

namespace groupoid

variables (C : Type*) [groupoid C]

section thin

lemma is_thin_iff : quiver.is_thin C ↔ ∀ c : C, subsingleton (c ⟶ c) :=
begin
  refine ⟨λ h c, h c c, λ h c d, subsingleton.intro $ λ f g, _⟩,
  haveI := h d,
  calc f = f ≫ (inv g ≫ g) : by simp only [inv_eq_inv, is_iso.inv_hom_id, category.comp_id]
     ... = f ≫ (inv f ≫ g) : by congr
     ... = g               : by simp only [inv_eq_inv, is_iso.hom_inv_id_assoc],
end

end thin

section disconnected

/-- A subgroupoid is totally disconnected if it only has loops. -/
def is_totally_disconnected := ∀ (c d : C), (c ⟶ d) → c = d

end disconnected

end groupoid

end category_theory
