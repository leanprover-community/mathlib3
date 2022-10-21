/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import category_theory.groupoid
import category_theory.is_connected

/-!
This file defines a few basic properties of groupoids.
-/

namespace category_theory

namespace groupoid

universes u v

variables (C : Type u) [groupoid C]

section graph_like

/-- A groupoid is graph-like if it has no parallel arrows -/
def is_graph_like := ∀ (c d : C), subsingleton (c ⟶ d)

lemma is_graph_like_iff : (is_graph_like C) ↔ ∀ (c : C), subsingleton (c ⟶ c) :=
begin
  refine ⟨ λ h c, h c c, λ h c d, subsingleton.intro $ λ f g, _ ⟩,
  { have : inv f ≫ g = 𝟙 _, by { obtain ⟨ss⟩ := (h d), apply ss, },
    calc f
       = f ≫ (inv g ≫ g) : by simp
    ...= f ≫ (inv f ≫ g) : by { apply congr_arg2, refl, rw this, simp, }
    ...= g                : by simp, }
end

end graph_like

section disconnected

/-- A subgroupoid is disconnected if it only has loops -/
def is_disconnected := ∀ (c d : C), nonempty (c ⟶ d) → c = d

end disconnected

end groupoid

end category_theory
