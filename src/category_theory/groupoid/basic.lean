import category_theory.groupoid.vertex_group
import category_theory.groupoid
import algebra.group.defs
import algebra.hom.group
import algebra.hom.equiv
import data.set.lattice
import combinatorics.quiver.connected_component
import combinatorics.quiver.subquiver
import group_theory.subgroup.basic


open set classical function
local attribute [instance] prop_decidable

namespace category_theory

namespace groupoid

universes u v

variables (C : Type u) [groupoid C]

section graph_like

/-- A subgroupoid is graph-like if it has no parallel arrows -/
def is_graph_like := ∀ (c d : C), subsingleton (c ⟶ d)

lemma is_graph_like_iff : (is_graph_like C) ↔ ∀ (c : C), subsingleton (c ⟶ c) :=
begin
  split,
  { rintro h c, exact h c c,},
  { rintros h c d, constructor, rintro f g,
    have : inv f ≫ g = 𝟙 _, by { obtain ⟨ss⟩ := h d, apply ss, },
    calc f
       = f ≫ (inv g ≫ g) : by simp
    ...= f ≫ (inv f ≫ g) : by { apply congr_arg2, refl, rw this, simp, }
    ...= g                : by simp, }
end

end graph_like

section disconnected

/-- A subgroupoid is disconnected if it only has loops -/
def is_disconnected := ∀ (c d : C), c ≠ d → is_empty (c ⟶ d)

end disconnected

end groupoid

end category_theory
