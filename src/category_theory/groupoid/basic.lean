import category_theory.groupoid
import algebra.group.defs
import algebra.hom.group
import algebra.hom.equiv
import data.set.lattice
import combinatorics.quiver.connected_component
import combinatorics.quiver.subquiver
import group_theory.subgroup.basic
import category_theory.is_connected


open set classical function
local attribute [instance] prop_decidable

namespace category_theory

namespace groupoid

universes u v

section of_group

def of_group (G : Type*) [group G] := unit

-- What am I doing wrong?
/-
instance (G : Type*) [g : group G] : groupoid (of_group G) :=
{ hom := @punit.rec (λ _, unit → Type u) (@punit.rec (λ _, Type u) G),
  id := λ a, by {cases a, exact g.one, },
  comp := λ a b c x y, @punit.rec (λ _, unit → Type u) (@punit.rec (λ _, Type u) G),
  --by {cases a, cases b, cases c, apply g.mul x y},
  id_comp' := λ a b x, by {cases a, cases b, exact one_mul x,},
  comp_id' := λ a b x, by {cases a, cases b, exact mul_one x,},
  assoc' := λ a b c d x y z, by {cases a, cases b, cases c, cases d, exact mul_assoc x y z, },
  inv := λ a b x, by {cases a, cases b, exact g.inv x, }
  inv_comp' := λ a b ⟨p,hp⟩, by simp only [inv_comp],
  comp_inv' := λ a b ⟨p,hp⟩, by simp only [comp_inv] }
-/

end of_group

variables (C : Type u) [groupoid C]

section is_connected

lemma is_connected_iff : is_connected C ↔ (∀ X Y : C, nonempty (X ⟶ Y)) := sorry

end is_connected

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
def is_disconnected := ∀ (c d : C), nonempty (c ⟶ d) → c = d

end disconnected

end groupoid

end category_theory
