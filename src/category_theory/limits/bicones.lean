/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.limits.cones
import category_theory.fin_category

/-!
# Bicones

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given a category `J`, a walking `bicone J` is a category whose objects are the objects of `J` and
two extra vertices `bicone.left` and `bicone.right`. The morphisms are the morphisms of `J` and
`left ⟶ j`, `right ⟶ j` for each `j : J` such that `⬝ ⟶ j` and `⬝ ⟶ k` commutes with each
`f : j ⟶ k`.

Given a diagram `F : J ⥤ C` and two `cone F`s, we can join them into a diagram `bicone J ⥤ C` via
`bicone_mk`.

This is used in `category_theory.flat_functors.preserves_finite_limits_of_flat`.
-/

universes v₁ u₁

noncomputable theory

open category_theory.limits
open_locale classical

namespace category_theory
section bicone
variables (J : Type u₁)

/-- Given a category `J`, construct a walking `bicone J` by adjoining two elements. -/
@[derive decidable_eq]
inductive bicone
| left : bicone
| right : bicone
| diagram (val : J) : bicone

instance : inhabited (bicone J) := ⟨bicone.left⟩

instance fin_bicone [fintype J] : fintype (bicone J) :=
{ elems := [bicone.left, bicone.right].to_finset ∪ finset.image bicone.diagram (fintype.elems J),
  complete := λ j, by { cases j; simp, exact fintype.complete j, }, }

variables [category.{v₁} J]

/-- The homs for a walking `bicone J`. -/
inductive bicone_hom : bicone J → bicone J → Type (max u₁ v₁)
| left_id  : bicone_hom bicone.left bicone.left
| right_id : bicone_hom bicone.right bicone.right
| left (j : J) : bicone_hom bicone.left (bicone.diagram j)
| right (j : J) : bicone_hom bicone.right (bicone.diagram j)
| diagram {j k : J} (f : j ⟶ k) : bicone_hom (bicone.diagram j) (bicone.diagram k)

instance : inhabited (bicone_hom J bicone.left bicone.left) := ⟨bicone_hom.left_id⟩

instance bicone_hom.decidable_eq {j k : bicone J} : decidable_eq (bicone_hom J j k) :=
λ f g, by { cases f; cases g; simp; apply_instance }

@[simps]
instance bicone_category_struct : category_struct (bicone J) :=
{ hom := bicone_hom J,
  id := λ j, bicone.cases_on j
    bicone_hom.left_id bicone_hom.right_id (λ k, bicone_hom.diagram (𝟙 k)),
  comp := λ X Y Z f g, by
  { cases f, exact g, exact g,
    cases g, exact bicone_hom.left g_k,
    cases g, exact bicone_hom.right g_k,
    cases g, exact bicone_hom.diagram (f_f ≫ g_f) } }

instance bicone_category : category (bicone J) :=
{ id_comp' := λ X Y f, by { cases f; simp },
  comp_id' := λ X Y f, by { cases f; simp },
  assoc' := λ W X Y Z f g h, by { cases f; cases g; cases h; simp } }

end bicone
section small_category
variables (J : Type v₁) [small_category J]

/--
Given a diagram `F : J ⥤ C` and two `cone F`s, we can join them into a diagram `bicone J ⥤ C`.
-/
@[simps] def bicone_mk {C : Type u₁} [category.{v₁} C]
  {F : J ⥤ C} (c₁ c₂ : cone F) : bicone J ⥤ C :=
{ obj := λ X, bicone.cases_on X c₁.X c₂.X (λ j, F.obj j),
  map := λ X Y f, by
  { cases f, exact (𝟙 _), exact (𝟙 _),
    exact c₁.π.app f_1,
    exact c₂.π.app f_1,
    exact F.map f_f, },
  map_id' := λ X, by { cases X; simp },
  map_comp' := λ X Y Z f g, by
  { cases f,
    exact (category.id_comp _).symm,
    exact (category.id_comp _).symm,
    cases g, exact (category.id_comp _).symm.trans (c₁.π.naturality g_f : _),
    cases g, exact (category.id_comp _).symm.trans (c₂.π.naturality g_f : _),
    cases g, exact F.map_comp _ _ } }

instance fin_bicone_hom [fin_category J] (j k : bicone J) : fintype (j ⟶ k) :=
begin
  cases j; cases k,
  exact { elems := {bicone_hom.left_id}, complete := λ f, by { cases f, simp } },
  exact { elems := ∅, complete := λ f, by { cases f } },
  exact { elems := {bicone_hom.left k}, complete := λ f, by { cases f, simp } },
  exact { elems := ∅, complete := λ f, by { cases f } },
  exact { elems := {bicone_hom.right_id}, complete := λ f, by { cases f, simp } },
  exact { elems := {bicone_hom.right k}, complete := λ f, by { cases f, simp } },
  exact { elems := ∅, complete := λ f, by { cases f } },
  exact { elems := ∅, complete := λ f, by { cases f } },
  exact { elems := finset.image (bicone_hom.diagram) (fintype.elems (j ⟶ k)),
          complete := λ f, by
            { cases f, simp only [finset.mem_image], use f_f, simpa using fintype.complete _, } },
end

instance bicone_small_category : small_category (bicone J) :=
category_theory.bicone_category J

instance bicone_fin_category [fin_category J] : fin_category (bicone J) := {}
end small_category
end category_theory
