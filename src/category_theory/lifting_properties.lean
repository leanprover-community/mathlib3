/-
Copyright (c) 2021 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach
-/
import category_theory.category
import category_theory.arrow
import category_theory.functor
import category_theory.limits.preserves.shapes.terminal

/-!
# Lifting properties

This file defines the lifting property of two arrows in a category and shows basic properties of
this notion.
We also construct the subcategory consisting of those morphisms which have the right lifting
property with respect to arrows in a given diagram.

## Main results
- `has_lifting_property`: the definition of the lifting property
- `iso_has_right_lifting_property`: any isomorphism satisfies the right lifting property (rlp)
- `id_has_right_lifting_property`: any identity has the rlp
- `right_lifting_property_initial_iff`: spells out the rlp with respect to a map whose source is an
initial object
- `right_lifting_subcat`: given a set of arrows `F : D → arrow C`, we construct the subcategory
of those morphisms `p` in `C` that satisfy the rlp w.r.t. `F i`, for any element `i` of `D`.

## Tags
lifting property
-/

open category_theory.limits

namespace category_theory

universes v u v₁
variables {C : Type u} [category.{v} C]
variables {D : Type v₁}

variables {X Y Z : C}

/-- The lifting property of a morphism `i` with respect to a morphism `p`.
This can be interpreted as the right lifting property of `i` with respect to `p`,
or the left lifting property of `p` with respect to `i`. -/
class has_lifting_property (i p : arrow C) : Prop :=
(sq_has_lift : ∀ (sq : i ⟶ p), arrow.has_lift sq)

instance has_lifting_property' {i p : arrow C} [h : has_lifting_property i p] (sq : i ⟶ p) : arrow.has_lift sq :=
begin
  let s := h.sq_has_lift,
  specialize s sq,
  exact s
end

/-- Any isomorphism has the right lifting property with respect to any map.
A    → X
↓i    ↓p≅
B    → Y
-/
lemma iso_has_right_lifting_property (i : arrow C) (p : X ≅ Y) :
  has_lifting_property i (arrow.mk p.hom) :=
{ sq_has_lift := λ sq, ⟨⟨{ lift := sq.right ≫ p.inv, }⟩⟩ } -- the lift is obtained by p⁻¹ ∘ (B → Y)

/-- Any identity has the right lifting property with respect to any map. -/
lemma id_has_right_lifting_property (i : arrow C) : has_lifting_property i (arrow.mk (𝟙 X)) :=
  iso_has_right_lifting_property i (iso.refl _)

/-- An equivalent characterization for right lifting with respect to a map `i` whose source is
initial.
∅ → X
↓   ↓
B → Y has a lifting iff there is a map B → X making the right part commute.
-/
lemma right_lifting_property_initial_iff (i p : arrow C)
  (h : is_initial i.left) :
  has_lifting_property i p ↔ ∀ {e : i.right ⟶ p.right}, ∃ l : i.right ⟶ p.left, l ≫ p.hom = e :=
begin
  fsplit,
  { intros hlift e,
    have comm : (is_initial.to h p.left) ≫ p.hom = i.hom ≫ e :=
      is_initial.hom_ext h _ _,
    let s := hlift.sq_has_lift,
    specialize s (arrow.hom_mk comm),
    haveI := s,
    use arrow.lift (arrow.hom_mk comm),
    simp },
  { intro hlift,
    constructor,
    intro sq,
    have : ∃ (l : i.right ⟶ p.left), l ≫ p.hom = sq.right := hlift,
    cases this with l hl,
    exact arrow.has_lift.mk ⟨l, is_initial.hom_ext h _ _⟩, }
end

/-- The condition of having the rlp with respect to a morphism `i` is stable under composition. -/
lemma has_right_lifting_property_comp {i : arrow C} {f : X ⟶ Y} {g : Y ⟶ Z}
  (hf : has_lifting_property i (arrow.mk f))
  (hg : has_lifting_property i (arrow.mk g)) :
  has_lifting_property i (arrow.mk (f ≫ g)) :=
{ sq_has_lift := λ sq1,
  begin
    -- construct a square i ⟶ f
    let sq2 : i ⟶ (arrow.mk f) :=
    { left := sq1.left,
      right := arrow.lift (arrow.square_to_snd sq1) },

    -- show that the lift of this square is a lift of i with respect to g ∘ f
    exact ⟨⟨⟨(arrow.lift sq2 : _ ⟶ _), by simp⟩⟩⟩,
  end }

variable {F : D → arrow C}

/-- Given a set of arrows in C, indexed by `F : D → arrow C`,
we construct the (non-full) subcategory of `C`
spanned by those morphisms that have the right lifting property relative to all maps
of the form `F i`, where `i` is any element in `D`. -/
def right_lifting_subcat (F : D → arrow C) := C

/--The objects of this subcategory are the ones of `C`. -/
def right_lifting_subcat.X (x : right_lifting_subcat F) : C := x

lemma id_has_right_lifting_property' (X : C) :
  ∀ i : D, has_lifting_property (F i) (arrow.mk (𝟙 X)) :=
λ i, id_has_right_lifting_property (F i)

lemma has_right_lifting_property_comp'
  {f : X ⟶ Y} (hf : ∀ i : D, has_lifting_property (F i) (arrow.mk f))
  {g : Y ⟶ Z} (hg : ∀ i : D, has_lifting_property (F i) (arrow.mk g)) :
  ∀ i : D,  has_lifting_property (F i) (arrow.mk (f ≫ g)) :=
λ i, has_right_lifting_property_comp (hf i) (hg i)

instance : category (right_lifting_subcat F) :=
{ hom := λ X Y, { p : X.X ⟶ Y.X //
    ∀ {i : D}, has_lifting_property (F i) (arrow.mk p) },
  id := λ X, ⟨𝟙 X.X, id_has_right_lifting_property' X⟩,
  comp := λ X Y Z f g, ⟨f.val ≫ g.val,
    begin intro i, apply has_right_lifting_property_comp' f.property g.property end⟩ }

end category_theory
