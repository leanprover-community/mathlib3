/-
Copyright (c) 2021 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach
-/
import category_theory.arrow
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

@[priority 100] -- see Note [lower instance priority]
instance has_lifting_property' {i p : arrow C} [has_lifting_property i p] (sq : i ⟶ p) :
  arrow.has_lift sq :=
has_lifting_property.sq_has_lift sq

/-- Any isomorphism has the right lifting property with respect to any map.
A    → X
↓i    ↓p≅
B    → Y
-/
lemma iso_has_right_lifting_property (i : arrow C) (p : X ≅ Y) :
  has_lifting_property i (arrow.mk p.hom) :=
⟨λ sq, ⟨⟨{ lift := sq.right ≫ p.inv, }⟩⟩⟩ -- the lift is obtained by p⁻¹ ∘ (B → Y)

/-- Any identity has the right lifting property with respect to any map. -/
lemma id_has_right_lifting_property (i : arrow C) : has_lifting_property i (arrow.mk (𝟙 X)) :=
iso_has_right_lifting_property i (iso.refl _)

/-- An equivalent characterization for right lifting with respect to a map `i` whose source is
initial.
∅ → X
↓   ↓
B → Y has a lifting iff there is a map B → X making the right part commute.
-/
lemma right_lifting_property_initial_iff (i p : arrow C) (h : is_initial i.left) :
  has_lifting_property i p ↔ ∀ {e : i.right ⟶ p.right}, ∃ l : i.right ⟶ p.left, l ≫ p.hom = e :=
begin
  fsplit,
  { introsI hlift e,
    have comm : (is_initial.to h p.left) ≫ p.hom = i.hom ≫ e :=
      is_initial.hom_ext h _ _,
    use arrow.lift (arrow.hom_mk comm),
    simp },
  { refine λ hlift, ⟨λ sq, _⟩,
    obtain ⟨l, hl⟩ : ∃ (l : i.right ⟶ p.left), l ≫ p.hom = sq.right := hlift,
    exact arrow.has_lift.mk ⟨l, is_initial.hom_ext h _ _⟩, }
end

/-- The condition of having the rlp with respect to a morphism `i` is stable under composition. -/
lemma has_right_lifting_property_comp {i : arrow C} {f : X ⟶ Y} {g : Y ⟶ Z}
  (hf : has_lifting_property i (arrow.mk f))
  (hg : has_lifting_property i (arrow.mk g)) :
  has_lifting_property i (arrow.mk (f ≫ g)) :=
{ sq_has_lift := λ sq1,
    -- construct a square i ⟶ f
    let sq2 : i ⟶ (arrow.mk f) := ⟨sq1.left, arrow.lift (arrow.square_to_snd sq1)⟩ in
    -- show that the lift of this square is a lift of i with respect to g ∘ f
    ⟨⟨⟨(arrow.lift sq2 : _ ⟶ _), by simp⟩⟩⟩ }

/-- The objects of the subcategory `right_lifting_subcategory` are the ones in the
underlying category. -/
def right_lifting_subcat (R : Type u) := R

instance right_lifting_subcat.inhabited  (R : Type u) [inhabited R] :
  inhabited (right_lifting_subcat R) :=
{ default := (default R : R) }

/-- The objects of the subcategory `right_lifting_subcategory` are the ones in the
underlying category. -/
def right_lifting_subcat.X {R : Type u} (x : right_lifting_subcat R) : R := x

lemma id_has_right_lifting_property' {F : D → arrow C} (X : C) :
  ∀ i : D, has_lifting_property (F i) (arrow.mk (𝟙 X)) :=
λ i, id_has_right_lifting_property (F i)

lemma has_right_lifting_property_comp'
  {F : D → arrow C} {f : X ⟶ Y} (hf : ∀ i : D, has_lifting_property (F i) (arrow.mk f))
  {g : Y ⟶ Z} (hg : ∀ i : D, has_lifting_property (F i) (arrow.mk g)) :
  ∀ i : D,  has_lifting_property (F i) (arrow.mk (f ≫ g)) :=
λ i, has_right_lifting_property_comp (hf i) (hg i)

/-- Given a set of arrows in C, indexed by `F : D → arrow C`,
we construct the (non-full) subcategory of `C`
spanned by those morphisms that have the right lifting property relative to all maps
of the form `F i`, where `i` is any element in `D`. -/
def right_lifting_subcategory (F : D → arrow C) : category (right_lifting_subcat C) :=
{ hom := λ X Y, { p : X ⟶ Y // ∀ {i : D}, has_lifting_property (F i) (arrow.mk p) },
  id := λ X, ⟨𝟙 X, id_has_right_lifting_property' X⟩,
  comp := λ X Y Z f g, ⟨f.val ≫ g.val, has_right_lifting_property_comp' f.property g.property⟩ }

end category_theory
