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

universes v u
variables {C : Type u} [category.{v} C]

-- TODO: Move this to arrow file.
@[simp]
lemma arrow.coe_hom_eq {a b : C} (f : a ⟶ b) : (f : arrow C).hom = f := rfl

class has_lifting_property (l r : arrow C) : Prop :=
(has_lift : ∀ sq : l ⟶ r, arrow.has_lift sq)

instance arrow.has_lift.of_has_lifting_property {l r : arrow C}
  [has_lifting_property l r] (sq : l ⟶ r) : arrow.has_lift sq :=
has_lifting_property.has_lift sq

instance has_lifting_property.of_is_iso_left {a b : C} (l : a ⟶ b) [is_iso l] (r : arrow C) :
  has_lifting_property ↑l r :=
{ has_lift := λ sq, { exists_lift := nonempty.intro { lift := inv l ≫ sq.left } } }

instance has_lifting_property.of_is_iso_left' (l r : arrow C) [is_iso l.hom] :
  has_lifting_property l r :=
{ has_lift := λ sq, { exists_lift := nonempty.intro { lift := inv l.hom ≫ sq.left } } }

instance has_lifting_property.of_is_iso_right (l : arrow C) {a b : C} (r : a ⟶ b) [is_iso r] :
  has_lifting_property l r :=
{ has_lift := λ sq, { exists_lift := nonempty.intro
  { lift := sq.right ≫ inv r,
    fac_left' := by { rw [← category.assoc, is_iso.comp_inv_eq], simp } } } }

instance has_lifting_property.of_is_iso_right' (l r : arrow C) [is_iso r.hom] :
  has_lifting_property l r :=
{ has_lift := λ sq, { exists_lift := nonempty.intro
  { lift := sq.right ≫ inv r.hom,
    fac_left' := by { rw [← category.assoc, is_iso.comp_inv_eq], simp } } } }

instance has_lifting_property.of_comp_left (r : arrow C) {a b c : C} (l1 : a ⟶ b) (l2 : b ⟶ c)
  [has_lifting_property ↑l1 r] [has_lifting_property ↑l2 r] :
  has_lifting_property ↑(l1 ≫ l2) r :=
{ has_lift := λ sq, { exists_lift := nonempty.intro
  { lift := let
      sq1 : (l1 : arrow C) ⟶ r := ⟨sq.left, l2 ≫ sq.right⟩,
      lift1 := arrow.lift sq1,
      sq2 : (l2 : arrow C) ⟶ r := ⟨lift1, sq.right⟩,
      lift2 := arrow.lift sq2 in lift2 } } }

instance has_lifting_property.of_comp_right (l : arrow C) {a b c : C} (r1 : a ⟶ b) (r2 : b ⟶ c)
  [has_lifting_property l r1] [has_lifting_property l r2] : has_lifting_property l (r1 ≫ r2) :=
{ has_lift := λ sq, { exists_lift := nonempty.intro
  { lift := let
      sq2 : l ⟶ r2 := ⟨sq.left ≫ r1, sq.right⟩,
      lift2 := arrow.lift sq2,
      sq1 : l ⟶ r1 := ⟨sq.left, lift2⟩,
      lift1 := arrow.lift sq1 in lift1 } } }

example {a b : C} (f : a ≅ b) (r : arrow C) : has_lifting_property (f.hom : arrow C) r :=
by apply_instance

example {a : C} (r : arrow C) : has_lifting_property (𝟙 a : arrow C) r :=
by apply_instance

example {a b : C} (f : a ≅ b) (l : arrow C) : has_lifting_property l f.hom :=
by apply_instance

example {a : C} (l : arrow C) : has_lifting_property l (𝟙 a) :=
by apply_instance

lemma has_lifting_property_of_initial {a b : C} (l : a ⟶ b) (r : arrow C) (ha : is_initial a) :
  has_lifting_property ↑l r ↔ ∀ (e : b ⟶ r.right), ∃ (g : b ⟶ r.left), g ≫ r.hom = e :=
begin
  fsplit,
  { introsI hlift e,
    have comm : (ha.to r.left) ≫ r.hom = l ≫ e := ha.hom_ext _ _,
    use arrow.lift (arrow.hom_mk comm : (l : arrow C) ⟶ r),
    simp },
  { refine λ hlift, ⟨λ sq, _⟩,
    obtain ⟨l, hl⟩ : ∃ (l : b ⟶ r.left), l ≫ r.hom = sq.right := hlift _,
    exact arrow.has_lift.mk ⟨l, ha.hom_ext _ _, hl⟩, }
end

lemma has_lifting_property_of_terminal (l : arrow C) {a b : C} (r : a ⟶ b) (hb : is_terminal b) :
  has_lifting_property l r ↔ ∀ (e : l.left ⟶ a), ∃ (g : l.right ⟶ a), l.hom ≫ g = e :=
begin
  fsplit,
  { introsI hlift e,
    have comm : e ≫ r = l.hom ≫ (hb.from l.right) := hb.hom_ext _ _,
    use arrow.lift (arrow.hom_mk comm : l ⟶ r),
    simp },
  { refine λ hlift, ⟨λ sq, _⟩,
    obtain ⟨r, hr⟩ : ∃ (g : l.right ⟶ a), l.hom ≫ g = sq.left := hlift _,
    exact arrow.has_lift.mk ⟨r, hr, hb.hom_ext _ _⟩ }
end

section right_lifting_subcat

def right_lifting {D} (L : D → arrow C) := C

namespace right_lifting

variables {D : Type*} {L : D → arrow C}

def of (X : C) : right_lifting L := X

def drop (X : right_lifting L) : C := X

@[ext]
structure hom (X Y : right_lifting L) :=
(to_hom : X.drop ⟶ Y.drop)
[str : ∀ (l : D), has_lifting_property (L l) to_hom]

namespace hom
instance foo {X Y : right_lifting L} (f : hom X Y) (x : D) :
  has_lifting_property (L x) f.to_hom :=
f.str _
end hom

@[simps]
instance : category (right_lifting L) :=
{ hom := hom,
  id := λ X, ⟨𝟙 _⟩,
  comp := λ X Y Z f g, ⟨f.to_hom ≫ g.to_hom⟩ }

end right_lifting

end right_lifting_subcat

section left_lifting_subcat

def left_lifting {D} (R : D → arrow C) := C

namespace left_lifting

variables {D : Type*} {R : D → arrow C}

def of (X : C) : left_lifting R := X

def drop (X : left_lifting R) : C := X

@[ext]
structure hom (X Y : left_lifting R) :=
(to_hom : X.drop ⟶ Y.drop)
[str : ∀ (l : D), has_lifting_property ↑to_hom (R l)]

namespace hom
instance foo {X Y : left_lifting R} (f : hom X Y) (x : D) :
  has_lifting_property ↑f.to_hom (R x) :=
f.str _
end hom

@[simps]
instance : category (left_lifting R) :=
{ hom := hom,
  id := λ X, ⟨𝟙 _⟩,
  comp := λ X Y Z f g, ⟨f.to_hom ≫ g.to_hom⟩ }

end left_lifting

end left_lifting_subcat

end category_theory
