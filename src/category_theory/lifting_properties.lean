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
- `right_lifting_property_initial_iff`: spells out the rlp against a map whose source is an
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

/-- The lifting property of a morphism `i` vs. a morphism `p`. This can be interpreted as the
right lifting property of `i` vs. `p`, or the left lifting property of `p` vs. `i`. -/
def has_lifting_property (i p : arrow C) : Prop := ∀ (sq : i ⟶ p), arrow.has_lift sq

/-X Y : C,
i : arrow C,
p : X ≅ Y,
sq : i ⟶ arrow.mk p.hom
⊢ i.hom ≫ sq.right ≫ p.inv = sq.left-/


/-- Any isomorphism has the right lifting property with respect to any map.
A    → X
↓i    ↓p≅
B    → Y
-/
lemma iso_has_right_lifting_property (i : arrow C) (p : X ≅ Y) :
  has_lifting_property i (arrow.mk p.hom) :=
λ sq, ⟨⟨{ lift := sq.right ≫ p.inv, }⟩⟩
--⟨⟨⟨sq.right ≫ p.inv, by { rw [←category.assoc, (arrow.w sq).symm], simp, }, by simp⟩⟩⟩
-- the lift is obtained by p⁻¹ ∘ (B → Y)

/-- Any identity has the right lifting property with respect to any map. -/
lemma id_has_right_lifting_property (i : arrow C) : has_lifting_property i (arrow.mk (𝟙 X)) :=
  iso_has_right_lifting_property i (iso.refl _)

/-- An equivalent characterization for right lifting against a map `i` whose source is initial.
∅ → X
↓   ↓
B → Y has a lifting iff there is a map B → X making the right part commute.
-/
lemma right_lifting_property_initial_iff (i p : arrow C)
  (h : is_initial i.left) :
  has_lifting_property i p ↔ ∀ {e : i.right ⟶ p.right}, ∃ l : i.right ⟶ p.left, l ≫ p.hom = e :=
begin
  fsplit,
  { intros hlift bottom,
    have comm : (is_initial.to h p.left) ≫ p.hom = i.hom ≫ bottom :=
      is_initial.hom_ext h _ _,
    haveI := hlift (arrow.hom_mk comm),
    use arrow.lift (arrow.hom_mk comm),
    simp },
  { intros h1 sq,
    cases h1 with e he,
    refine ⟨⟨{lift := e, fac_left' := _}⟩⟩,
    apply is_initial.hom_ext, simpa using h },
end

/-- The condition of having the rlp with respect to a morphism `i` is stable under composition-/
lemma has_right_lifting_property_comp {i : arrow C} {f : X ⟶ Y} {g : Y ⟶ Z}
  (hf : has_lifting_property i (arrow.mk f))
  (hg : has_lifting_property i (arrow.mk g)) :
  has_lifting_property i (arrow.mk (f ≫ g)) :=
begin
  intro sq0, -- a square between i and f ≫ g
  let sq1 := arrow.square_to_snd sq0, -- transform this into a square between i and g

  -- lift i vs. g
  haveI := hg sq1,

  -- form a square from i to f, using the previously constructed lift
  have h3 : sq0.left ≫ (arrow.mk f).hom = i.hom ≫ (arrow.has_lift.struct sq1).lift :=
  begin
    rw (arrow.has_lift.struct sq1).fac_left,
    refl,
  end,

  -- construct a square i ⟶ f
  let sq2 : i ⟶ (arrow.mk f) :=
  { left := sq0.left,
    right := (arrow.has_lift.struct sq1).lift },

  -- construct a lift i vs. f
  haveI := hf sq2,

  -- show that this lift is a lift of i vs. g ∘ f
  refine ⟨⟨{lift := (arrow.has_lift.struct sq2).lift, fac_right' := _}⟩⟩,
  { have : sq0.right = sq1.right := rfl,
    rw this,
    simp only [arrow.mk_hom],
    rw ←category.assoc,
    rw ←((arrow.has_lift.struct sq1).fac_right),
    simp only [arrow.mk_hom],
    let d := (arrow.has_lift.struct sq2).fac_right,
    simp only [arrow.mk_hom] at d,
    rw d }
end

variable {F : D → arrow C}

/-- Right lifting conditions relative to a set of arrows in `C`. -/
def right_lifting_property_rel (p : X ⟶ Y) : Prop :=
  ∀ i : D, has_lifting_property (F i) (arrow.mk p)

lemma id_has_right_lifting_property' (X : C) :
  ∀ i : D, has_lifting_property (F i) (arrow.mk (𝟙 X)) :=
λ i, id_has_right_lifting_property (F i)

lemma has_right_lifting_property_comp'
  {f : X ⟶ Y} (hf : ∀ i : D, has_lifting_property (F i) (arrow.mk f))
  {g : Y ⟶ Z} (hg : ∀ i : D, has_lifting_property (F i) (arrow.mk g)) :
  ∀ i : D,  has_lifting_property (F i) (arrow.mk (f ≫ g)) :=
λ i, has_right_lifting_property_comp (hf i) (hg i)

/-- Given a set of arrows in C, indexed by `F : D → arrow C`,
we construct the (non-full) subcategory of `C`
spanned by those morphisms that have the right lifting property relative to all maps
of the form `F i`, where `i` is any element in `D`. -/
def right_lifting_subcat (F : D → arrow C) := C

/--The objects of this subcategory are the ones of `C`. -/
def right_lifting_subcat.X (x : right_lifting_subcat F) : C := x

instance : category (right_lifting_subcat F) :=
{ hom := λ X Y, { p : X.X ⟶ Y.X //
    ∀ {i : D}, has_lifting_property (F i) (arrow.mk p) },
  id := λ X, ⟨𝟙 X.X, id_has_right_lifting_property' X⟩,
  comp := λ X Y Z f g, ⟨f.val ≫ g.val,
    begin intro i, apply has_right_lifting_property_comp' f.property g.property end⟩ }

end category_theory
