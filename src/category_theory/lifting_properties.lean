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

This file defines the lifting property of two arrows in a category and show basic properties of
this notion.
We also construct the subcategory consisting of those morphisms which have the right lifting
property with respect to arrows in a given diagram.

## Main results
- `has_lifting_property`: the definition of the lifting property
- `iso_has_right_lifting_property`: any isomorphism satisfies the right lifting property (rlp)
- `id_has_right_lifting_property`: any identity has the rlp
- `right_lifting_property_initial_iff`: spells out the rlp against a map whose source is an
initial object
- `right_lifting_subcat`: given a functor F : D ⥤ arrow C, we construct the subcategory of those
morphisms p in C that satisfy the rlp w.r.t. F(i), for any object i in D.

## Tags
lifting property
-/

namespace category_theory

universes v u
variables {C : Type u} [category.{v} C]
variables {D : Type u} [category.{v} D]

variables {X Y Z : C}

/- The left lifting property of a morphism i vs. a morphism p. -/
def has_lifting_property (i p : arrow C) : Prop := ∀ (sq : i ⟶ p), arrow.has_lift sq

/- Any isomorphism has the right lifting property with respect to any map.
A    → X
↓i    ↓p≅
B    → Y
-/
lemma iso_has_right_lifting_property (i : arrow C) (p : X ≅ Y) :
has_lifting_property i (arrow.mk p.hom) :=
begin
  intro sq,
  fconstructor,
  fconstructor,
  fconstructor,
  { use sq.right ≫ p.inv }, -- the lift is obtained by p⁻¹ ∘ (B → Y)
  { rw [←category.assoc, (arrow.w sq).symm],
    simp, },
  { simp, }
end

/- Any identity has the right lifting property with respect to any map. -/
lemma id_has_right_lifting_property (i : arrow C) : has_lifting_property i (arrow.mk (𝟙 X)) :=
begin
  haveI := is_iso.id X,
  exact iso_has_right_lifting_property i (category_theory.as_iso (𝟙 X)),
end

/- An equivalent characterization for right lifting against a map i whose source is initial.
∅ → X
↓   ↓
B → Y has a lifting iff there is a map B → X making the right part commute.
-/
lemma right_lifting_property_initial_iff (i p : arrow C)
(h : category_theory.limits.is_initial i.left) :
has_lifting_property i p ↔ ∀ {e : i.right ⟶ p.right}, ∃ l : i.right ⟶ p.left, l ≫ p.hom = e :=
begin
  split,
  { intros hlift bottom,
    have comm : (category_theory.limits.is_initial.to h p.left) ≫ p.hom = i.hom ≫ bottom :=
    begin apply category_theory.limits.is_initial.hom_ext h, end,
    haveI := hlift (arrow.hom_mk comm),
    use (arrow.has_lift.struct (arrow.hom_mk comm)).lift,
    rw (arrow.has_lift.struct (arrow.hom_mk comm)).fac_right,
    refl },
  { intros h1 sq,
    cases h1 with e he,
    fconstructor,
    fconstructor,
    fconstructor, }
end

/- A helper construction: given a square between i and f ≫ g, produce a square between i and g,
whose top leg uses f:
A  → X
     ↓f
↓i   Y             --> A → Y
     ↓g                ↓i  ↓g
B  → Z                 B → Z
 -/
@[simps] def square_to_second {i : arrow C} {f : X ⟶ Y} {g : Y ⟶ Z} (sq : i ⟶ arrow.mk (f ≫ g)) :
i ⟶ arrow.mk g :=
{ left := sq.left ≫ f,
  right := sq.right,
  w' := begin
    have : sq.left ≫ f ≫ g = i.hom ≫ sq.right := arrow.w sq,
    rw ←category.assoc at this,
    tidy,
  end
}

/- The condition of having the rlp with respect to a morphism i is stable under composition-/
lemma has_right_lifting_property_comp {i : arrow C} {f : X ⟶ Y} {g : Y ⟶ Z}
(hf : has_lifting_property i (arrow.mk f))
(hg : has_lifting_property i (arrow.mk g)) :
has_lifting_property i (arrow.mk (f ≫ g)) :=
begin
  intro sq0, -- a square between i and f ≫ g
  let sq1 := square_to_second sq0, -- transform this into a square between i and g

  -- lift i vs. g
  haveI := hg sq1,
  have lift_structure_sq1 := arrow.has_lift.struct sq1,
  have sq1_lift := arrow.lift sq1,

  -- form a square from i to f, using the previously constructed lift
  have h3 : sq0.left ≫ (arrow.mk f).hom = i.hom ≫ lift_structure_sq1.lift :=
  begin
    rw lift_structure_sq1.fac_left,
    refl,
  end,

  -- construct a square i ⟶ f
  let sq2 : i ⟶ (arrow.mk f) :=
  {
    left := sq0.left,
    right := lift_structure_sq1.lift,
    w' := begin
      simp,
      tidy,
    end,
  },

  -- construct a lift i vs. f
  haveI := hf sq2,
  have lift_structure_sq2 := arrow.has_lift.struct sq2,
  have sq2_lift := arrow.lift sq2,

  -- show that this lift is a lift of i vs. g ∘ f
  fconstructor,
  fconstructor,
  fconstructor,
  { simp, exact lift_structure_sq2.lift, },
  { simp,  },
  { simp, tidy,
    rw ←category.assoc,
    let d := lift_structure_sq2.fac_right,
    let d' := lift_structure_sq1.fac_right,
    have : sq0.right = sq1.right := begin tidy, end,
    rw this,
    rw ←d',
    tidy,
    rw ←category.assoc,
    rw d,
  },
end

/- Right lifting conditions relative to a diagram of arrows in C. -/
variable {F : D ⥤ arrow C}

def right_lifting_property_rel (p : X ⟶ Y) : Prop :=
∀ i : D, has_lifting_property ((F.obj) i) (arrow.mk p)

lemma id_has_right_lifting_property' (X : C) :
∀ i : D, has_lifting_property ((F.obj) i) (arrow.mk (𝟙 X)) :=
begin
  intro i,
  exact id_has_right_lifting_property ((F.obj) i),
end

lemma has_right_lifting_property_comp'
{f : X ⟶ Y} (hf : ∀ i : D, has_lifting_property ((F.obj) i) (arrow.mk f))
{g : Y ⟶ Z} (hg : ∀ i : D, has_lifting_property ((F.obj) i) (arrow.mk g)) :
∀ i : D,  has_lifting_property ((F.obj) i) (arrow.mk (f ≫ g)) :=
begin
  intro i,
  exact has_right_lifting_property_comp (hf i) (hg i),
end

/- Given a diagram of arrows in C, F : D ⥤ arrow C, we construct the (non-full) subcategory of C
spanned by those morphisms that have the right lifting property relative to all maps
of the form F(i), where i is any object in D. Its objects are the same as the one of C. -/
def right_lifting_subcat (F : D ⥤ arrow C) := C
def right_lifting_subcat.X (x : right_lifting_subcat F) : C := x

instance : category (right_lifting_subcat F) :=
{ hom := λ X Y, { p : X.X ⟶ Y.X //
    ∀ {i : D}, has_lifting_property ((F.obj) i) (arrow.mk p) },
  id := λ X, ⟨ 𝟙 X, id_has_right_lifting_property' X, ⟩,
  comp := λ X Y Z f g, ⟨f.val ≫ g.val,
    begin intro i, apply has_right_lifting_property_comp' f.property g.property end ⟩,
  id_comp' := λ X Y f, begin tidy, apply category.id_comp, end,
  comp_id' := λ _ _ _, begin tidy, apply category.comp_id, end,
  assoc' := λ _ _ _ _ _ _ _, begin tidy, end }

end category_theory
