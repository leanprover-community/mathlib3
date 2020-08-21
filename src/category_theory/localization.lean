/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import category_theory.category
import category_theory.equivalence
import category_theory.arrow

/-!

# Localization of a Category

Given a category `C` and a set `S` of arrows in `C`, we construct the localization of `C` with
respect to `S`. This is the initial category with a functor from `C` in which all the members
of `S` become isomorphisms.

# Notation/Constructions

The localization of `C` at `S` is denoted `localize S`, and is endowed with a canonical functor
`ι S : C ⥤ localize S`. Given any functor `F : C ⥤ D` and a proof `cond` that for every `f ∈ S`,
`F.map f.hom` is an isomorphism in `D`, there is a unique lift
`lift F cond : localize S ⥤ D` whose composition with `ι S` is `F`.

Note: In these statements, we use isomorphisms of functors as opposed to equality!

We also provide an `is_iso ((ι S).map f.hom)` given a proof `h` of `f ∈ S`. This is denoted
`iso_of_mem h`.

-/

universes v₁ v₂ u₁ u₂

namespace category_theory

variables {C : Type u₁} [category.{v₁} C] (S : set (arrow C))

include S
/-- The objects of the localization of `C` are the same as those of `C`. -/
@[nolint unused_arguments]
def localize := C

namespace localize
variable {S}

instance [I : inhabited C] : inhabited (localize S) := I

/-- An auxiliary inductive type used to define morphisms in `localize S`. -/
inductive prehom : localize S → localize S → Type (max u₁ v₁)
| of {X Y : C} : (X ⟶ Y) → prehom X Y
| inv {f : arrow C} : f ∈ S → prehom f.right f.left
| comp {X Y Z : C} : prehom X Y → prehom Y Z → prehom X Z
namespace prehom

instance {X : localize S} : inhabited (prehom X X) := ⟨of (𝟙 _)⟩

/-- A relation on `prehom X Y` the quotient by which will be the `hom` for `localize S`. -/
inductive rel : Π {X Y : localize S}, prehom X Y → prehom X Y → Prop
| of_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : rel (of $ f ≫ g) (comp (of f) (of g))
| self_comp_inv {f : arrow C} (h : f ∈ S) : rel (comp (of f.hom) (inv h)) (of $ 𝟙 _)
| inv_comp_self {f : arrow C} (h : f ∈ S) : rel (comp (inv h) (of f.hom)) (of $ 𝟙 _)
| id_comp {X Y : localize S} (f : prehom X Y) : rel (comp (of $ 𝟙 _) f) f
| comp_id {X Y : localize S} (f : prehom X Y) : rel (comp f (of $ 𝟙 _)) f
| assoc {X Y Z W : localize S} (f : prehom X Y) (g : prehom Y Z) (h : prehom Z W) :
    rel (comp (comp f g) h) (comp f (comp g h))
| compat_comp_left {X Y Z : localize S} {f g : prehom X Y} {h : prehom Y Z} :
    rel f g → rel (comp f h) (comp g h)
| compat_comp_right {X Y Z : localize S} {f : prehom X Y} {g h : prehom Y Z} :
    rel g h → rel (comp f g) (comp f h)
end prehom

/-- The morphisms in `localize S` are given as the quotient of `prehom X Y` by `prehom.rel`. -/
def hom (X Y : localize S) := quot (@prehom.rel _ _ _ X Y)
namespace hom

/-- The composition of two morphisms in `localize S`. -/
def comp {X Y Z : localize S} (f : hom X Y) (g : hom Y Z) : hom X Z :=
  quot.lift_on₂ f g (λ f' g', quot.mk prehom.rel $ prehom.comp f' g')
  (λ _ _ _ h, quot.sound (prehom.rel.compat_comp_right h))
  (λ _ _ _ h, quot.sound (prehom.rel.compat_comp_left h))

/-- The identity morphisms in `localize S`. -/
def id (X : localize S) : hom X X := quot.mk prehom.rel $ prehom.of $ 𝟙 _

instance {X : localize S} : inhabited (hom X X) := ⟨id _⟩

@[simp] lemma id_comp {X Y : localize S} (f : hom X Y) : (id _).comp f = f :=
by {rcases f, exact quot.sound (prehom.rel.id_comp _)}
@[simp] lemma comp_id {X Y : localize S} (f : hom X Y) : f.comp (id _) = f :=
by {rcases f, exact quot.sound (prehom.rel.comp_id _)}
@[simp] lemma assoc {X Y Z W : localize S} (f : hom X Y) (g : hom Y Z) (h : hom Z W) :
  (f.comp g).comp h = f.comp (g.comp h) :=
by { rcases f, rcases g, rcases h, exact quot.sound (prehom.rel.assoc _ _ _)}

/-- Any morphism in `C` gives a corresponding morphism in `localize S`. -/
def of {X Y : C} (f : X ⟶ Y) : @hom _ _ S X Y := quot.mk prehom.rel $ prehom.of f

@[simp] lemma of_id {X : C} : @of _ _ S _ _ (𝟙 _) = id X := rfl
@[simp] lemma of_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  @of _ _ S _ _ (f ≫ g) = (of f).comp (of g) := quot.sound (prehom.rel.of_comp _ _)

end hom

instance : category (localize S) :=
{ hom := hom,
  id := hom.id,
  comp := @hom.comp _ _ _ }

variable (S)
/-- The canonical functor from `C` to its localization at `S`. -/
def ι : C ⥤ localize S :=
{ obj := λ X, X,
  map := @hom.of _ _ _ }
variable {S}

/-- Given `f ∈ S`, the image of `f` in `localize S` is an isomorphism. -/
def iso_of_mem {f : arrow C} (h : f ∈ S) : is_iso ((ι S).map f.hom) :=
{ inv := quot.mk prehom.rel (prehom.inv h),
  hom_inv_id' := quot.sound (prehom.rel.self_comp_inv _),
  inv_hom_id' := quot.sound (prehom.rel.inv_comp_self _) }

/-- An auxiliary function used to define `lift`. -/
@[simp]
def lift_func {D : Type u₂} [category.{v₂} D] {X Y : localize S} (F : C ⥤ D)
  (cond : ∀ f, f ∈ S → is_iso (F.map $ comma.hom f)) :
  (prehom X Y) →  (F.obj X ⟶ F.obj Y) := @prehom.rec _ _ S (λ X Y _, F.obj X ⟶ F.obj Y)
  (F.map) (λ f h, @is_iso.inv _ _ _ _ (F.map f.hom) (cond _ h))
  (λ _ _ _ _ _ f g, f ≫ g) _ _
local attribute [reducible] lift_func


/--
Given a functor `F : C ⥤ D` and a proof that `F` maps every member of `S` to an isomorhpism,
this provides a lift of `F` to a functor `localize S ⥤ D`.
-/
@[simps]
def lift {D : Type u₂} [category.{v₂} D] (F : C ⥤ D)
  (cond : ∀ f ∈ S, is_iso $ F.map $ comma.hom f) : (localize S ⥤ D) :=
{ obj := λ X, F.obj X,
  map := λ X Y, quot.lift (lift_func F cond)
  begin
    intros f g r,
    induction r,
    tidy,
  end,
  map_id' := begin
    intros X,
    change F.map _ = _,
    simp,
  end }

/--
The composition of `lift F cond` with `ι S` is isomorphic to `F`.
-/
@[simps] def lift_comp_ι {D : Type u₂} [category.{v₂} D] {F : C ⥤ D}
  (h : ∀ f ∈ S, is_iso $ F.map $ comma.hom f) : (ι S ⋙ lift F h) ≅ F :=
{ hom := { app := λ _, 𝟙 _ },
  inv := { app := λ _, 𝟙 _ } }

/--
If the composition of `G : localize S ⥤ D` with `ι S` is isomorphic to `F`, then
`G` is isomorphic to `lift F cond`.
-/
@[simps] def lift_unique {D : Type u₂} [category.{v₂} D] {F : C ⥤ D}
  (cond : ∀ f ∈ S, is_iso $ F.map $ comma.hom f) (G : localize S ⥤ D)
  (equiv : ι S ⋙ G ≅ F) : G ≅ lift F cond :=
{ hom :=
  { app := λ X, equiv.hom.app X,
    naturality' := begin
      intros X Y f,
      rcases f, induction f,
      { change G.map ((ι S).map _) ≫ _ = _,
        change _ = _ ≫ (lift F cond).map ((ι S).map f_a),
        simp_rw [←functor.comp_map],
        apply equiv.hom.naturality },
      { letI := cond _ f_a,
        letI := iso_of_mem f_a,
        change G.map (inv ((ι S).map f_f.hom)) ≫ _ = _,
        change _ = _ ≫ (lift F cond).map (inv ((ι S).map f_f.hom)),
        simp_rw functor.map_inv,
        have : equiv.hom.app f_f.left = inv (equiv.inv.app _), by refl, rw this, clear this,
        have : equiv.hom.app f_f.right = inv (equiv.inv.app _), by refl, rw this, clear this,
        simp_rw ←is_iso.inv_comp,
        rw is_iso.inv_eq_inv,
        symmetry,
        simp_rw [←functor.comp_map],
        apply equiv.inv.naturality },
      { change  _ = _ ≫ ((lift F cond).map (quot.mk _ f_a) ≫ (lift F cond).map (quot.mk _ f_a_1)),
        rw [←category.assoc,←f_ih_a,category.assoc,←f_ih_a_1,←category.assoc],
        suffices : G.map (quot.mk prehom.rel (f_a.comp f_a_1)) =
          G.map (quot.mk prehom.rel f_a) ≫ G.map (quot.mk prehom.rel f_a_1), by rw this,
        rw ←functor.map_comp,
        refl }
    end },
  inv :=
  { app := λ X, equiv.inv.app X,
    naturality' := begin
      intros X Y f,
      rcases f, induction f,
      { change _ = _ ≫ G.map ((ι S).map _),
        change (lift F cond).map ((ι S).map f_a) ≫ _ = _,
        simp_rw [←functor.comp_map],
        apply equiv.inv.naturality },
      { letI := cond _ f_a,
        letI := iso_of_mem f_a,
        change _ = _ ≫ G.map (inv ((ι S).map f_f.hom)),
        change (lift F cond).map (inv ((ι S).map f_f.hom)) ≫ _ = _,
        simp_rw functor.map_inv,
        have : equiv.inv.app f_f.left = inv (equiv.hom.app _), by refl, rw this, clear this,
        have : equiv.inv.app f_f.right = inv (equiv.hom.app _), by refl, rw this, clear this,
        simp_rw ←is_iso.inv_comp,
        rw is_iso.inv_eq_inv,
        symmetry,
        simp_rw [←functor.comp_map],
        apply equiv.hom.naturality },
      { change ((lift F cond).map (quot.mk _ _) ≫ (lift F cond).map (quot.mk _ _)) ≫ _ = _,
        rw [category.assoc,f_ih_a_1,←category.assoc,f_ih_a,category.assoc],
        suffices : G.map (quot.mk prehom.rel f_a) ≫ G.map (quot.mk prehom.rel f_a_1) =
          G.map (quot.mk prehom.rel (f_a.comp f_a_1)), by rw this,
        rw ←functor.map_comp,
        refl },
    end } }

end localize
end category_theory
