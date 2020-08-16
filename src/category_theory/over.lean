/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Bhavik Mehta
-/
import category_theory.comma
import category_theory.punit
import category_theory.reflects_isomorphisms

/-!
# Over and under categories

Over (and under) categories are special cases of comma categories.
* If `L` is the identity functor and `R` is a constant functor, then `comma L R` is the "slice" or
  "over" category over the object `R` maps to.
* Conversely, if `L` is a constant functor and `R` is the identity functor, then `comma L R` is the
  "coslice" or "under" category under the object `L` maps to.

## Tags

comma, slice, coslice, over, under
-/

namespace category_theory

universes v₁ v₂ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation
variables {T : Type u₁} [category.{v₁} T]

/-- The over category has as objects arrows in `T` with codomain `X` and as morphisms commutative
    triangles. -/
@[derive category]
def over (X : T) := comma.{v₁ 0 v₁} (𝟭 T) (functor.from_punit X)

-- Satisfying the inhabited linter
instance over.inhabited [inhabited T] : inhabited (over (default T)) :=
{ default :=
  { left := default T,
    hom := 𝟙 _ } }

namespace over

variables {X : T}

@[ext] lemma over_morphism.ext {X : T} {U V : over X} {f g : U ⟶ V}
  (h : f.left = g.left) : f = g :=
by tidy

@[simp] lemma over_right (U : over X) : U.right = punit.star := by tidy

@[simp] lemma id_left (U : over X) : comma_morphism.left (𝟙 U) = 𝟙 U.left := rfl
@[simp] lemma comp_left (a b c : over X) (f : a ⟶ b) (g : b ⟶ c) :
  (f ≫ g).left = f.left ≫ g.left := rfl

@[simp, reassoc] lemma w {A B : over X} (f : A ⟶ B) : f.left ≫ B.hom = A.hom :=
by have := f.w; tidy

/-- To give an object in the over category, it suffices to give a morphism with codomain `X`. -/
@[simps]
def mk {X Y : T} (f : Y ⟶ X) : over X :=
{ left := Y, hom := f }

/-- To give a morphism in the over category, it suffices to give an arrow fitting in a commutative
    triangle. -/
@[simps]
def hom_mk {U V : over X} (f : U.left ⟶ V.left) (w : f ≫ V.hom = U.hom . obviously) :
  U ⟶ V :=
{ left := f }

/--
Construct an isomorphism in the over category given isomorphisms of the objects whose forward
direction gives a commutative triangle.
-/
def iso_mk {f g : over X} (hl : f.left ≅ g.left) (hw : hl.hom ≫ g.hom = f.hom) : f ≅ g :=
comma.iso_mk hl (eq_to_iso (subsingleton.elim _ _)) (by simp [hw])

@[simp]
lemma iso_mk_hom_left {f g : over X} (hl : f.left ≅ g.left) (hw : hl.hom ≫ g.hom = f.hom) :
  (iso_mk hl hw).hom.left = hl.hom := rfl

@[simp]
lemma iso_mk_inv_left {f g : over X} (hl : f.left ≅ g.left) (hw : hl.hom ≫ g.hom = f.hom) :
  (iso_mk hl hw).inv.left = hl.inv := rfl

/-- The forgetful functor mapping an arrow to its domain. -/
def forget : over X ⥤ T := comma.fst _ _

@[simp] lemma forget_obj {U : over X} : forget.obj U = U.left := rfl
@[simp] lemma forget_map {U V : over X} {f : U ⟶ V} : forget.map f = f.left := rfl

/-- A morphism `f : X ⟶ Y` induces a functor `over X ⥤ over Y` in the obvious way. -/
def map {Y : T} (f : X ⟶ Y) : over X ⥤ over Y := comma.map_right _ $ discrete.nat_trans (λ _, f)

section
variables {Y : T} {f : X ⟶ Y} {U V : over X} {g : U ⟶ V}
@[simp] lemma map_obj_left : ((map f).obj U).left = U.left := rfl
@[simp] lemma map_obj_hom  : ((map f).obj U).hom  = U.hom ≫ f := rfl
@[simp] lemma map_map_left : ((map f).map g).left = g.left := rfl

/-- Mapping by the identity morphism is just the identity functor. -/
def map_id : map (𝟙 Y) ≅ 𝟭 _ :=
nat_iso.of_components (λ X, iso_mk (iso.refl _) (by tidy)) (by tidy)

/-- Mapping by the composite morphism `f ≫ g` is the same as mapping by `f` then by `g`. -/
def map_comp {Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map f ⋙ map g :=
nat_iso.of_components (λ X, iso_mk (iso.refl _) (by tidy)) (by tidy)

end

instance forget_reflects_iso : reflects_isomorphisms (forget : over X ⥤ T) :=
{ reflects := λ X Y f t, by exactI
  { inv := over.hom_mk t.inv ((as_iso (forget.map f)).inv_comp_eq.2 (over.w f).symm) } }

section iterated_slice
variables (f : over X)

/-- Given f : Y ⟶ X, this is the obvious functor from (T/X)/f to T/Y -/
@[simps]
def iterated_slice_forward : over f ⥤ over f.left :=
{ obj := λ α, over.mk α.hom.left,
  map := λ α β κ, over.hom_mk κ.left.left (by { rw auto_param_eq, rw ← over.w κ, refl }) }

/-- Given f : Y ⟶ X, this is the obvious functor from T/Y to (T/X)/f -/
@[simps]
def iterated_slice_backward : over f.left ⥤ over f :=
{ obj := λ g, mk (hom_mk g.hom : mk (g.hom ≫ f.hom) ⟶ f),
  map := λ g h α, hom_mk (hom_mk α.left (w_assoc α f.hom)) (over_morphism.ext (w α)) }

/-- Given f : Y ⟶ X, we have an equivalence between (T/X)/f and T/Y -/
@[simps]
def iterated_slice_equiv : over f ≌ over f.left :=
{ functor := iterated_slice_forward f,
  inverse := iterated_slice_backward f,
  unit_iso :=
    nat_iso.of_components
    (λ g, over.iso_mk (over.iso_mk (iso.refl _) (by tidy)) (by tidy))
    (λ X Y g, by { ext, dsimp, simp }),
  counit_iso :=
    nat_iso.of_components
    (λ g, over.iso_mk (iso.refl _) (by tidy))
    (λ X Y g, by { ext, dsimp, simp }) }

lemma iterated_slice_forward_forget :
  iterated_slice_forward f ⋙ forget = forget ⋙ forget :=
rfl

lemma iterated_slice_backward_forget_forget :
  iterated_slice_backward f ⋙ forget ⋙ forget = forget :=
rfl

end iterated_slice

section
variables {D : Type u₂} [category.{v₂} D]

/-- A functor `F : T ⥤ D` induces a functor `over X ⥤ over (F.obj X)` in the obvious way. -/
@[simps]
def post (F : T ⥤ D) : over X ⥤ over (F.obj X) :=
{ obj := λ Y, mk $ F.map Y.hom,
  map := λ Y₁ Y₂ f,
  { left := F.map f.left,
    w' := by tidy; erw [← F.map_comp, w] } }

end

end over

/-- The under category has as objects arrows with domain `X` and as morphisms commutative
    triangles. -/
@[derive category]
def under (X : T) := comma.{0 v₁ v₁} (functor.from_punit X) (𝟭 T)

-- Satisfying the inhabited linter
instance under.inhabited [inhabited T] : inhabited (under (default T)) :=
{ default :=
  { right := default T,
    hom := 𝟙 _ } }

namespace under

variables {X : T}

@[ext] lemma under_morphism.ext {X : T} {U V : under X} {f g : U ⟶ V}
  (h : f.right = g.right) : f = g :=
by tidy

@[simp] lemma under_left (U : under X) : U.left = punit.star := by tidy

@[simp] lemma id_right (U : under X) : comma_morphism.right (𝟙 U) = 𝟙 U.right := rfl
@[simp] lemma comp_right (a b c : under X) (f : a ⟶ b) (g : b ⟶ c) :
  (f ≫ g).right = f.right ≫ g.right := rfl

@[simp] lemma w {A B : under X} (f : A ⟶ B) : A.hom ≫ f.right = B.hom :=
by have := f.w; tidy

/-- To give an object in the under category, it suffices to give an arrow with domain `X`. -/
@[simps]
def mk {X Y : T} (f : X ⟶ Y) : under X :=
{ right := Y, hom := f }

/-- To give a morphism in the under category, it suffices to give a morphism fitting in a
    commutative triangle. -/
@[simps]
def hom_mk {U V : under X} (f : U.right ⟶ V.right) (w : U.hom ≫ f = V.hom . obviously) :
  U ⟶ V :=
{ right := f }

/--
Construct an isomorphism in the over category given isomorphisms of the objects whose forward
direction gives a commutative triangle.
-/
def iso_mk {f g : under X} (hr : f.right ≅ g.right) (hw : f.hom ≫ hr.hom = g.hom) : f ≅ g :=
comma.iso_mk (eq_to_iso (subsingleton.elim _ _)) hr (by simp [hw])

@[simp]
lemma iso_mk_hom_right {f g : under X} (hr : f.right ≅ g.right) (hw : f.hom ≫ hr.hom = g.hom) :
  (iso_mk hr hw).hom.right = hr.hom := rfl

@[simp]
lemma iso_mk_inv_right {f g : under X} (hr : f.right ≅ g.right) (hw : f.hom ≫ hr.hom = g.hom) :
  (iso_mk hr hw).inv.right = hr.inv := rfl

/-- The forgetful functor mapping an arrow to its domain. -/
def forget : under X ⥤ T := comma.snd _ _

@[simp] lemma forget_obj {U : under X} : forget.obj U = U.right := rfl
@[simp] lemma forget_map {U V : under X} {f : U ⟶ V} : forget.map f = f.right := rfl

/-- A morphism `X ⟶ Y` induces a functor `under Y ⥤ under X` in the obvious way. -/
def map {Y : T} (f : X ⟶ Y) : under Y ⥤ under X := comma.map_left _ $ discrete.nat_trans (λ _, f)

section
variables {Y : T} {f : X ⟶ Y} {U V : under Y} {g : U ⟶ V}
@[simp] lemma map_obj_right : ((map f).obj U).right = U.right := rfl
@[simp] lemma map_obj_hom   : ((map f).obj U).hom   = f ≫ U.hom := rfl
@[simp] lemma map_map_right : ((map f).map g).right = g.right := rfl

/-- Mapping by the identity morphism is just the identity functor. -/
def map_id : map (𝟙 Y) ≅ 𝟭 _ :=
nat_iso.of_components (λ X, iso_mk (iso.refl _) (by tidy)) (by tidy)

/-- Mapping by the composite morphism `f ≫ g` is the same as mapping by `f` then by `g`. -/
def map_comp {Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map g ⋙ map f :=
nat_iso.of_components (λ X, iso_mk (iso.refl _) (by tidy)) (by tidy)

end

section
variables {D : Type u₂} [category.{v₂} D]

/-- A functor `F : T ⥤ D` induces a functor `under X ⥤ under (F.obj X)` in the obvious way. -/
@[simps]
def post {X : T} (F : T ⥤ D) : under X ⥤ under (F.obj X) :=
{ obj := λ Y, mk $ F.map Y.hom,
  map := λ Y₁ Y₂ f,
  { right := F.map f.right,
    w' := by tidy; erw [← F.map_comp, w] } }

end

end under

end category_theory
