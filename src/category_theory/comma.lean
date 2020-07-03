/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin, Bhavik Mehta
-/
import category_theory.punit
import category_theory.reflect_isomorphisms

/-!
# Comma categories

A comma category is a construction in category theory, which builds a category out of two functors
with a common codomain. Specifically, for functors `L : A ⥤ T` and `R : B ⥤ T`, an object in
`comma L R` is a morphism `hom : L.obj left ⟶ R.obj right` for some objects `left : A` and
`right : B`, and a morphism in `comma L R` between `hom : L.obj left ⟶ R.obj right` and
`hom' : L.obj left' ⟶ R.obj right'` is a commutative square

L.obj left   ⟶   L.obj left'
      |               |
  hom |               | hom'
      ↓               ↓
R.obj right  ⟶   R.obj right',

where the top and bottom morphism come from morphisms `left ⟶ left'` and `right ⟶ right'`,
respectively.

Several important constructions are special cases of this construction.
* If `L` is the identity functor and `R` is a constant functor, then `comma L R` is the "slice" or
  "over" category over the object `R` maps to.
* Conversely, if `L` is a constant functor and `R` is the identity functor, then `comma L R` is the
  "coslice" or "under" category under the object `L` maps to.
* If `L` and `R` both are the identity functor, then `comma L R` is the arrow category of `T`.

## Main definitions

* `comma L R`: the comma category of the functors `L` and `R`.
* `over X`: the over category of the object `X`.
* `under X`: the under category of the object `X`.
* `arrow T`: the arrow category of the category `T`.

## References

* https://ncatlab.org/nlab/show/comma+category

## Tags

comma, slice, coslice, over, under, arrow
-/


namespace category_theory

universes v₁ v₂ v₃ u₁ u₂ u₃ -- declare the `v`'s first; see `category_theory.category` for an explanation
variables {A : Type u₁} [category.{v₁} A]
variables {B : Type u₂} [category.{v₂} B]
variables {T : Type u₃} [category.{v₃} T]

/-- The objects of the comma category are triples of an object `left : A`, an object
   `right : B` and a morphism `hom : L.obj left ⟶ R.obj right`.  -/
structure comma (L : A ⥤ T) (R : B ⥤ T) : Type (max u₁ u₂ v₃) :=
(left : A . obviously)
(right : B . obviously)
(hom : L.obj left ⟶ R.obj right)

-- Satisfying the inhabited linter
instance comma.inhabited [inhabited T] : inhabited (comma (𝟭 T) (𝟭 T)) :=
{ default :=
  { left := default T,
    right := default T,
    hom := 𝟙 (default T) } }

variables {L : A ⥤ T} {R : B ⥤ T}

/-- A morphism between two objects in the comma category is a commutative square connecting the
    morphisms coming from the two objects using morphisms in the image of the functors `L` and `R`.
-/
@[ext] structure comma_morphism (X Y : comma L R) :=
(left : X.left ⟶ Y.left . obviously)
(right : X.right ⟶ Y.right . obviously)
(w' : L.map left ≫ Y.hom = X.hom ≫ R.map right . obviously)

-- Satisfying the inhabited linter
instance comma_morphism.inhabited [inhabited (comma L R)] :
  inhabited (comma_morphism (default (comma L R)) (default (comma L R))) :=
{ default :=
  { left := 𝟙 _,
    right := 𝟙 _ } }

restate_axiom comma_morphism.w'
attribute [simp, reassoc] comma_morphism.w

instance comma_category : category (comma L R) :=
{ hom := comma_morphism,
  id := λ X,
  { left := 𝟙 X.left,
    right := 𝟙 X.right },
  comp := λ X Y Z f g,
  { left := f.left ≫ g.left,
    right := f.right ≫ g.right } }

namespace comma

section
variables {X Y Z : comma L R} {f : X ⟶ Y} {g : Y ⟶ Z}

@[simp] lemma id_left  : ((𝟙 X) : comma_morphism X X).left = 𝟙 X.left := rfl
@[simp] lemma id_right : ((𝟙 X) : comma_morphism X X).right = 𝟙 X.right := rfl
@[simp] lemma comp_left  : (f ≫ g).left  = f.left ≫ g.left   := rfl
@[simp] lemma comp_right : (f ≫ g).right = f.right ≫ g.right := rfl

end

variables (L) (R)

/-- The functor sending an object `X` in the comma category to `X.left`. -/
@[simps]
def fst : comma L R ⥤ A :=
{ obj := λ X, X.left,
  map := λ _ _ f, f.left }

/-- The functor sending an object `X` in the comma category to `X.right`. -/
@[simps]
def snd : comma L R ⥤ B :=
{ obj := λ X, X.right,
  map := λ _ _ f, f.right }

/-- We can interpret the commutative square constituting a morphism in the comma category as a
    natural transformation between the functors `fst ⋙ L` and `snd ⋙ R` from the comma category
    to `T`, where the components are given by the morphism that constitutes an object of the comma
    category. -/
@[simps]
def nat_trans : fst L R ⋙ L ⟶ snd L R ⋙ R :=
{ app := λ X, X.hom }

section
variables {L₁ L₂ L₃ : A ⥤ T} {R₁ R₂ R₃ : B ⥤ T}

/-- A natural transformation `L₁ ⟶ L₂` induces a functor `comma L₂ R ⥤ comma L₁ R`. -/
@[simps]
def map_left (l : L₁ ⟶ L₂) : comma L₂ R ⥤ comma L₁ R :=
{ obj := λ X,
  { left  := X.left,
    right := X.right,
    hom   := l.app X.left ≫ X.hom },
  map := λ X Y f,
  { left  := f.left,
    right := f.right } }

/-- The functor `comma L R ⥤ comma L R` induced by the identity natural transformation on `L` is
    naturally isomorphic to the identity functor. -/
@[simps]
def map_left_id : map_left R (𝟙 L) ≅ 𝟭 _ :=
{ hom :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } },
  inv :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } } }

/-- The functor `comma L₁ R ⥤ comma L₃ R` induced by the composition of two natural transformations
    `l : L₁ ⟶ L₂` and `l' : L₂ ⟶ L₃` is naturally isomorphic to the composition of the two functors
    induced by these natural transformations. -/
@[simps]
def map_left_comp (l : L₁ ⟶ L₂) (l' : L₂ ⟶ L₃) :
  (map_left R (l ≫ l')) ≅ (map_left R l') ⋙ (map_left R l) :=
{ hom :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } },
  inv :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } } }

/-- A natural transformation `R₁ ⟶ R₂` induces a functor `comma L R₁ ⥤ comma L R₂`. -/
@[simps]
def map_right (r : R₁ ⟶ R₂) : comma L R₁ ⥤ comma L R₂ :=
{ obj := λ X,
  { left  := X.left,
    right := X.right,
    hom   := X.hom ≫ r.app X.right },
  map := λ X Y f,
  { left  := f.left,
    right := f.right } }

/-- The functor `comma L R ⥤ comma L R` induced by the identity natural transformation on `R` is
    naturally isomorphic to the identity functor. -/
@[simps]
def map_right_id : map_right L (𝟙 R) ≅ 𝟭 _ :=
{ hom :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } },
  inv :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } } }

/-- The functor `comma L R₁ ⥤ comma L R₃` induced by the composition of the natural transformations
    `r : R₁ ⟶ R₂` and `r' : R₂ ⟶ R₃` is naturally isomorphic to the composition of the functors
    induced by these natural transformations. -/
@[simps]
def map_right_comp (r : R₁ ⟶ R₂) (r' : R₂ ⟶ R₃) :
  (map_right L (r ≫ r')) ≅ (map_right L r) ⋙ (map_right L r') :=
{ hom :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } },
  inv :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } } }

end

end comma

/-- The over category has as objects arrows in `T` with codomain `X` and as morphisms commutative
    triangles. -/
@[derive category]
def over (X : T) := comma.{v₃ 0 v₃} (𝟭 T) (functor.from_punit X)

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
-- @[simp] lemma over_morphism_right {U V : over X} (f : U ⟶ V) : f.right = sorry :=
-- begin

-- end

@[simp] lemma id_left (U : over X) : comma_morphism.left (𝟙 U) = 𝟙 U.left := rfl
@[simp] lemma comp_left (a b c : over X) (f : a ⟶ b) (g : b ⟶ c) :
  (f ≫ g).left = f.left ≫ g.left := rfl

@[simp, reassoc] lemma w {A B : over X} (f : A ⟶ B) : f.left ≫ B.hom = A.hom :=
by have := f.w; tidy

/-- To give an object in the over category, it suffices to give a morphism with codomain `X`. -/
def mk {X Y : T} (f : Y ⟶ X) : over X :=
{ left := Y, hom := f }

@[simp] lemma mk_left {X Y : T} (f : Y ⟶ X) : (mk f).left = Y := rfl
@[simp] lemma mk_hom {X Y : T} (f : Y ⟶ X) : (mk f).hom = f := rfl

/-- To give a morphism in the over category, it suffices to give an arrow fitting in a commutative
    triangle. -/
@[simps]
def hom_mk {U V : over X} (f : U.left ⟶ V.left) (w : f ≫ V.hom = U.hom . obviously) :
  U ⟶ V :=
{ left := f }

/-- The forgetful functor mapping an arrow to its domain. -/
def forget : (over X) ⥤ T := comma.fst _ _

@[simp] lemma forget_obj {U : over X} : forget.obj U = U.left := rfl
@[simp] lemma forget_map {U V : over X} {f : U ⟶ V} : forget.map f = f.left := rfl

/-- A morphism `f : X ⟶ Y` induces a functor `over X ⥤ over Y` in the obvious way. -/
def map {Y : T} (f : X ⟶ Y) : over X ⥤ over Y := comma.map_right _ $ discrete.nat_trans (λ _, f)

section
variables {Y : T} {f : X ⟶ Y} {U V : over X} {g : U ⟶ V}
@[simp] lemma map_obj_left : ((map f).obj U).left = U.left := rfl
@[simp] lemma map_obj_hom  : ((map f).obj U).hom  = U.hom ≫ f := rfl
@[simp] lemma map_map_left : ((map f).map g).left = g.left := rfl
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
    (λ g, ⟨hom_mk (hom_mk (𝟙 g.left.left)) (by apply_auto_param),
           hom_mk (hom_mk (𝟙 g.left.left)) (by apply_auto_param),
           by { ext, dsimp, simp }, by { ext, dsimp, simp }⟩)
    (λ X Y g, by { ext, dsimp, simp }),
  counit_iso :=
    nat_iso.of_components
    (λ g, ⟨hom_mk (𝟙 g.left) (by apply_auto_param),
           hom_mk (𝟙 g.left) (by apply_auto_param),
           by { ext, dsimp, simp }, by { ext, dsimp, simp }⟩)
    (λ X Y g, by { ext, dsimp, simp }) }

lemma iterated_slice_forward_forget :
  iterated_slice_forward f ⋙ forget = forget ⋙ forget :=
rfl

lemma iterated_slice_backward_forget_forget :
  iterated_slice_backward f ⋙ forget ⋙ forget = forget :=
rfl

end iterated_slice

section
variables {D : Type u₃} [category.{v₃} D]

/-- A functor `F : T ⥤ D` induces a functor `over X ⥤ over (F.obj X)` in the obvious way. -/
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
def under (X : T) := comma.{0 v₃ v₃} (functor.from_punit X) (𝟭 T)

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

/-- The forgetful functor mapping an arrow to its domain. -/
def forget : (under X) ⥤ T := comma.snd _ _

@[simp] lemma forget_obj {U : under X} : forget.obj U = U.right := rfl
@[simp] lemma forget_map {U V : under X} {f : U ⟶ V} : forget.map f = f.right := rfl

/-- A morphism `X ⟶ Y` induces a functor `under Y ⥤ under X` in the obvious way. -/
def map {Y : T} (f : X ⟶ Y) : under Y ⥤ under X := comma.map_left _ $ discrete.nat_trans (λ _, f)

section
variables {Y : T} {f : X ⟶ Y} {U V : under Y} {g : U ⟶ V}
@[simp] lemma map_obj_right : ((map f).obj U).right = U.right := rfl
@[simp] lemma map_obj_hom   : ((map f).obj U).hom   = f ≫ U.hom := rfl
@[simp] lemma map_map_right : ((map f).map g).right = g.right := rfl
end

section
variables {D : Type u₃} [category.{v₃} D]

/-- A functor `F : T ⥤ D` induces a functor `under X ⥤ under (F.obj X)` in the obvious way. -/
def post {X : T} (F : T ⥤ D) : under X ⥤ under (F.obj X) :=
{ obj := λ Y, mk $ F.map Y.hom,
  map := λ Y₁ Y₂ f,
  { right := F.map f.right,
    w' := by tidy; erw [← F.map_comp, w] } }

end

end under

section
variables (T)

/-- The arrow category of `T` has as objects all morphisms in `T` and as morphisms commutative
     squares in `T`. -/
@[derive category]
def arrow := comma.{v₃ v₃ v₃} (𝟭 T) (𝟭 T)

-- Satisfying the inhabited linter
instance arrow.inhabited [inhabited T] : inhabited (arrow T) :=
{ default := show comma (𝟭 T) (𝟭 T), from default (comma (𝟭 T) (𝟭 T)) }

end

namespace arrow

@[simp] lemma id_left (f : arrow T) : comma_morphism.left (𝟙 f) = 𝟙 (f.left) := rfl
@[simp] lemma id_right (f : arrow T) : comma_morphism.right (𝟙 f) = 𝟙 (f.right) := rfl

/-- An object in the arrow category is simply a morphism in `T`. -/
@[simps]
def mk {X Y : T} (f : X ⟶ Y) : arrow T :=
{ left := X,
  right := Y,
  hom := f }

/-- A morphism in the arrow category is a commutative square connecting two objects of the arrow
    category. -/
@[simps]
def hom_mk {f g : arrow T} {u : f.left ⟶ g.left} {v : f.right ⟶ g.right}
  (w : u ≫ g.hom = f.hom ≫ v) : f ⟶ g :=
{ left := u,
  right := v,
  w' := w }

/-- We can also build a morphism in the arrow category out of any commutative square in `T`. -/
@[simps]
def hom_mk' {X Y : T} {f : X ⟶ Y} {P Q : T} {g : P ⟶ Q} {u : X ⟶ P} {v : Y ⟶ Q}
  (w : u ≫ g = f ≫ v) : arrow.mk f ⟶ arrow.mk g :=
{ left := u,
  right := v,
  w' := w }

@[reassoc] lemma w {f g : arrow T} (sq : f ⟶ g) : sq.left ≫ g.hom = f.hom ≫ sq.right := sq.w

/-- A lift of a commutative square is a diagonal morphism making the two triangles commute. -/
@[ext] class has_lift {f g : arrow T} (sq : f ⟶ g) :=
(lift : f.right ⟶ g.left)
(fac_left : f.hom ≫ lift = sq.left)
(fac_right : lift ≫ g.hom = sq.right)

attribute [simp, reassoc] has_lift.fac_left has_lift.fac_right

/-- If we have chosen a lift of a commutative square `sq`, we can access it by saying `lift sq`. -/
abbreviation lift {f g : arrow T} (sq : f ⟶ g) [has_lift sq] : f.right ⟶ g.left :=
has_lift.lift sq

lemma lift.fac_left {f g : arrow T} (sq : f ⟶ g) [has_lift sq] : f.hom ≫ lift sq = sq.left :=
by simp

lemma lift.fac_right {f g : arrow T} (sq : f ⟶ g) [has_lift sq] : lift sq ≫ g.hom = sq.right :=
by simp

@[simp, reassoc]
lemma lift_mk'_left {X Y P Q : T} {f : X ⟶ Y} {g : P ⟶ Q} {u : X ⟶ P} {v : Y ⟶ Q}
  (h : u ≫ g = f ≫ v) [has_lift $ arrow.hom_mk' h] : f ≫ lift (arrow.hom_mk' h) = u :=
by simp only [←arrow.mk_hom f, lift.fac_left, arrow.hom_mk'_left]

@[simp, reassoc]
lemma lift_mk'_right {X Y P Q : T} {f : X ⟶ Y} {g : P ⟶ Q} {u : X ⟶ P} {v : Y ⟶ Q}
  (h : u ≫ g = f ≫ v) [has_lift $ arrow.hom_mk' h] : lift (arrow.hom_mk' h) ≫ g = v :=
by simp only [←arrow.mk_hom g, lift.fac_right, arrow.hom_mk'_right]

section

instance subsingleton_has_lift_of_epi {f g : arrow T} (sq : f ⟶ g) [epi f.hom] :
  subsingleton (has_lift sq) :=
subsingleton.intro $ λ a b, has_lift.ext a b $ (cancel_epi f.hom).1 $ by simp

instance subsingleton_has_lift_of_mono {f g : arrow T} (sq : f ⟶ g) [mono g.hom] :
  subsingleton (has_lift sq) :=
subsingleton.intro $ λ a b, has_lift.ext a b $ (cancel_mono g.hom).1 $ by simp

end

end arrow

end category_theory
