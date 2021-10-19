/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin, Bhavik Mehta
-/
import category_theory.natural_isomorphism

/-!
# Comma categories

A comma category is a construction in category theory, which builds a category out of two functors
with a common codomain. Specifically, for functors `L : A ⥤ T` and `R : B ⥤ T`, an object in
`comma L R` is a morphism `hom : L.obj left ⟶ R.obj right` for some objects `left : A` and
`right : B`, and a morphism in `comma L R` between `hom : L.obj left ⟶ R.obj right` and
`hom' : L.obj left' ⟶ R.obj right'` is a commutative square

```
L.obj left   ⟶   L.obj left'
      |               |
  hom |               | hom'
      ↓               ↓
R.obj right  ⟶   R.obj right',
```

where the top and bottom morphism come from morphisms `left ⟶ left'` and `right ⟶ right'`,
respectively.

## Main definitions

* `comma L R`: the comma category of the functors `L` and `R`.
* `over X`: the over category of the object `X` (developed in `over.lean`).
* `under X`: the under category of the object `X` (also developed in `over.lean`).
* `arrow T`: the arrow category of the category `T` (developed in `arrow.lean`).

## References

* <https://ncatlab.org/nlab/show/comma+category>

## Tags

comma, slice, coslice, over, under, arrow
-/


namespace category_theory

-- declare the `v`'s first; see `category_theory.category` for an explanation
universes v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅
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

/--
Construct an isomorphism in the comma category given isomorphisms of the objects whose forward
directions give a commutative square.
-/
@[simps]
def iso_mk {X Y : comma L₁ R₁} (l : X.left ≅ Y.left) (r : X.right ≅ Y.right)
  (h : L₁.map l.hom ≫ Y.hom = X.hom ≫ R₁.map r.hom) : X ≅ Y :=
{ hom := { left := l.hom, right := r.hom },
  inv :=
  { left := l.inv,
    right := r.inv,
    w' := begin
      rw [←L₁.map_iso_inv l, iso.inv_comp_eq, L₁.map_iso_hom, reassoc_of h, ← R₁.map_comp],
      simp
    end, } }

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

section
variables {C : Type u₄} [category.{v₄} C] {D : Type u₅} [category.{v₅} D]

/-- The functor `(F ⋙ L, R) ⥤ (L, R)` -/
@[simps] def pre_left (F: C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) : comma (F ⋙ L) R ⥤ comma L R :=
{ obj := λ X, { left := F.obj X.left, right := X.right, hom := X.hom },
  map := λ X Y f, { left := F.map f.left, right := f.right, w' := by simpa using f.w } }

/-- The functor `(F ⋙ L, R) ⥤ (L, R)` -/
@[simps] def pre_right (L : A ⥤ T) (F: C ⥤ B) (R : B ⥤ T) : comma L (F ⋙ R) ⥤ comma L R :=
{ obj := λ X, { left := X.left, right := F.obj X.right, hom := X.hom },
  map := λ X Y f, { left := f.left, right := F.map f.right, w' := by simp } }

/-- The functor `(L, R) ⥤ (L ⋙ F, R ⋙ F)` -/
@[simps] def post (L : A ⥤ T) (R : B ⥤ T) (F: T ⥤ C) : comma L R ⥤ comma (L ⋙ F) (R ⋙ F) :=
{ obj := λ X, { left := X.left, right := X.right, hom := F.map X.hom },
  map := λ X Y f, { left := f.left, right := f.right, w' :=
    by { simp only [functor.comp_map, ←F.map_comp, f.w] } } }

end
end comma

end category_theory
