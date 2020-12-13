/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.comma

/-!
# The category of arrows

The category of arrows, with morphisms commutative squares.
We set this up as a specialization of the comma category `comma L R`,
where `L` and `R` are both the identity functor.

We also define the typeclass `has_lift`, representing a choice of a lift
of a commutative square (that is, a diagonal morphism making the two triangles commute).

## Tags

comma, arrow
-/

namespace category_theory

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation
variables {T : Type u} [category.{v} T]

section
variables (T)

/-- The arrow category of `T` has as objects all morphisms in `T` and as morphisms commutative
     squares in `T`. -/
@[derive category]
def arrow := comma.{v v v} (𝟭 T) (𝟭 T)

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

@[simp, reassoc] lemma w {f g : arrow T} (sq : f ⟶ g) : sq.left ≫ g.hom = f.hom ≫ sq.right := sq.w

/-- A lift of a commutative square is a diagonal morphism making the two triangles commute. -/
@[ext] structure lift_struct {f g : arrow T} (sq : f ⟶ g) :=
(lift : f.right ⟶ g.left)
(fac_left : f.hom ≫ lift = sq.left)
(fac_right : lift ≫ g.hom = sq.right)

instance lift_struct_inhabited {X : T} : inhabited (lift_struct (𝟙 (arrow.mk (𝟙 X)))) :=
⟨⟨𝟙 _, category.id_comp _, category.comp_id _⟩⟩

/-- `has_lift sq` says that there is some `lift_struct sq`, i.e., that it is possible to find a
    diagonal morphism making the two triangles commute. -/
class has_lift {f g : arrow T} (sq : f ⟶ g) : Prop :=
mk' :: (exists_lift : nonempty (lift_struct sq))

lemma has_lift.mk {f g : arrow T} {sq : f ⟶ g} (s : lift_struct sq) : has_lift sq :=
⟨nonempty.intro s⟩

attribute [simp, reassoc] lift_struct.fac_left lift_struct.fac_right

/-- Given `has_lift sq`, obtain a lift. -/
noncomputable def has_lift.struct {f g : arrow T} (sq : f ⟶ g) [has_lift sq] : lift_struct sq :=
classical.choice has_lift.exists_lift

/-- If there is a lift of a commutative square `sq`, we can access it by saying `lift sq`. -/
noncomputable abbreviation lift {f g : arrow T} (sq : f ⟶ g) [has_lift sq] : f.right ⟶ g.left :=
(has_lift.struct sq).lift

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

instance subsingleton_lift_struct_of_epi {f g : arrow T} (sq : f ⟶ g) [epi f.hom] :
  subsingleton (lift_struct sq) :=
subsingleton.intro $ λ a b, lift_struct.ext a b $ (cancel_epi f.hom).1 $ by simp

instance subsingleton_lift_struct_of_mono {f g : arrow T} (sq : f ⟶ g) [mono g.hom] :
  subsingleton (lift_struct sq) :=
subsingleton.intro $ λ a b, lift_struct.ext a b $ (cancel_mono g.hom).1 $ by simp

end

end arrow

namespace functor

universes v₁ v₂ u₁ u₂

variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

/-- A functor `C ⥤ D` induces a functor between the corresponding arrow categories. -/
@[simps]
def map_arrow (F : C ⥤ D) : arrow C ⥤ arrow D :=
{ obj := λ a,
  { left := F.obj a.left,
    right := F.obj a.right,
    hom := F.map a.hom, },
  map := λ a b f,
  { left := F.map f.left,
    right := F.map f.right,
    w' := by { have w := f.w, simp only [id_map] at w, dsimp, simp only [←F.map_comp, w], } } }

end functor

end category_theory
