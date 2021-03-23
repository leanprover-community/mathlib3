/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Scott Morrison
-/
import category_theory.comma
import category_theory.punit
import category_theory.limits.shapes.terminal

/-!
# The category of "structured arrows"

For `T : C ⥤ D`, a `T`-structured arrow with source `S : D`
is just a morphism `S ⟶ T.obj Y`, for some `Y : D`.

These form a category with morphisms `g : Y ⟶ Y'` making the obvious diagram commute.

We prove that `𝟙 (T.obj Y)` is the initial object in `T`-structured objects with source `T.obj Y`.
-/

namespace category_theory

universes v₁ v₂ u₁ u₂ -- morphism levels before object levels. See note [category_theory universes].
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

/--
The category of `T`-structured arrows with domain `S : D` (here `T : C ⥤ D`),
has as its objects `D`-morphisms of the form `S ⟶ T Y`, for some `Y : C`,
and morphisms `C`-morphisms `Y ⟶ Y'` making the obvious triangle commute.
-/
@[derive category, nolint has_inhabited_instance]
def structured_arrow (S : D) (T : C ⥤ D) := comma (functor.from_punit S) T

namespace structured_arrow

variables {S S' S'' : D} {Y Y' : C} {T : C ⥤ D}

/-- Construct a structured arrow from a morphism. -/
def mk (f : S ⟶ T.obj Y) : structured_arrow S T := ⟨⟨⟩, Y, f⟩

@[simp] lemma mk_left (f : S ⟶ T.obj Y) : (mk f).left = punit.star := rfl
@[simp] lemma mk_right (f : S ⟶ T.obj Y) : (mk f).right = Y := rfl
@[simp] lemma mk_hom_eq_self (f : S ⟶ T.obj Y) : (mk f).hom = f := rfl

lemma eq_mk (f : structured_arrow S T) : f = mk (f.hom) :=
by { cases f, congr, ext, }

/--
To construct a morphism of structured arrows,
we need a morphism of the objects underlying the target,
and to check that the triangle commutes.
-/
@[simps]
def mk_hom {f f' : structured_arrow S T} (g : f.right ⟶ f'.right) (w : f.hom ≫ T.map g = f'.hom) :
  f ⟶ f' :=
{ left := eq_to_hom (by ext),
  right := g,
  w' := by { dsimp, simpa using w.symm, }, }

/--
A morphism between source objects `S ⟶ S'`
contravariantly induces a functor between structured arrows,
`structured_arrow S' T ⥤ structured_arrow S T`.

Ideally this would be described as a 2-functor from `D`
(promoted to a 2-category with equations as 2-morphisms)
to `Cat`.
-/
@[simps]
def map (f : S ⟶ S') : structured_arrow S' T ⥤ structured_arrow S T :=
comma.map_left _ ((functor.const _).map f)

@[simp] lemma map_mk {f : S' ⟶ T.obj Y} (g : S ⟶ S') :
  (map g).obj (mk f) = mk (g ≫ f) := rfl

@[simp] lemma map_id {f : structured_arrow S T} : (map (𝟙 S)).obj f = f :=
by { rw eq_mk f, simp, }

@[simp] lemma map_comp {f : S ⟶ S'} {f' : S' ⟶ S''} {h : structured_arrow S'' T} :
  (map (f ≫ f')).obj h = (map f).obj ((map f').obj h) :=
by { rw eq_mk h, simp, }

open category_theory.limits

/-- The identity structured arrow is initial. -/
def mk_id_initial [full T] [faithful T] : is_initial (mk (𝟙 (T.obj Y))) :=
{ desc := λ c, mk_hom (T.preimage c.X.hom) (by { dsimp, simp, }),
  uniq' := begin
    rintros c m -,
    ext,
    apply T.map_injective,
    have := m.w.symm,
    dsimp at this,
    simpa using this,
  end }

end structured_arrow

end category_theory
