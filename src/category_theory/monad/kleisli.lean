/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki, Bhavik Mehta
-/

import category_theory.adjunction
import category_theory.monad.adjunction
import category_theory.monad.basic

/-! # Kleisli category on a monad

This file defines the Kleisli category on a monad `(T, η_ T, μ_ T)`. It also defines the Kleisli
adjunction which gives rise to the monad `(T, η_ T, μ_ T)`.

## References
* [Riehl, *Category theory in context*, Definition 5.2.9][riehl2017]
-/
namespace category_theory

universes v u -- morphism levels before object levels. See note [category_theory universes].

variables {C : Type u} [category.{v} C]

/--
The objects for the Kleisli category of the functor (usually monad) `T : C ⥤ C`, which are the same
thing as objects of the base category `C`.
-/
@[nolint unused_arguments]
def kleisli (T : monad C) := C

namespace kleisli

variables (T : monad C)

instance [inhabited C] (T : monad C) : inhabited (kleisli T) := ⟨(default _ : C)⟩

/-- The Kleisli category on a monad `T`.
    cf Definition 5.2.9 in [Riehl][riehl2017]. -/
instance kleisli.category : category (kleisli T) :=
{ hom  := λ (X Y : C), X ⟶ (T : C ⥤ C).obj Y,
  id   := λ X, T.η.app X,
  comp := λ X Y Z f g, f ≫ (T : C ⥤ C).map g ≫ T.μ.app Z,
  id_comp' := λ X Y f,
  begin
    rw [← T.η.naturality_assoc f, T.left_unit],
    apply category.comp_id,
  end,
  assoc'   := λ W X Y Z f g h,
  begin
    simp only [functor.map_comp, category.assoc, monad.assoc],
    erw T.μ.naturality_assoc,
  end }

namespace adjunction

/-- The left adjoint of the adjunction which induces the monad `(T, η_ T, μ_ T)`. -/
@[simps] def to_kleisli : C ⥤ kleisli T :=
{ obj       := λ X, (X : kleisli T),
  map       := λ X Y f, (f ≫ T.η.app Y : _),
  map_comp' := λ X Y Z f g, by { unfold_projs, simp [← T.η.naturality g] } }

/-- The right adjoint of the adjunction which induces the monad `(T, η_ T, μ_ T)`. -/
@[simps] def from_kleisli : kleisli T ⥤ C :=
{ obj       := λ X, T.obj X,
  map       := λ X Y f, T.map f ≫ T.μ.app Y,
  map_id'   := λ X, T.right_unit _,
  map_comp' := λ X Y Z f g,
  begin
    unfold_projs,
    simp only [functor.map_comp, category.assoc],
    erw [← T.μ.naturality_assoc g, T.assoc],
    refl,
  end }

/-- The Kleisli adjunction which gives rise to the monad `(T, η_ T, μ_ T)`.
    cf Lemma 5.2.11 of [Riehl][riehl2017]. -/
def adj : to_kleisli T ⊣ from_kleisli T :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y, equiv.refl (X ⟶ T.obj Y),
  hom_equiv_naturality_left_symm' := λ X Y Z f g,
  begin
    unfold_projs,
    dsimp,
    rw [category.assoc, ← T.η.naturality_assoc g, functor.id_map],
    dsimp,
    simp [monad.left_unit],
  end }

/-- The composition of the adjunction gives the original functor. -/
def to_kleisli_comp_from_kleisli_iso_self : to_kleisli T ⋙ from_kleisli T ≅ T :=
nat_iso.of_components (λ X, iso.refl _) (λ X Y f, by { dsimp, simp })

end adjunction
end kleisli

end category_theory
