/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki, Bhavik Mehta
-/

import category_theory.adjunction.basic
import category_theory.monad.basic

/-! # Kleisli category on a (co)monad

This file defines the Kleisli category on a monad `(T, η_ T, μ_ T)` as well as the co-Kleisli
category on a comonad `(U, ε_ U, δ_ U)`. It also defines the Kleisli adjunction which gives rise to
the monad `(T, η_ T, μ_ T)` as well as the co-Kleisli adjunction which gives rise to the comonad
`(U, ε_ U, δ_ U)`.

## References
* [Riehl, *Category theory in context*, Definition 5.2.9][riehl2017]
-/
namespace category_theory

universes v u -- morphism levels before object levels. See note [category_theory universes].

variables {C : Type u} [category.{v} C]

/--
The objects for the Kleisli category of the monad `T : monad C`, which are the same
thing as objects of the base category `C`.
-/
@[nolint unused_arguments]
def kleisli (T : monad C) := C

namespace kleisli

variables (T : monad C)

instance [inhabited C] (T : monad C) : inhabited (kleisli T) := ⟨(default : C)⟩

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

/--
The objects for the co-Kleisli category of the comonad `U : monad C`, which are the same
thing as objects of the base category `C`.
-/
@[nolint unused_arguments]
def cokleisli (U : comonad C) := C

namespace cokleisli

variables (U : comonad C)

instance [inhabited C] (U : comonad C) : inhabited (cokleisli U) := ⟨(default : C)⟩

/-- The co-Kleisli category on a comonad `U`.-/
instance cokleisli.category : category (cokleisli U) :=
{ hom := λ (X Y : C), (U : C ⥤ C).obj X ⟶  Y,
  id := λ X, U.ε.app X,
  comp := λ X Y Z f g, U.δ.app X ≫ (U : C ⥤ C).map f ≫ g,
  id_comp' := λ X Y f, by rw U.right_counit_assoc,
  assoc' := λ W X Y Z f g h,
    begin unfold_projs,
      simp only [functor.map_comp, ← category.assoc, U.δ.naturality_assoc, functor.comp_map,
        U.coassoc] end }

namespace adjunction

/-- The right adjoint of the adjunction which induces the comonad `(U, ε_ U, δ_ U)`. -/
@[simps] def to_cokleisli : C ⥤ cokleisli U :=
{ obj       := λ X, (X : cokleisli U),
  map       := λ X Y f, (U.ε.app X ≫ f : _),
  map_comp' := λ X Y Z f g, by { unfold_projs, simp [← U.ε.naturality g] } }

/-- The left adjoint of the adjunction which induces the comonad `(U, ε_ U, δ_ U)`. -/
@[simps] def from_cokleisli : cokleisli U ⥤ C :=
{ obj       := λ X, U.obj X,
  map       := λ X Y f, U.δ.app X ≫ U.map f,
  map_id'   := λ X, U.right_counit _,
  map_comp' := λ X Y Z f g,
  begin
    unfold_projs,
    dsimp,
    simp only [functor.map_comp, ← category.assoc],
    rw comonad.coassoc,
    simp only [category.assoc, nat_trans.naturality, functor.comp_map],
  end }

/-- The co-Kleisli adjunction which gives rise to the monad `(U, ε_ U, δ_ U)`. -/
def adj :  from_cokleisli U ⊣ to_cokleisli U :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y, equiv.refl (U.obj X ⟶ Y),
  hom_equiv_naturality_right' := λ X Y Z f g,
    begin unfold_projs, dsimp, erw [← category.assoc (U.map f), U.ε.naturality], dsimp,
      simp only [← category.assoc, comonad.left_counit, category.id_comp] end }

/-- The composition of the adjunction gives the original functor. -/
def to_cokleisli_comp_from_cokleisli_iso_self : to_cokleisli U ⋙ from_cokleisli U ≅ U :=
nat_iso.of_components (λ X, iso.refl _) (λ X Y f, by { dsimp, simp })

end adjunction
end cokleisli

end category_theory
