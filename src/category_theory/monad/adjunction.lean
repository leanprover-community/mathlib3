/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monad.algebra
import category_theory.reflective

namespace category_theory
open category

universes v₁ v₂ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒞 𝒟
variables {L : C ⥤ D} {R : D ⥤ C}

namespace adjunction

def monad (h : L ⊣ R) : monad.{v₁} C :=
{ T := L ⋙ R,
  η := h.unit,
  μ := whisker_right (whisker_left L h.counit) R,
  assoc' := λ X, by { dsimp, erw [←R.map_comp, h.counit.naturality, R.map_comp], refl },
  right_unit' := λ X, by { dsimp, rw [←R.map_comp], simp }, }

@[simp] lemma monad_T_obj (h : L ⊣ R) (X) : h.monad.T.obj X = R.obj (L.obj X) := rfl
@[simp] lemma monad_T_map (h : L ⊣ R) {X Y} (f : X ⟶ Y) : h.monad.T.map f = R.map (L.map f) := rfl
@[simp] lemma monad_η_app (h : L ⊣ R) (X) : h.monad.η.app X = h.unit.app X := rfl
@[simp] lemma monad_μ_app (h : L ⊣ R) (X) : h.monad.μ.app X = R.map (h.counit.app (L.obj X)) := rfl

end adjunction

namespace monad

-- TODO move
instance μ_iso_of_reflective [full R] [faithful R] (h : L ⊣ R) : is_iso (h.monad.μ) :=
by { dsimp [adjunction.monad], apply_instance }

def comparison (h : L ⊣ R) : D ⥤ algebra h.monad :=
{ obj := λ X,
  { A := R.obj X,
    a := R.map (h.counit.app X),
    assoc' := by { dsimp, conv { to_rhs, erw [←R.map_comp, h.counit.naturality, R.map_comp], }, refl } },
  map := λ X Y f,
  { f := R.map f,
    h' := begin dsimp, erw [←R.map_comp, h.counit.naturality, R.map_comp, functor.id_map], refl, end }}

@[simp] lemma comparison_map_f (h : L ⊣ R) {X Y} (f : X ⟶ Y) : ((comparison h).map f).f = R.map f := rfl
@[simp] lemma comparison_obj_a (h : L ⊣ R) (X) : ((comparison h).obj X).a = R.map (h.counit.app X) := rfl

def comparison_forget (h : L ⊣ R) : comparison h ⋙ forget (h.monad) ≅ R :=
{ hom := { app := λ X, 𝟙 _, },
  inv := { app := λ X, 𝟙 _, } }

end monad

namespace adjunction

def monadic (h : L ⊣ R) := is_equivalence (monad.comparison h)

-- TODO prove Beck's monadicity theorem, e.g. from Section 5.5 of Riehl

end adjunction

class reflective (R : D ⥤ C) extends is_right_adjoint R, fully_faithful R.

class monadic (R : D ⥤ C) extends is_right_adjoint R :=
(monadic : adj.monadic)

def left (R : D ⥤ C) [is_right_adjoint R] : C ⥤ D :=
is_right_adjoint.left R
def right (L : C ⥤ D) [is_left_adjoint L] : D ⥤ C :=
is_left_adjoint.right L

namespace reflective

lemma comparison_ess_surj_aux {L : C ⥤ D} {R : D ⥤ C} [full R] [faithful R] (h : L ⊣ R) (X : monad.algebra h.monad) :
  (h.unit).app (R.obj (L.obj (X.A))) = R.map (L.map (h.unit.app X.A)) :=
begin
 -- both are left inverses to μ_X.
 apply (cancel_mono (h.monad.μ.app _)).1,
 { dsimp, erw [adjunction.right_triangle_components, ←R.map_comp], simp, },
 { apply is_iso.mono_of_iso _,
   apply nat_iso.is_iso_app_of_is_iso }
end

instance {L : C ⥤ D} {R : D ⥤ C} [full R] [faithful R] (h : L ⊣ R) (X : monad.algebra h.monad) :
  is_iso (h.unit.app X.A) :=
{ inv := X.a,
  hom_inv_id' := X.unit,
  inv_hom_id' :=
  begin
    dsimp,
    erw [h.unit.naturality, comparison_ess_surj_aux,
          ←R.map_comp, ←L.map_comp, X.unit, L.map_id, R.map_id],
  end }

instance comparison_ess_surj {L : C ⥤ D} {R : D ⥤ C} [full R] [faithful R] (h : L ⊣ R) : ess_surj (monad.comparison h) :=
{ obj_preimage := λ X, L.obj X.A,
  iso' := λ X,
  { hom :=
    { f := (as_iso (h.unit.app X.A)).inv,
      h' :=
      begin
        dsimp,
        apply (cancel_epi (R.map (L.map ((h.unit).app (X.A))))).1,
        rw [is_iso.hom_inv_id_assoc, ←category.assoc, ←R.map_comp,adjunction.left_triangle_components],
        erw [functor.map_id, category.id_comp],
        apply (cancel_epi ((h.unit).app (X.A))).1,
        rw is_iso.hom_inv_id,
        exact X.unit,
      end },
    inv :=
    { f := (as_iso (h.unit.app X.A)).hom,
      h' :=
      begin
        dsimp,
        erw [←R.map_comp, adjunction.left_triangle_components, R.map_id],
        apply (cancel_epi ((h.unit).app (X.A))).1,
        conv { to_rhs, erw [←category.assoc, X.unit] },
        erw [comp_id, id_comp],
      end },
    hom_inv_id' := by { ext, exact (as_iso (h.unit.app X.A)).inv_hom_id, },
    inv_hom_id' := by { ext, exact (as_iso (h.unit.app X.A)).hom_inv_id, }, } }

instance comparison_full {L : C ⥤ D} {R : D ⥤ C} [full R] (h : L ⊣ R) : full (monad.comparison h) :=
{ preimage := λ X Y f, R.preimage f.f }
instance comparison_faithful {L : C ⥤ D} {R : D ⥤ C} [faithful R] (h : L ⊣ R) : faithful (monad.comparison h) :=
{ injectivity' := λ X Y f g w, by { have w' := (congr_arg monad.algebra.hom.f w), exact R.injectivity w' } }

end reflective

-- Proposition 5.3.3 of Riehl
instance monadic_of_reflective [reflective R] : monadic R :=
{ monadic := equivalence.equivalence_of_fully_faithfully_ess_surj _ }

end category_theory
