/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monad.algebra
import category_theory.adjunction.fully_faithful

namespace category_theory
open category

universes v₁ v₂ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]
variables (R : D ⥤ C)

namespace adjunction

instance monad (R : D ⥤ C) [is_right_adjoint R] : monad ((left_adjoint R) ⋙ R) :=
let L := left_adjoint R in
let h : L ⊣ R := is_right_adjoint.adj in
{ η := h.unit,
  μ := whisker_right (whisker_left L h.counit) R,
  assoc' := λ X, by { dsimp, erw [←R.map_comp, h.counit.naturality, R.map_comp], refl },
  right_unit' := λ X, by { dsimp, rw [←R.map_comp], simp }, }

@[simp] lemma monad_η_app [is_right_adjoint R] (X) :
  (η_ ((left_adjoint R) ⋙ R)).app X = is_right_adjoint.adj.unit.app X := rfl
@[simp] lemma monad_μ_app [is_right_adjoint R] (X) :
  (μ_ ((left_adjoint R) ⋙ R)).app X = R.map (is_right_adjoint.adj.counit.app ((left_adjoint R).obj X)) := rfl

end adjunction

namespace monad

-- We can't use `@[simps]` here because it can't cope with `let` statements.
def comparison [is_right_adjoint R] : D ⥤ algebra ((left_adjoint R) ⋙ R) :=
let h : _ ⊣ R := is_right_adjoint.adj in
{ obj := λ X,
  { A := R.obj X,
    a := R.map (h.counit.app X),
    assoc' := by { dsimp, conv { to_rhs, erw [←R.map_comp, h.counit.naturality, R.map_comp], }, refl } },
  map := λ X Y f,
  { f := R.map f,
    h' := begin dsimp, erw [←R.map_comp, h.counit.naturality, R.map_comp, functor.id_map], refl, end } }.

@[simp] lemma comparison_map_f [is_right_adjoint R] {X Y} (f : X ⟶ Y) :
  ((comparison R).map f).f = R.map f := rfl
@[simp] lemma comparison_obj_a [is_right_adjoint R] (X) :
  ((comparison R).obj X).a = R.map (is_right_adjoint.adj.counit.app X) := rfl

def comparison_forget [is_right_adjoint R] : comparison R ⋙ forget ((left_adjoint R) ⋙ R) ≅ R :=
{ hom := { app := λ X, 𝟙 _, },
  inv := { app := λ X, 𝟙 _, } }

end monad

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A functor is *reflective*, or *a reflective inclusion*, if it is fully faithful and right adjoint. -/
class reflective (R : D ⥤ C) extends is_right_adjoint R, full R, faithful R.

/-- A right adjoint functor `R : D ⥤ C` is *monadic* if the comparison function `monad.comparison R` from `D` to the
category of Eilenberg-Moore algebras for the adjunction is an equivalence. -/
class monadic_right_adjoint (R : D ⥤ C) extends is_right_adjoint R :=
(eqv : is_equivalence (monad.comparison R))
end prio

instance μ_iso_of_reflective [reflective R] : is_iso (μ_ ((left_adjoint R) ⋙ R)) :=
by { dsimp [adjunction.monad], apply_instance }

attribute [instance] monadic_right_adjoint.eqv

-- PROJECT prove Beck's monadicity theorem, e.g. from Section 5.5 of [Riehl][riehl2017]

namespace reflective

lemma comparison_ess_surj_aux [reflective R] (X : monad.algebra ((left_adjoint R) ⋙ R)) :
  ((is_right_adjoint.adj).unit).app (R.obj ((left_adjoint R).obj (X.A)))
    = R.map ((left_adjoint R).map ((is_right_adjoint.adj).unit.app X.A)) :=
begin
 -- both are left inverses to μ_X.
 apply (cancel_mono ((μ_ ((left_adjoint R) ⋙ R)).app _)).1,
 { dsimp, erw [adjunction.right_triangle_components, ←R.map_comp], simp, },
 { apply is_iso.mono_of_iso _,
   apply nat_iso.is_iso_app_of_is_iso }
end

instance [reflective R] (X : monad.algebra ((left_adjoint R) ⋙ R)) :
  is_iso ((is_right_adjoint.adj : _ ⊣ R).unit.app X.A) :=
let L := left_adjoint R in
let h : L ⊣ R := (is_right_adjoint.adj) in
{ inv := X.a,
  hom_inv_id' := X.unit,
  inv_hom_id' :=
  begin
    dsimp,
    erw [h.unit.naturality, comparison_ess_surj_aux,
          ←R.map_comp, ←L.map_comp, X.unit, L.map_id, R.map_id],
    refl
  end }

instance comparison_ess_surj [reflective R]: ess_surj (monad.comparison R) :=
let L := left_adjoint R in
let h : L ⊣ R := is_right_adjoint.adj in
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

instance comparison_full [full R] [is_right_adjoint R] : full (monad.comparison R) :=
{ preimage := λ X Y f, R.preimage f.f }
instance comparison_faithful [faithful R] [is_right_adjoint R] : faithful (monad.comparison R) :=
{ map_injective' := λ X Y f g w, by { have w' := (congr_arg monad.algebra.hom.f w), exact R.map_injective w' } }

end reflective

/-- Any reflective inclusion has a monadic right adjoint.
    cf Prop 5.3.3 of [Riehl][riehl2017] -/
@[priority 100] -- see Note [lower instance priority]
instance monadic_of_reflective [reflective R] : monadic_right_adjoint R :=
{ eqv := equivalence.equivalence_of_fully_faithfully_ess_surj _ }

end category_theory
