/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.monad.algebra
import category_theory.adjunction

namespace category_theory
open category

universes v₁ v₂ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]
variables (R : D ⥤ C)

namespace adjunction

@[simps]
instance monad (R : D ⥤ C) [is_right_adjoint R] : monad (left_adjoint R ⋙ R) :=
{ η := (of_right_adjoint R).unit,
  μ := whisker_right (whisker_left (left_adjoint R) (of_right_adjoint R).counit) R,
  assoc' := λ X, by { dsimp, rw [←R.map_comp], simp },
  right_unit' := λ X, by { dsimp, rw [←R.map_comp], simp } }

end adjunction

namespace monad

/--
Gven any adjunction `L ⊣ R`, there is a comparison functor `category_theory.monad.comparison R`
sending objects `Y : D` to Eilenberg-Moore algebras for `L ⋙ R` with underlying object `R.obj X`.

We later show that this is full when `R` is full, faithful when `R` is faithful,
and essentially surjective when `R` is reflective.
-/
@[simps]
def comparison [is_right_adjoint R] : D ⥤ algebra (left_adjoint R ⋙ R) :=
{ obj := λ X,
  { A := R.obj X,
    a := R.map ((adjunction.of_right_adjoint R).counit.app X),
    assoc' := by { dsimp, rw [← R.map_comp, ← adjunction.counit_naturality, R.map_comp], refl } },
  map := λ X Y f,
  { f := R.map f,
    h' := by { dsimp, rw [← R.map_comp, adjunction.counit_naturality, R.map_comp] } } }.

/--
The underlying object of `(monad.comparison R).obj X` is just `R.obj X`.
-/
@[simps]
def comparison_forget [is_right_adjoint R] : comparison R ⋙ forget (left_adjoint R ⋙ R) ≅ R :=
{ hom := { app := λ X, 𝟙 _, },
  inv := { app := λ X, 𝟙 _, } }

end monad

/-- A right adjoint functor `R : D ⥤ C` is *monadic* if the comparison function `monad.comparison R` from `D` to the
category of Eilenberg-Moore algebras for the adjunction is an equivalence. -/
class monadic_right_adjoint (R : D ⥤ C) extends is_right_adjoint R :=
(eqv : is_equivalence (monad.comparison R))

-- TODO: This holds more generally for idempotent adjunctions, not just reflective adjunctions.
instance μ_iso_of_reflective [reflective R] : is_iso (μ_ (left_adjoint R ⋙ R)) :=
by { dsimp [adjunction.monad], apply_instance }

attribute [instance] monadic_right_adjoint.eqv

namespace reflective

instance [reflective R] (X : monad.algebra (left_adjoint R ⋙ R)) :
  is_iso ((adjunction.of_right_adjoint R).unit.app X.A) :=
{ inv := X.a,
  hom_inv_id' := X.unit,
  inv_hom_id' :=
  begin
    dsimp only [functor.id_obj],
    rw ← (adjunction.of_right_adjoint R).unit_naturality,
    dsimp only [functor.comp_obj],
    rw [unit_obj_eq_map_unit, ←functor.map_comp, ←functor.map_comp],
    erw X.unit,
    simp,
  end }

instance comparison_ess_surj [reflective R] : ess_surj (monad.comparison R) :=
begin
  refine ⟨λ X, ⟨(left_adjoint R).obj X.A, ⟨_⟩⟩⟩,
  symmetry,
  refine monad.algebra.iso_mk _ _,
  { exact as_iso ((adjunction.of_right_adjoint R).unit.app X.A) },
  dsimp only [functor.comp_map, monad.comparison_obj_a, as_iso_hom, functor.comp_obj,
    monad.comparison_obj_A],
  rw [←cancel_epi ((adjunction.of_right_adjoint R).unit.app X.A), adjunction.unit_naturality_assoc,
      adjunction.right_triangle_components, comp_id],
  apply (X.unit_assoc _).symm,
end

instance comparison_full [full R] [is_right_adjoint R] : full (monad.comparison R) :=
{ preimage := λ X Y f, R.preimage f.f }
instance comparison_faithful [faithful R] [is_right_adjoint R] : faithful (monad.comparison R) :=
{ map_injective' := λ X Y f g w,
    by { have w' := congr_arg monad.algebra.hom.f w, exact R.map_injective w' } }

end reflective

-- It is possible to do this computably since the construction gives the data of the inverse, not
-- just the existence of an inverse on each object.
/-- Any reflective inclusion has a monadic right adjoint.
    cf Prop 5.3.3 of [Riehl][riehl2017] -/
@[priority 100] -- see Note [lower instance priority]
noncomputable instance monadic_of_reflective [reflective R] : monadic_right_adjoint R :=
{ eqv := equivalence.equivalence_of_fully_faithfully_ess_surj _ }

end category_theory
