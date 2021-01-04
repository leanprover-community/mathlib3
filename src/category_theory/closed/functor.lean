/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.closed.cartesian
import category_theory.limits.preserves.shapes.binary_products
import category_theory.adjunction.fully_faithful

/-!
# Cartesian closed functors

Define the exponential comparison morphisms for a functor which preserves binary products, and use
them to define a cartesian closed functor: one which (naturally) preserves exponentials.

## TODO
Some of the results here are true more generally for closed objects and
for closed monoidal categories, and these could be generalised.
-/

namespace category_theory

open category limits cartesian_closed

universes v u u'
variables {C : Type u} [category.{v} C]
variables {D : Type u'} [category.{v} D]

variables [has_finite_products C] [has_finite_products D]

variables [cartesian_closed C] [cartesian_closed D]
variables (F : C ⥤ D) [preserves_limits_of_shape (discrete walking_pair) F]

noncomputable theory

/--
The exponential comparison map.
`F` is a cartesian closed functor if this is an iso for all `A`.
-/
def exp_comparison (A : C) :
  exp A ⋙ F ⟶ F ⋙ exp (F.obj A) :=
transfer_nat_trans (exp.adjunction A) (exp.adjunction (F.obj A)) (prod_comparison_nat_iso F A).inv

lemma exp_comparison_ev (A B : C) :
  limits.prod.map (𝟙 (F.obj A)) ((exp_comparison F A).app B) ≫ (ev (F.obj A)).app (F.obj B) =
    inv (prod_comparison F _ _) ≫ F.map ((ev _).app _) :=
by convert transfer_nat_trans_counit _ _ (prod_comparison_nat_iso F A).inv B

def coev_exp_comparison (A B : C) :
  F.map ((coev A).app B) ≫ (exp_comparison F A).app (A ⨯ B) =
      (coev _).app (F.obj B) ≫ (exp (F.obj A)).map (inv (prod_comparison F A B)) :=
by convert unit_transfer_nat_trans _ _ (prod_comparison_nat_iso F A).inv B

lemma uncurry_exp_comparison (A B : C) :
  uncurry ((exp_comparison F A).app B) = inv (prod_comparison F _ _) ≫ F.map ((ev _).app _) :=
by rw [uncurry_eq, exp_comparison_ev]

/-- The exponential comparison map is natural in `A`. -/
lemma exp_comparison_natural_left {A A' : C} (f : A' ⟶ A) :
  exp_comparison F A ≫ whisker_left _ (pre (F.map f)) =
  whisker_right (pre f) _ ≫ exp_comparison F A' :=
begin
  ext B,
  dsimp,
  apply uncurry_injective,
  rw [uncurry_natural_left, uncurry_natural_left, uncurry_exp_comparison, uncurry_pre,
    limits.prod.map_swap_assoc, ←F.map_id, exp_comparison_ev, ←F.map_id,
    ←prod_comparison_inv_natural_assoc, ←prod_comparison_inv_natural_assoc, ←F.map_comp,
    ←F.map_comp, prod_map_pre_app_comp_ev],
end

/--
The functor `F` is cartesian closed (ie preserves exponentials) if each natural transformation
`exp_comparison F A` is an isomorphism
-/
class cartesian_closed_functor :=
(comparison_iso : ∀ A, is_iso (exp_comparison F A))

variables {L : D ⥤ C}

def frobenius_morphism (h : L ⊣ F) (A : C) :
  prod.functor.obj (F.obj A) ⋙ L ⟶ L ⋙ prod.functor.obj A :=
(transfer_nat_trans_self
  (h.comp _ _ (exp.adjunction A))
  ((exp.adjunction (F.obj A)).comp _ _ h)).symm
  (exp_comparison F A)

/-- An alternative expression for the components of the frobenius morphism. -/
lemma frobenius_morphism_app (h : L ⊣ F) (A : C) (B : D) :
  (frobenius_morphism F h A).app B =
    prod_comparison L _ _ ≫ limits.prod.map (h.counit.app _) (𝟙 _) :=
begin
  dsimp [frobenius_morphism, transfer_nat_trans_self, transfer_nat_trans, adjunction.comp],
  simp only [id_comp, comp_id],
  rw [←L.map_comp_assoc, prod.map_id_comp, assoc, exp_comparison_ev, prod.map_id_comp, assoc,
    ← F.map_id, ← prod_comparison_inv_natural_assoc, ← F.map_comp, ev_coev, F.map_id (A ⨯ L.obj B),
    comp_id],
  apply prod.hom_ext,
  { rw [assoc, ←h.counit_naturality, ←L.map_comp_assoc, assoc, inv_prod_comparison_map_fst],
    simp },
  { rw [assoc, ←h.counit_naturality, ←L.map_comp_assoc, assoc, inv_prod_comparison_map_snd],
    simp },
end.

instance frobenius_morphism_iso_of_preserves_finite_products (h : L ⊣ F) (A : C)
  [preserves_limits_of_shape (discrete walking_pair) L] [full F] [faithful F] :
is_iso (frobenius_morphism F h A) :=
begin
  apply nat_iso.is_iso_of_is_iso_app _,
  intro B,
  rw frobenius_morphism_app,
  haveI : is_iso (h.counit.app A) := by apply_instance,

  -- haveI : is_iso (limits.prod.map (𝟙 A) (h.counit.app A)) := by apply_instance,
end

/--
If the exponential comparison transformation (at `A`) is an isomorphism, then the Frobenius morphism
at `A` is an isomorphism.
-/
def frobenius_morphism_iso_of_exp_comparison_iso (h : L ⊣ F) (A : C) [is_iso (exp_comparison F A)] :
  is_iso (frobenius_morphism F h A) :=
category_theory.transfer_nat_trans_self_symm_iso _ _ _

/--
If the Frobenius morphism at `A` is an isomorphism, then the exponential comparison transformation
(at `A`) is an isomorphism.
-/
def exp_comparison_iso_of_frobenius_morphism_iso (h : L ⊣ F) (A : C)
  [i : is_iso (frobenius_morphism F h A)] :
  is_iso (exp_comparison F A) :=
@transfer_nat_trans_self_symm_of_iso _ _ _ _ _ _ _ _ _ _ _ i


-- def cartesian_closed_functor_of_left_adjoint_preserves_finite_products (h : L ⊣ F) :
--   cartesian_closed_functor F
-- TODO: If F has a left adjoint L, then F is cartesian closed if and only if
-- L (B ⨯ F A) ⟶ L B ⨯ L F A ⟶ L B ⨯ A
-- is an iso for all A ∈ D, B ∈ C.
-- Corollary: If F has a left adjoint L which preserves finite products, F is cartesian closed iff
-- F is full and faithful.

end category_theory
