/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.functor

/-!
# Braided and symmetric monoidal categories

The basic definitions of braided monoidal categories, and symmetric monoidal categories,
as well as braided functors.

## Implementation note

We make `braided_monoidal_category` another typeclass, but then have `symmetric_monoidal_category`
extend this. The rationale is that we are not carrying any additional data,
just requiring a property.

## Future work

* Construct the Drinfeld center of a monoidal category as a braided monoidal category.
* Say something about pseudo-natural transformations.

## References

 * Proposition 1 of André Joyal and Ross Street, "Braided monoidal categories", Macquarie Math Reports 860081 (1986).
 * Proposition 2.1 of André Joyal and Ross Street, "Braided tensor categories" , Adv. Math. 102 (1993), 20–78.
 * Exercise 8.1.6 of Etingof, Gelaki, Nikshych, Ostrik, "Tensor categories", vol 25, Mathematical Surveys and Monographs (2015), AMS.

-/

open category_theory

universes v v₁ v₂ v₃ u u₁ u₂ u₃

namespace category_theory

/--
A braided monoidal category is a monoidal category equipped with a braiding isomorphism
`β_ X Y : X ⊗ Y ≅ Y ⊗ X`
which is natural in both arguments,
and also satisfies the two hexagon identities.
-/
class braided_category (C : Type u) [category.{v} C] [monoidal_category.{v} C] :=
-- braiding natural iso:
(braiding             : Π X Y : C, X ⊗ Y ≅ Y ⊗ X)
(braiding_naturality' : ∀ {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'),
  (f ⊗ g) ≫ (braiding Y Y').hom = (braiding X X').hom ≫ (g ⊗ f) . obviously)
-- hexagon identities:
(hexagon_forward'     : Π X Y Z : C,
    (α_ X Y Z).hom ≫ (braiding X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom
  = ((braiding X Y).hom ⊗ (𝟙 Z)) ≫ (α_ Y X Z).hom ≫ ((𝟙 Y) ⊗ (braiding X Z).hom)
  . obviously)
(hexagon_reverse'     : Π X Y Z : C,
    (α_ X Y Z).inv ≫ (braiding (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv
  = ((𝟙 X) ⊗ (braiding Y Z).hom) ≫ (α_ X Z Y).inv ≫ ((braiding X Z).hom ⊗ (𝟙 Y))
  . obviously)

restate_axiom braided_category.braiding_naturality'
attribute [simp, reassoc] braided_category.braiding_naturality
restate_axiom braided_category.hexagon_forward'
restate_axiom braided_category.hexagon_reverse'
attribute [reassoc] braided_category.hexagon_forward braided_category.hexagon_reverse

open braided_category

notation `β_` := braiding

namespace braided_category
variables (C : Type u)
variables [category.{v} C]
variables [monoidal_category.{v} C]
variables [braided_category.{v} C]
variables (X Y Z : C)

@[simp, reassoc]
lemma braiding_naturality_inv {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
  (f ⊗ g) ≫ (braiding Y' Y).inv = (braiding X' X).inv ≫ (g ⊗ f) :=
by rw ← cancel_mono ((β_ Y' Y).hom); simp only [iso.inv_hom_id_assoc, category.comp_id, braiding_naturality, iso.inv_hom_id, category.assoc]


lemma left_unitor_braiding : β_ _ _ ≪≫ λ_ X = ρ_ X :=
begin
  ext, simp only [iso.trans_hom],
  rw [← monoidal_category.tensor_right_iff],
  suffices :
    ((β_ X (𝟙_ C)).hom ⊗ 𝟙 (𝟙_ C)) ≫ ((λ_ X).hom ⊗ 𝟙 (𝟙_ C)) =
    (ρ_ X).hom ⊗ 𝟙 (𝟙_ C),
  { simpa only [← monoidal_category.tensor_comp, category.id_comp] using this },
  rw ← monoidal_category.left_unitor_tensor,
  rw ← category.assoc,
  rw ← iso.eq_comp_inv,
  simp only [← cancel_mono (𝟙 (𝟙_ C) ⊗ (β_ X (𝟙_ C)).hom), category.assoc],

  show ((β_ X (𝟙_ C)).hom ⊗ 𝟙 (𝟙_ C)) ≫
      (α_ (𝟙_ C) X (𝟙_ C)).hom ≫ (𝟙 (𝟙_ C) ⊗ (β_ X (𝟙_ C)).hom) =
    ((ρ_ X).hom ⊗ 𝟙 (𝟙_ C)) ≫ (λ_ (X ⊗ 𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ (β_ X (𝟙_ C)).hom),
  rw ← hexagon_forward,
  rw ← monoidal_category.triangle_assoc_comp_left,
  simp only [category.assoc, iso.cancel_iso_hom_left],
  rw ← monoidal_category.left_unitor_inv_naturality,
  rw braiding_naturality_assoc,
  simp only [iso.cancel_iso_hom_left],
  rw [← monoidal_category.left_unitor_tensor, category.assoc, iso.hom_inv_id], simp,
end

lemma left_unitor_braiding' : (β_ _ _).symm ≪≫ ρ_ X = λ_ X :=
by rw [← left_unitor_braiding, iso.symm_self_id_assoc]

@[simp, reassoc]
lemma braiding_left_unit_hom : (β_ _ _).hom ≫ (λ_ X).hom = (ρ_ X).hom :=
begin
  have := congr_arg iso.hom (left_unitor_braiding C X),
  simpa
end

@[simp, reassoc]
lemma braiding_left_unit_inv : (λ_ X).inv ≫ (β_ _ _).inv = (ρ_ X).inv :=
begin
  have := congr_arg iso.inv (left_unitor_braiding C X),
  simpa
end

lemma foo {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) [is_iso g] :
  h = f ≫ g ↔ f = h ≫ inv g :=
sorry

lemma foo' {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) [is_iso g] :
  f ≫ g = h ↔ f = h ≫ inv g :=
sorry

lemma foo'' {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) [is_iso f] :
  f ≫ g = h ↔ g = inv f ≫ h :=
sorry

lemma foo''' {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) [is_iso f] :
  h = f ≫ g ↔ inv f ≫ h = g :=
sorry

open monoidal_category
lemma right_unitor_braiding' :
  β_ _ _ ≪≫ ρ_ X = λ_ X :=
begin
  ext, simp,
  have := @hexagon_reverse C _ _ _ (𝟙_ _) (𝟙_ _) X,
  rw ← cancel_mono ((ρ_ X).hom ⊗ 𝟙 (𝟙_ _)) at this,
  simp at this,
  simp only [← tensor_comp, ← braiding_naturality] at this,
  -- rw [monoidal_category.left_unitor_eq_right_unitor] at this,
  simp only [triangle_assoc_comp_right_assoc, left_unitor_eq_right_unitor] at this,
  simp at this,
  rw [← iso.eq_inv_comp] at this,
  rw [← tensor_right_iff, this], clear this,
  simp,
  -- rw [← hexagon_reverse_assoc],
  rw [iso.eq_inv_comp, ← braiding_naturality_assoc],
  rw cancel_epi,
  rw [← category.assoc],
  rw cancel_mono,

  rw [← cancel_epi (𝟙 (𝟙_ C) ⊗ (β_ (𝟙_ C) X).hom), ← hexagon_reverse],
  admit
end

lemma right_unitor_braiding :
  β_ _ _ ≪≫ ρ_ X = λ_ X :=
begin
  ext, simp,
  rw [← monoidal_category.tensor_right_iff],
  suffices :
    ((β_ (𝟙_ C) X).hom ⊗ 𝟙 (𝟙_ C)) ≫ ((ρ_ X).hom ⊗ 𝟙 (𝟙_ C)) =
    (λ_ X).hom ⊗ 𝟙 (𝟙_ C),
  { simpa only [← monoidal_category.tensor_comp, category.id_comp] using this },

  -- have := @hexagon_forward C _ _ _ (𝟙_ _) X (𝟙_ _),
  -- rw foo at this,
  have := @hexagon_reverse C _ _ _ (𝟙_ _) (𝟙_ _) X,
  rw [foo''', foo'''] at this,
  rw ← this, simp,
  -- simp at this,
  -- rw this, simp,
  admit
  -- rw ← monoidal_category.triangle_assoc_comp_right,
  -- rw ← monoidal_category.triangle,

  -- -- rw ← monoidal_category.left_unitor_tensor,
  -- rw ← category.assoc,
  -- -- rw ← iso.eq_comp_inv,
  -- simp only [← cancel_mono (𝟙 (𝟙_ C) ⊗ (β_ X (𝟙_ C)).hom), category.assoc],

  -- show ((β_ X (𝟙_ C)).hom ⊗ 𝟙 (𝟙_ C)) ≫
  --     (α_ (𝟙_ C) X (𝟙_ C)).hom ≫ (𝟙 (𝟙_ C) ⊗ (β_ X (𝟙_ C)).hom) =
  --   ((ρ_ X).hom ⊗ 𝟙 (𝟙_ C)) ≫ (λ_ (X ⊗ 𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ (β_ X (𝟙_ C)).hom),
  -- rw ← hexagon_forward,


  -- -- rw ← monoidal_category.triangle,

  -- rw ← monoidal_category.triangle_assoc_comp_right,

  -- rw iso.eq_inv_comp,

  -- -- rw ← category.assoc,
  -- -- have := cancel_mono (𝟙 (𝟙_ C) ⊗ (β_ (𝟙_ C) X).hom),
  -- -- rw ← cancel_mono (𝟙 (𝟙_ C) ⊗ (β_ (𝟙_ C) X).hom),
  -- -- simp [- iso.cancel_iso_hom_right_assoc, category.assoc],

  -- -- suffices : (𝟙 (𝟙_ C) ⊗ (β_ (𝟙_ C) X).hom) ≫
  -- --     (α_ (𝟙_ C) X (𝟙_ C)).inv ≫ ((β_ (𝟙_ C) X).hom ⊗ 𝟙 (𝟙_ C)) =
  -- --   ((ρ_ X).hom ⊗ 𝟙 (𝟙_ C)) ≫ (λ_ (X ⊗ 𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ (β_ X (𝟙_ C)).hom),
  -- -- { simpa },
  -- rw ← hexagon_forward,
  -- rw ← monoidal_category.triangle_assoc_comp_left,
  -- simp only [category.assoc, iso.cancel_iso_hom_left],
  -- rw ← monoidal_category.left_unitor_inv_naturality,
  -- rw braiding_naturality_assoc,
  -- simp,
  -- rw [← monoidal_category.left_unitor_tensor, category.assoc, iso.hom_inv_id], simp,
end

@[simp, reassoc]
lemma braiding_right_unit_hom : (β_ _ _).hom ≫ (ρ_ X).hom = (λ_ X).hom :=
begin
  have := congr_arg iso.hom (right_unitor_braiding C X),
  simpa
end

@[simp, reassoc]
lemma braiding_right_unit_inv : (ρ_ X).inv ≫ (β_ _ _).inv = (λ_ X).inv :=
begin
  have := congr_arg iso.inv (right_unitor_braiding C X),
  simpa
end

@[simp, reassoc]
lemma braiding_left_inv_unit_hom : (β_ _ _).inv ≫ (λ_ X).hom = (ρ_ X).hom :=
by rw ← cancel_epi ((β_ (𝟙_ C) X).hom); simp

@[simp, reassoc]
lemma braiding_left_hom_unit_inv : (λ_ X).inv ≫ (β_ _ _).hom = (ρ_ X).inv :=
by rw ← cancel_mono ((β_ (𝟙_ C) X).inv); simp

@[simp, reassoc]
lemma braiding_inv_right_unit_hom : (β_ _ _).inv ≫ (ρ_ X).hom = (λ_ X).hom :=
by rw ← cancel_epi ((β_ X (𝟙_ C)).hom); simp

@[simp, reassoc]
lemma braiding_hom_right_unit_inv : (ρ_ X).inv ≫ (β_ _ _).hom = (λ_ X).inv :=
by rw ← cancel_mono ((β_ X (𝟙_ C)).inv); simp

end braided_category

section prio
set_option default_priority 100 -- see Note [default priority]

/--
A symmetric monoidal category is a braided monoidal category for which the braiding is symmetric.
-/
class symmetric_category (C : Type u) [category.{v} C] [monoidal_category.{v} C]
   extends braided_category.{v} C :=
-- braiding symmetric:
(symmetry' : ∀ X Y : C, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y) . obviously)

end prio

restate_axiom symmetric_category.symmetry'
attribute [simp,reassoc] symmetric_category.symmetry

namespace symmetric_category

variables (C : Type u₁) [category.{v₁} C] [monoidal_category C] [symmetric_category C]

lemma braiding_inv {X Y : C} : (β_ X Y).inv = (β_ Y X).hom :=
by rw [← cancel_epi (β_ X Y).hom, iso.hom_inv_id, symmetry]

end symmetric_category

variables (C : Type u₁) [category.{v₁} C] [monoidal_category C] [braided_category C]
variables (D : Type u₂) [category.{v₂} D] [monoidal_category D] [braided_category D]
variables (E : Type u₃) [category.{v₃} E] [monoidal_category E] [braided_category E]

/--
A braided functor between braided monoidal categories is a monoidal functor
which preserves the braiding.
-/
structure braided_functor extends monoidal_functor C D :=
(braided' : ∀ X Y : C, map (β_ X Y).hom = inv (μ X Y) ≫ (β_ (obj X) (obj Y)).hom ≫ μ Y X . obviously)

restate_axiom braided_functor.braided'
-- It's not totally clear that `braided` deserves to be a `simp` lemma.
-- The principle being applying here is that `μ` "doesn't weigh much"
-- (similar to all the structural morphisms, e.g. associators and unitors)
-- and the `simp` normal form is determined by preferring `obj` over `map`.
attribute [simp] braided_functor.braided

namespace braided_functor

/-- The identity braided monoidal functor. -/
@[simps] def id : braided_functor C C :=
{ braided' := λ X Y, by { dsimp, simp, },
  .. monoidal_functor.id C }

instance : inhabited (braided_functor C C) := ⟨id C⟩

variables {C D E}

/-- The composition of braided monoidal functors. -/
@[simps]
def comp (F : braided_functor C D) (G : braided_functor D E) : braided_functor C E :=
{ braided' := λ X Y, by { dsimp, simp, },
  ..(monoidal_functor.comp F.to_monoidal_functor G.to_monoidal_functor) }

end braided_functor

end category_theory
