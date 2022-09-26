/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import category_theory.category.basic
import category_theory.functor.basic
import category_theory.groupoid
import combinatorics.quiver.basic
import combinatorics.quiver.connected_component
import logic.relation
import tactic.nth_rewrite
import category_theory.path_category
import category_theory.quotient

/-!
# Free groupoid on a quiver

This file defines the free groupoid on a quiver, the lifting of a prefunctor to its unique
extension as a functor from the free groupoid, and proves uniqueness of this extension.

## Main results

Given the type `V` and a quiver instance on `V`:

- `free_groupoid V`: a type synonym for `V`.
- `free_groupoid_groupoid`: the `groupoid` instance on `free_groupoid V`.
- `lift`: the lifting of a prefunctor from `V` to `V'` where `V'` is a groupoid, to a functor.
  `free_groupoid V ⥤ V'`.
- `lift_spec` and `lift_unique`: the proofs that, respectively, `lift` indeed is a lifting
  and is the unique one.

## Implementation notes

The free groupoid is first defined by symmetrifying the quiver, taking the induced path category
and finally quotienting by the reducibility relation.

-/


open set classical function relation
local attribute [instance] prop_decidable

namespace category_theory
namespace groupoid
namespace free

universes u v u' v'

variables {V : Type u} [quiver.{v+1} V]

abbreviation quiver.hom.to_pos {X Y : V} (f : X ⟶ Y) :
  (quiver.symmetrify_quiver V).hom X Y := sum.inl f

abbreviation quiver.hom.to_neg {X Y : V} (f : X ⟶ Y) :
  (quiver.symmetrify_quiver V).hom Y X := sum.inr f

abbreviation quiver.hom.to_pos_path {X Y : V} (f : X ⟶ Y) :
  ((category_theory.paths.category_paths $ quiver.symmetrify V).hom X Y) := f.to_pos.to_path

abbreviation quiver.hom.to_neg_path {X Y : V} (f : X ⟶ Y) :
  ((category_theory.paths.category_paths $ quiver.symmetrify V).hom Y X) := f.to_neg.to_path

def paths.reverse {X Y : paths $ quiver.symmetrify V} :
  (category_theory.paths.category_paths $ quiver.symmetrify V).hom X Y →
  (category_theory.paths.category_paths $ quiver.symmetrify V).hom Y X := λ p, p.reverse

def red_step : hom_rel $ paths $ quiver.symmetrify V :=
λ X Y p q, ∃ (h : Y = X) (Z) (f : (quiver.symmetrify_quiver V).hom X Z),
  (h.rec_on p = 𝟙 X) ∧ (h.rec_on q = f.to_path ≫ (quiver.reverse f).to_path)

def free_groupoid (V) [Q : quiver.{v+1} V] := quotient (@red_step V Q)

@[simp] lemma congr_reverse {X Y : paths $ quiver.symmetrify V} (p q : X ⟶ Y) :
  quotient.comp_closure red_step p q →
  quotient.comp_closure red_step (paths.reverse p) (paths.reverse q) :=
begin
  rintros ⟨_,W,XW,pp,qq,WY,⟨rfl,Z,f,epp,eqq⟩⟩,
  simp only at epp eqq,
  rw [epp,eqq],
  simp only [category.id_comp, category.assoc],
  change quotient.comp_closure red_step (paths.reverse (XW ≫ WY))
  (paths.reverse (XW ≫ (f.to_path ≫ (quiver.reverse f).to_path ≫ WY))),

  have : paths.reverse (XW ≫ WY)
       = (paths.reverse WY) ≫ (𝟙 _) ≫ (paths.reverse XW), by sorry,
  rw this,
  have : paths.reverse (XW ≫ f.to_path ≫ (quiver.reverse f).to_path ≫ WY)
       = (paths.reverse WY) ≫ ((paths.reverse (quiver.reverse f).to_path) ≫ (paths.reverse f.to_path)) ≫ (paths.reverse XW), by sorry,
  rw this,
  apply quotient.comp_closure.intro,
  simp,
  sorry
end

@[simp] lemma congr_reverse_comp {X Y : paths $ quiver.symmetrify V} (p : X ⟶ Y) :
  quotient.comp_closure red_step ((paths.reverse p) ≫ p)  (𝟙 Y) := sorry

@[simp] lemma congr_comp_reverse {X Y : paths $ quiver.symmetrify V} (p : X ⟶ Y) :
  quotient.comp_closure red_step (p ≫ (paths.reverse p)) (𝟙 X) := sorry

instance : category (free_groupoid V) := quotient.category red_step

def quot_inv {X Y : free_groupoid V} (f : X ⟶ Y) : Y ⟶ X :=
quot.lift_on f
            (λ pp, quot.mk _ $ (paths.reverse pp))
            (λ pp qq con, quot.sound $ congr_reverse pp qq con)

instance : groupoid (free_groupoid V) :=
{ inv := λ X Y f, quot_inv f
, inv_comp' := λ X Y p, quot.induction_on p $ λ pp, quot.sound $ congr_reverse_comp pp
, comp_inv' := λ X Y p, quot.induction_on p $ λ pp, quot.sound $ congr_comp_reverse pp }

def of : prefunctor V (free_groupoid V) :=
{ obj := λ X, ⟨X⟩
, map := λ X Y f, quot.mk _ f.to_pos_path}

lemma of_eq : of =
  ((quiver.symmetrify.of).comp
    paths.of).comp (quotient.functor $ @red_step V _).to_prefunctor :=
begin
  apply prefunctor.ext, rotate,
  { rintro X, refl, },
  { rintro X Y f, refl, }
end

section universal_property

variables {V' : Type u'} [groupoid V'] (φ : prefunctor V V')

def lift (φ : prefunctor V V') : free_groupoid V ⥤ V' :=
begin
  dsimp only [free_groupoid],
  fapply quotient.lift,
  { fapply paths.lift,
    fapply quiver.symmetrify.lift,
    exact φ, },
  { rintros X Y f₀ f₁ ⟨rfl,Z,c,h₁,h₂⟩,
    simp only at h₁ h₂,
    subst_vars,
    simp only [functor.map_id, functor.map_comp, paths.lift_to_path,quiver.symmetrify.lift_reverse],
    symmetry, apply groupoid.comp_inv, }
end


lemma lift_spec (φ : prefunctor V V') : of.comp (lift φ).to_prefunctor = φ :=
begin
  rw [of_eq, prefunctor.comp_assoc, prefunctor.comp_assoc, functor.to_prefunctor_comp],
  dsimp [lift],
  rw [quotient.lift_spec, paths.lift_spec, quiver.symmetrify.lift_spec],
end

lemma lift_unique_spec  (φ : prefunctor V V') (Φ : free_groupoid V ⥤ V')
  (hΦ : of.comp Φ.to_prefunctor = φ) : Φ = (lift φ) :=
begin
  apply quotient.lift_spec_unique,
  apply paths.lift_spec_unique,
  apply quiver.symmetrify.lift_spec_unique,
  { rw ←functor.to_prefunctor_comp, exact hΦ, },
  { rintros X Y f,
    rw [←functor.to_prefunctor_comp,prefunctor.comp_map, prefunctor.comp_map, paths.of_map],
    change Φ.map (inv ((quotient.functor red_step).to_prefunctor.map f.to_path)) =
    inv (Φ.map ((quotient.functor red_step).to_prefunctor.map f.to_path)),
    convert functor.map_inv Φ ((quotient.functor red_step).to_prefunctor.map f.to_path);
    simp only [inv_eq_inv], }
end

end universal_property


end free
end groupoid
end category_theory
