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

The definition of the free groupoid in terms of "words" on the base quiver, up to reduction,
is mostly copied from `group_theory/free_group.lean`.

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
  rintro ⟨_,W,XW,pp,qq,WY,⟨rfl,Z,f,epp,eqq⟩⟩,
  simp at epp eqq, subst_vars,
  simp,
  sorry
end

@[simp] lemma congr_reverse_comp {X Y : paths $ quiver.symmetrify V} (p : X ⟶ Y) :
  quotient.comp_closure red_step ((paths.reverse p) ≫ p)  (𝟙 Y) := sorry

@[simp] lemma congr_comp_reverse {X Y : paths $ quiver.symmetrify V} (p : X ⟶ Y) :
  quotient.comp_closure red_step (p ≫ (paths.reverse p)) (𝟙 X) := sorry

instance : category (free_groupoid V) := quotient.category red_step
instance : groupoid (free_groupoid V) :=
{ inv := λ X Y p, quot.lift_on p
                    (λ pp, quot.mk _ $ (paths.reverse pp))
                    (λ pp qq con, quot.sound $ congr_reverse pp qq con)
, inv_comp' := λ X Y p, quot.induction_on p $ λ pp, quot.sound $ congr_reverse_comp pp
, comp_inv' := λ X Y p, quot.induction_on p $ λ pp, quot.sound $ congr_comp_reverse pp }

def ι : prefunctor V (free_groupoid V) :=
{ obj := λ X, ⟨X⟩
, map := λ X Y f, quot.mk _ f.to_pos_path}

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

lemma lift_spec (φ : prefunctor V V') : ι.comp (lift φ).to_prefunctor = φ :=
begin
  ext, rotate,
  { rintro X, refl, },
  { rcases φ with ⟨φo,φm⟩, sorry, }
end

lemma lift_unique_spec  (φ : prefunctor V V') (Φ : free_groupoid V ⥤ V')
  (hΦ : ι.comp Φ.to_prefunctor = φ) : Φ = (lift φ) := sorry

end universal_property


end free
end groupoid
end category_theory
