/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import category_theory.category.basic
import category_theory.functor.basic
import category_theory.groupoid
import category_theory.groupoid.basic
import combinatorics.quiver.basic
import combinatorics.quiver.symmetric
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

section push_quiver

variables {V : Type u} [quiver.{v+1} V] {V' : Type u'} (σ : V → V')

def push {V : Type u} [quiver.{v+1} V] {V' : Type u'} (σ : V → V')  := V'
def push_quiver : quiver (push σ) := ⟨λ X' Y', Σ (X: set.preimage σ {X'}) (Y : set.preimage σ {Y'}), X.val ⟶ Y.val⟩
instance : quiver (push σ) := push_quiver σ

def push_prefunctor : prefunctor V (push σ) :=
{ obj := σ,
  map := λ X Y f, ⟨⟨X,by simp,⟩,⟨Y,by simp⟩,f⟩}

@[simp] lemma push_prefunctor_obj : (push_prefunctor σ).obj = σ := rfl

instance [quiver.has_reverse V] : quiver.has_reverse (push σ) :=
{ reverse' := λ a b F, ⟨F.2.1,F.1,quiver.reverse F.2.2⟩ }

instance [h : quiver.has_involutive_reverse V] : quiver.has_involutive_reverse (push σ) :=
{ reverse' := λ a b F, ⟨F.2.1,F.1,quiver.reverse F.2.2⟩,
  inv' :=  λ a b ⟨A,B,f⟩, by
  { dsimp only [quiver.reverse],
    fapply sigma.eq, refl,
    fapply sigma.eq, refl,
    apply h.inv', }}

@[simp] lemma push_prefunctor_reverse [h : quiver.has_involutive_reverse V]  (X Y : V) (f : X ⟶ Y):
  (quiver.reverse $ (push_prefunctor σ).map f) = (push_prefunctor σ).map (quiver.reverse f) := rfl

end push_quiver

variables {V : Type u} [groupoid.{v+1} V] {V' : Type u'} (σ : V → V')

/-- Composing composable arrows -/
inductive red_step : hom_rel (paths (push σ))
| step (X Y Z : V) (f : X ⟶ Y) (g : Y ⟶ Z) :
    red_step
      ((push_prefunctor σ).map (f ≫ g)).to_path
      (((push_prefunctor σ).map f).to_path ≫ ((push_prefunctor σ).map g).to_path)

/-- Collapsing identity arrows -/
inductive red_step' : hom_rel (paths $ push σ)
| drop (X : V) :
    red_step'
      (𝟙 $ σ X)
      ((push_prefunctor σ).map $ 𝟙 X).to_path

def red_step'' : hom_rel (paths $ push σ) :=
λ X Y f g, red_step σ f g ∨ red_step' σ f g

/-- The underlying vertices of the free groupoid -/
def universal_groupoid {V : Type u} [groupoid.{v+1} V] {V' : Type u'} (σ : V → V') :=
  quotient (red_step'' σ)

instance : category (universal_groupoid σ) := quotient.category (red_step'' σ)

lemma congr_reverse {X Y : paths $ push σ} (p q : X ⟶ Y) :
  quotient.comp_closure (red_step σ) p q →
  quotient.comp_closure (red_step σ) (p.reverse) (q.reverse)  :=
begin
  rintros ⟨U, W, XW, pp, qq, WY, ⟨x, y, z, f, g⟩⟩,
  have : quotient.comp_closure
    (red_step σ)
    (WY.reverse
      ≫ ((push_prefunctor σ).map (quiver.reverse $ f≫g)).to_path
        ≫  XW.reverse)
    (WY.reverse ≫ (((push_prefunctor σ).map (quiver.reverse g)).to_path
      ≫ ((push_prefunctor σ).map (quiver.reverse f)).to_path)
        ≫ XW.reverse),
  { apply quotient.comp_closure.intro,
    have := @red_step.step _ _ _ σ (z) (y) (x) (inv g) (inv f),
    simpa only [reverse_eq_inv, inv_eq_inv, is_iso.inv_comp] using this, },
  dsimp only [category_struct.comp] at this ⊢,
  simpa only [quiver.path.reverse, quiver.path.reverse_comp, push_prefunctor_reverse, reverse_eq_inv,
             inv_eq_inv, is_iso.inv_comp, quiver.path.comp_nil, quiver.path.comp_assoc,
             quiver.path.reverse_to_path] using this,
end

lemma congr_comp_reverse {X Y : paths $ push σ} (p : X ⟶ Y) :
  quot.mk (@quotient.comp_closure _ _ (red_step σ) _ _) (p ≫ p.reverse) =
  quot.mk (@quotient.comp_closure _ _ (red_step σ) _ _) (𝟙 X) :=
begin
  apply quot.eqv_gen_sound,
  induction p with _ _ q f ih,
  { apply eqv_gen.refl, },
  { simp only [quiver.path.reverse],
    fapply eqv_gen.trans,
    { exact q ≫ q.reverse, },
    { apply eqv_gen.symm, apply eqv_gen.rel,
      have : quotient.comp_closure
               (red_step σ) (q ≫ (𝟙 _) ≫ q.reverse)
               (q ≫ (f.to_path ≫ (quiver.reverse f).to_path) ≫ q.reverse), by
      { apply quotient.comp_closure.intro, apply red_step.step, },
      have that : q.cons f = q.comp f.to_path, by refl, rw that,
      simp only [category.assoc, category.id_comp] at this ⊢,
      simp only [category_struct.comp, quiver.path.comp_assoc] at this ⊢,
      exact this, },
    { exact ih }, },
end

lemma congr_reverse_comp {X Y : paths $ push σ} (p : X ⟶ Y) :
  quot.mk (@quotient.comp_closure _ _ (red_step σ) _ _) (p.reverse ≫ p) =
  quot.mk (@quotient.comp_closure _ _ (red_step σ) _ _) (𝟙 Y) :=
begin
  nth_rewrite 1 ←quiver.path.reverse_reverse p,
  apply congr_comp_reverse,
end


/-- The inverse of an arrow in the free groupoid -/
def quot_inv {X Y : universal_groupoid σ} (f : X ⟶ Y) : Y ⟶ X :=
quot.lift_on f
            (λ pp, quot.mk _ $ pp.reverse)
            (λ pp qq con, quot.sound $ congr_reverse σ pp qq con)

instance : groupoid (universal_groupoid σ) :=
{ inv := λ (X Y : universal_groupoid σ) (f : X ⟶ Y), quot_inv σ f,
  inv_comp' := λ X Y p, quot.induction_on p $ λ pp, sorry,
  comp_inv' := λ X Y p, quot.induction_on p $ λ pp, sorry }

/-- The extension of `σ` to a functor -/
def of : V ⥤ (universal_groupoid σ) :=
{ obj := λ X, ⟨σ X⟩,
  map := λ X Y f, quot.mk _ ((push_prefunctor σ).map f).to_path,
  map_id' := λ X, by { dsimp [push_prefunctor], simp, },
  map_comp' := sorry }


section universal_property

end universal_property

end free
end groupoid
end category_theory
