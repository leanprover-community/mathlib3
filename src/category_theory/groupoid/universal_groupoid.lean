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

universes u v u' v' u'' v''


section push_quiver


section

variables {V : Type u} [quiver V] {V' : Type u'} (σ : V → V')

def push {V : Type u} [quiver V] {V' : Type u'} (σ : V → V')  := V'

inductive push_quiver {V : Type u} [quiver.{v} V] {V' : Type u'} (σ : V → V') : V' → V' → Type (max u u' v)
| arrow {X Y : V} (f : X ⟶ Y) : push_quiver (σ X) (σ Y)

instance : quiver (push σ) := ⟨λ X Y, push_quiver σ X Y⟩

def of  : prefunctor V (push σ) :=
{ obj := σ,
  map := λ X Y f, push_quiver.arrow f}

postfix ` * ` := of

@[simp] lemma of_obj : ((σ *)).obj = σ := rfl

end

section reverse

variables {V : Type u} [quiver.{v+1} V] {V' : Type u'} (σ : V → V')


instance [quiver.has_reverse V] : quiver.has_reverse (push σ) :=
{ reverse' := λ a b F, by { cases F, constructor, apply quiver.reverse, exact F_f, } }

instance [h : quiver.has_involutive_reverse V] : quiver.has_involutive_reverse (push σ) :=
{ reverse' := λ a b F, by { cases F, constructor, apply quiver.reverse, exact F_f, },
  inv' :=  λ a b F, by
  { cases F, dsimp [quiver.reverse], congr, apply h.inv', } }

@[simp] lemma of_reverse [h : quiver.has_involutive_reverse V]  (X Y : V) (f : X ⟶ Y):
  (quiver.reverse $ ((σ *)).map f) = ((σ *)).map (quiver.reverse f) := rfl

variables {V'' : Type u''} [quiver.{v''+1} V'']
  (φ : prefunctor V V'') (τ : V' → V'') (h : ∀ x, φ.obj x = τ (σ x) )

end reverse

variables {V : Type u} [quiver V] {V' : Type u'} (σ : V → V')
variables {V'' : Type u''} [quiver.{v''+1} V'']
  (φ : prefunctor V V'') (τ : V' → V'') (h : ∀ x, φ.obj x = τ (σ x) )

include φ h
def lift : prefunctor (push σ) V'' :=
{ obj := τ,
  map := by { apply push_quiver.rec, rintros X Y f, rw [←h X, ←h Y], exact φ.map f, } }



lemma lift_spec_obj : (lift σ φ τ h).obj = τ := rfl

lemma lift_spec_comm : (of σ).comp (lift σ φ τ h) = φ :=
begin
  dsimp [of,lift],
  fapply prefunctor.ext,
  { rintros, simp only [prefunctor.comp_obj], symmetry, exact h X, },
  { rintros, simp only [prefunctor.comp_map], dsimp, simp, sorry, }
end

#print lift
end push_quiver

variables {V : Type u} [groupoid.{v+1} V] {V' : Type u'} (σ : V → V')

/-- Two reduction steps possible: compose composable arrows, or drop identity arrows -/
inductive red_step : hom_rel (paths (push σ))
| comp (X Y Z : V) (f : X ⟶ Y) (g : Y ⟶ Z) :
    red_step
      ((σ *).map (f ≫ g)).to_path
      (((σ *).map f).to_path ≫ ((σ *).map g).to_path)
| id (X : V) :
    red_step
      (𝟙 $ σ X)
      ((σ *).map $ 𝟙 X).to_path

/-- The underlying vertices of the free groupoid -/
def universal_groupoid {V : Type u} [groupoid.{v+1} V] {V' : Type u'} (σ : V → V') :=
  quotient (red_step σ)

instance : category (universal_groupoid σ) := quotient.category (red_step σ)

lemma congr_reverse {X Y : paths $ push σ} (p q : X ⟶ Y) :
  quotient.comp_closure (red_step σ) p q →
  quotient.comp_closure (red_step σ) (p.reverse) (q.reverse)  :=
begin
  rintros ⟨U, W, XW, pp, qq, WY, rs⟩,
  rcases rs with (⟨x, y, z, f, g⟩|⟨x⟩),
  { have : quotient.comp_closure
      (red_step σ)
      (WY.reverse
        ≫ (((σ *)).map (quiver.reverse $ f≫g)).to_path
          ≫  XW.reverse)
      (WY.reverse ≫ ((((σ *)).map (quiver.reverse g)).to_path
        ≫ (((σ *)).map (quiver.reverse f)).to_path)
          ≫ XW.reverse),
    { apply quotient.comp_closure.intro,
      have := @red_step.comp _ _ _ σ (z) (y) (x) (inv g) (inv f),
      simpa only [reverse_eq_inv, inv_eq_inv, is_iso.inv_comp] using this, },
    dsimp only [category_struct.comp] at this ⊢,
    simpa only [quiver.path.reverse, quiver.path.reverse_comp, of_reverse, reverse_eq_inv,
                inv_eq_inv, is_iso.inv_comp, quiver.path.comp_nil, quiver.path.comp_assoc,
                quiver.path.reverse_to_path] using this, },
  { have : quotient.comp_closure
      (red_step σ)
      (WY.reverse ≫ 𝟙 _ ≫  XW.reverse)
      (WY.reverse ≫ (((σ *)).map (𝟙 x)).to_path ≫ XW.reverse),
    { apply quotient.comp_closure.intro,
      have := @red_step.id _ _ _ σ  (x),
      simpa only [reverse_eq_inv, inv_eq_inv, is_iso.inv_comp] using this, },
    dsimp only [category_struct.comp, category_struct.id] at this ⊢,
    simpa only [quiver.path.reverse, quiver.path.reverse_comp, of_reverse,
                reverse_eq_inv, inv_eq_inv, is_iso.inv_id, quiver.path.comp_nil,
                quiver.path.comp_assoc, quiver.path.nil_comp] using this, },

end

lemma congr_comp_reverse {X Y : paths $ push σ} (p : X ⟶ Y) :
  quot.mk (@quotient.comp_closure _ _ (red_step σ) _ _) (p ≫ p.reverse) =
  quot.mk (@quotient.comp_closure _ _ (red_step σ) _ _) (𝟙 X) :=
begin
  apply quot.eqv_gen_sound,
  induction p with _ _ q f ih,
  { apply eqv_gen.refl, },
  { rcases f with ⟨⟨x,hx⟩,⟨y,hy⟩,f⟩,
    simp only [mem_preimage, mem_singleton_iff] at hx hy, subst_vars,
    simp only [quiver.path.reverse],
    fapply eqv_gen.trans,
    { exact q ≫ (q.reverse),},
    { apply eqv_gen.symm,
      have hx : (⟨⟨x, hx⟩, ⟨⟨y, hy⟩, f⟩⟩ : (push_quiver σ).hom (σ x) (σ y)) = σ * .map f := rfl,
      simp only [hx],
      fapply eqv_gen.trans,
      { exact q ≫ ((σ *).map (𝟙 x)).to_path ≫ q.reverse, },
      { have : ((paths.category_paths (push σ)).id $ σ x) ≫ q.reverse = q.reverse, by {simp,},
        nth_rewrite_lhs 0 ←this,
        apply eqv_gen.rel, constructor, constructor, },
      { apply eqv_gen.rel,
        have : quotient.comp_closure
               (red_step σ)
               (q ≫ (σ * .map $ f ≫ inv f).to_path ≫ q.reverse)
               (q ≫ ((σ * .map f).to_path ≫ (σ * .map $ inv f).to_path) ≫ q.reverse), by
        { apply quotient.comp_closure.intro, constructor, },
      simp only [of_reverse, reverse_eq_inv, inv_eq_inv, is_iso.hom_inv_id,
                 category.assoc] at this ⊢,
      dsimp only [category_struct.comp, quiver.hom.to_path,quiver.path.comp] at this ⊢,
      simpa only [←quiver.path.comp_assoc] using this, }, },
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
  inv_comp' := λ X Y p, quot.induction_on p $ λ pp, congr_reverse_comp σ pp,
  comp_inv' := λ X Y p, quot.induction_on p $ λ pp, congr_comp_reverse σ pp }

/-- The extension of `σ` to a functor -/
def extend : V ⥤ (universal_groupoid σ) :=
{ obj := λ X, ⟨σ X⟩,
  map := λ X Y f, quot.mk _ (((σ *)).map f).to_path,
  map_id' := λ X, by
  { dsimp, symmetry,
    apply quot.sound,
    apply quotient.comp_closure.of,
    constructor, },
  map_comp' := λ X Y Z f g, by
  { dsimp,
    apply quot.sound,
    apply quotient.comp_closure.of,
    constructor, } }

section ump

def lift {V'' : Type*} [groupoid V'']
  (θ : V ⥤ V'') (τ₀ : V' → V'') (hτ₀ : θ.obj = τ₀ ∘ σ) : (universal_groupoid σ) ⥤ V'' :=
quotient.lift _
  (paths.lift $ by {}) -- need ump of `push` and good to go
  (sorry)



end ump

end free
end groupoid
end category_theory
