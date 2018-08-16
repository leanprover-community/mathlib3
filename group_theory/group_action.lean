/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.set.finite group_theory.coset

universes u v
variables {α : Type u} {β : Type v}

class is_monoid_action [monoid α] (f : α → β → β) : Prop :=
(one : ∀ a : β, f (1 : α) a = a)
(mul : ∀ (x y : α) (a : β), f (x * y) a = f x (f y a))

namespace is_monoid_action

variables [monoid α] (f : α → β → β) [is_monoid_action f]

def orbit (a : β) := set.range (λ x : α, f x a)

@[simp] lemma mem_orbit_iff {f : α → β → β} [is_monoid_action f] {a b : β} :
  b ∈ orbit f a ↔ ∃ x : α, f x a = b :=
iff.rfl

@[simp] lemma mem_orbit (a : β) (x : α) :
  f x a ∈ orbit f a :=
⟨x, rfl⟩

@[simp] lemma mem_orbit_self (a : β) :
  a ∈ orbit f a :=
⟨1, show f 1 a = a, by simp [is_monoid_action.one f]⟩

instance orbit_fintype (a : β) [fintype α] [decidable_eq β] :
  fintype (orbit f a) := set.fintype_range _

def stabilizer (a : β) : set α :=
{x : α | f x a = a}

@[simp] lemma mem_stabilizer_iff {f : α → β → β} [is_monoid_action f] {a : β} {x : α} :
  x ∈ stabilizer f a ↔ f x a = a :=
iff.rfl

def fixed_points : set β := {a : β | ∀ x, x ∈ stabilizer f a}

@[simp] lemma mem_fixed_points {f : α → β → β} [is_monoid_action f] {a : β} :
  a ∈ fixed_points f ↔ ∀ x : α, f x a = a := iff.rfl

lemma mem_fixed_points' {f : α → β → β} [is_monoid_action f] {a : β} : a ∈ fixed_points f ↔
  (∀ b, b ∈ orbit f a → b = a) :=
⟨λ h b h₁, let ⟨x, hx⟩ := mem_orbit_iff.1 h₁ in hx ▸ h x,
λ h b, mem_stabilizer_iff.2 (h _ (mem_orbit _ _ _))⟩

end is_monoid_action

class is_group_action [group α] (f : α → β → β) extends is_monoid_action f

namespace is_group_action
variables [group α] (f : α → β → β) [is_group_action f]
open is_monoid_action

def to_perm (g : α) : equiv.perm β :=
{ to_fun := f g,
  inv_fun := f g⁻¹,
  left_inv := λ a, by rw [← is_monoid_action.mul f, inv_mul_self, is_monoid_action.one f],
  right_inv := λ a, by rw [← is_monoid_action.mul f, mul_inv_self, is_monoid_action.one f] }

instance : is_group_hom (to_perm f) :=
{ mul := λ x y, equiv.ext _ _ (λ a, is_monoid_action.mul f x y a) }

lemma bijective (g : α) : function.bijective (f g) :=
(to_perm f g).bijective

lemma orbit_eq_iff {f : α → β → β} [is_monoid_action f] {a b : β} :
   orbit f a = orbit f b ↔ a ∈ orbit f b:=
⟨λ h, h ▸ mem_orbit_self _ _,
λ ⟨x, (hx : f x b = a)⟩, set.ext (λ c, ⟨λ ⟨y, (hy : f y a = c)⟩, ⟨y * x,
  show f (y * x) b = c, by rwa [is_monoid_action.mul f, hx]⟩,
  λ ⟨y, (hy : f y b = c)⟩, ⟨y * x⁻¹,
    show f (y * x⁻¹) a = c, by
      conv {to_rhs, rw [← hy, ← mul_one y, ← inv_mul_self x, ← mul_assoc,
        is_monoid_action.mul f, hx]}⟩⟩)⟩

instance (a : β) : is_subgroup (stabilizer f a) :=
{ one_mem := is_monoid_action.one _ _,
  mul_mem := λ x y (hx : f x a = a) (hy : f y a = a),
    show f (x * y) a = a, by rw is_monoid_action.mul f; simp *,
  inv_mem := λ x (hx : f x a = a), show f x⁻¹ a = a,
    by rw [← hx, ← is_monoid_action.mul f, inv_mul_self, is_monoid_action.one f, hx] }

open quotient_group

noncomputable def orbit_equiv_quotient_stabilizer (a : β) :
  orbit f a ≃ quotient (stabilizer f a) :=
equiv.symm (@equiv.of_bijective _ _
  (λ x : quotient (stabilizer f a), quotient.lift_on' x
    (λ x, (⟨f x a, mem_orbit _ _ _⟩ : orbit f a))
    (λ g h (H : _ = _), subtype.eq $ (is_group_action.bijective f (g⁻¹)).1
      $ show f g⁻¹ (f g a) = f g⁻¹ (f h a),
      by rw [← is_monoid_action.mul f, ← is_monoid_action.mul f,
        H, inv_mul_self, is_monoid_action.one f]))
⟨λ g h, quotient.induction_on₂' g h (λ g h H, quotient.sound' $
  have H : f g a = f h a := subtype.mk.inj H,
  show f (g⁻¹ * h) a = a,
  by rw [is_monoid_action.mul f, ← H, ← is_monoid_action.mul f, inv_mul_self,
    is_monoid_action.one f]),
  λ ⟨b, ⟨g, hgb⟩⟩, ⟨g, subtype.eq hgb⟩⟩)

end is_group_action