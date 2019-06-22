/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Michael Howes

The functor Grp → Ab which is the left adjoint
of the forgetful functor Ab → Grp.

-/

import group_theory.quotient_group

universes u v

variables (α : Type u) [group α]

def commutator : set α :=
group.normal_closure {x | ∃ p q, p * q * p⁻¹ * q⁻¹ = x}

instance : normal_subgroup (commutator α) :=
group.normal_closure.is_normal

def abelianization : Type u :=
quotient_group.quotient $ commutator α

namespace abelianization

local attribute [instance] quotient_group.left_rel normal_subgroup.to_is_subgroup

instance : comm_group (abelianization α) :=
{ mul_comm := λ x y, quotient.induction_on₂ x y $ λ a b, quotient.sound
    (group.subset_normal_closure ⟨b⁻¹,a⁻¹, by simp [mul_inv_rev, inv_inv, mul_assoc]⟩),
.. quotient_group.group _}

variable {α}

def of (x : α) : abelianization α :=
quotient.mk x

instance of.is_group_hom : is_group_hom (@of α _) :=
⟨λ _ _, rfl⟩

section lift

variables {β : Type v} [comm_group β] (f : α → β) [is_group_hom f]

lemma commutator_subset_ker : commutator α ⊆ is_group_hom.ker f  :=
group.normal_closure_subset (λ x ⟨p,q,w⟩, (is_group_hom.mem_ker f).2
  (by {rw ←w, simp [is_group_hom.map_mul f, is_group_hom.map_inv f, mul_comm]}))

def lift : abelianization α → β :=
quotient_group.lift _ f (λ x h, (is_group_hom.mem_ker f).1 (commutator_subset_ker f h))

instance lift.is_group_hom : is_group_hom (lift f) :=
quotient_group.is_group_hom_quotient_lift _ _ _

@[simp] lemma lift.of (x : α) : lift f (of x) = f x :=
rfl

theorem lift.unique
  (g : abelianization α → β) [is_group_hom g]
  (hg : ∀ x, g (of x) = f x) {x} :
  g x = lift f x :=
quotient_group.induction_on x hg

end lift

end abelianization
