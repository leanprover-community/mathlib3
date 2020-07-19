/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Michael Howes

The functor Grp → Ab which is the left adjoint
of the forgetful functor Ab → Grp.

-/
import group_theory.quotient_group
import deprecated.subgroup

universes u v

variables (α : Type u) [group α]

-- TODO this still uses unbundled subgroups, and needs to be updated.

@[derive subgroup.normal]
def commutator : subgroup α :=
subgroup.normal_closure {x | ∃ p q, p * q * p⁻¹ * q⁻¹ = x}

def abelianization : Type u :=
quotient_group.quotient (commutator α)

namespace abelianization

local attribute [instance] quotient_group.left_rel normal_subgroup.to_is_subgroup

instance : comm_group (abelianization α) :=
{ mul_comm := λ x y, quotient.induction_on₂' x y $ λ a b,
  begin
    apply quotient.sound,
    apply subgroup.subset_normal_closure,
    use b⁻¹, use a⁻¹,
    simp [mul_assoc],
  end,
.. quotient_group.group _ }

instance : inhabited (abelianization α) := ⟨1⟩

variable {α}

def of : α →* abelianization α :=
{ to_fun := quotient_group.mk,
  map_one' := rfl,
  map_mul' := λ x y, rfl }

section lift

variables {β : Type v} [comm_group β] (f : α →* β)

lemma commutator_subset_ker : commutator α ≤ f.ker :=
-- FIXME why is the apply_instance needed?
subgroup.normal_closure_le_normal (by apply_instance) (λ x ⟨p,q,w⟩, (is_group_hom.mem_ker f).2
  (by {rw ←w, simp [is_mul_hom.map_mul f, is_group_hom.map_inv f, mul_comm]}))

def lift : abelianization α →* β :=
quotient_group.lift _ f (λ x h, (is_group_hom.mem_ker f).1 (commutator_subset_ker f h))

@[simp] lemma lift.of (x : α) : lift f (of x) = f x :=
rfl

theorem lift.unique
  (g : abelianization α →* β)
  (hg : ∀ x, g (of x) = f x) {x} :
  g x = lift f x :=
quotient_group.induction_on x hg

end lift

end abelianization
