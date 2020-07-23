/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Michael Howes

The functor Grp → Ab which is the left adjoint
of the forgetful functor Ab → Grp.

-/
import group_theory.quotient_group
import tactic.group

-- TODO -- have an argument with computer scientists about whether these
-- proofs are better
--import tactic

variables (G : Type) [group G]

@[derive subgroup.normal]
def commutator : subgroup G :=
subgroup.normal_closure {x | ∃ p q, p * q * p⁻¹ * q⁻¹ = x}

def abelianization : Type :=
quotient_group.quotient (commutator G)

namespace abelianization

local attribute [instance] quotient_group.left_rel

instance : comm_group (abelianization G) :=
{ mul_comm := λ x y, quotient.induction_on₂' x y $ λ a b,
  begin
    apply quotient.sound,
    apply subgroup.subset_normal_closure,
    use b⁻¹, use a⁻¹,
    group,
  end,
.. quotient_group.group _ }

instance : inhabited (abelianization G) := ⟨1⟩

variable {G}

/-- `of` is the canonical group homomorphism from $$G$$ to $$G'$$ -/
def of : G →* abelianization G :=
{ to_fun := quotient_group.mk,
  map_one' := rfl,
  map_mul' := λ x y, rfl }

section lift

variables {H : Type} [comm_group H] (f : G →* H)

example (G : Type) [add_comm_group G] (a b : G) :
a + b + -a + -b = 0 :=
begin
  abel,
end

example (G : Type) [comm_group G] (a b : G) :
a * b * a⁻¹ * b⁻¹ = 1 :=
begin
  rw mul_comm a b,
  simp,
end

lemma commutator_subset_ker : commutator G ≤ f.ker :=

begin
  refine subgroup.normal_closure_le_normal _ _,
  { exact monoid_hom.normal_ker f},
  intro x,
  rintro ⟨p,q,rfl⟩,
  unfold_coes,
  -- some part of the API seemed to break here
  have : ∀ x, x ∈ f.ker.carrier ↔ x ∈ f.ker,
    intros, refl,
  rw this, clear this,
  rw monoid_hom.mem_ker,
  simp,
  rw mul_comm (f p) (f q),
  simp,
end

def lift : abelianization G →* H :=
quotient_group.lift _ f begin
  intro x,
  intro h,
  apply monoid_hom.mem_ker.mp,
  apply commutator_subset_ker,
  exact h,
end

@[simp] lemma lift.of (x : G) : lift f (of x) = f x :=
rfl

theorem lift.unique
  (g : abelianization G →* H)
  (hg : ∀ x, g (of x) = f x) {x} :
  g x = lift f x :=
quotient_group.induction_on x hg

end lift

end abelianization
