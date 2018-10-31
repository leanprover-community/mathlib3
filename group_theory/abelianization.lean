/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

The functor Grp → Ab which is the left adjoint
of the forgetful functor Ab → Grp.

-/

import group_theory.quotient_group

universes u v

variables (α : Type u) [group α]

def commutator : set α :=
{ x | ∃ L : list α, (∀ z ∈ L, ∃ p q, p * q * p⁻¹ * q⁻¹ = z) ∧ L.prod = x }

instance : normal_subgroup (commutator α) :=
{ one_mem := ⟨[], by simp⟩,
  mul_mem := λ x y ⟨L1, HL1, HP1⟩ ⟨L2, HL2, HP2⟩,
    ⟨L1 ++ L2, list.forall_mem_append.2 ⟨HL1, HL2⟩, by simp*⟩,
  inv_mem := λ x ⟨L, HL, HP⟩, ⟨L.reverse.map has_inv.inv,
    λ x hx, let ⟨y, h3, h4⟩ := list.exists_of_mem_map hx in
      let ⟨p, q, h5⟩ := HL y (list.mem_reverse.1 h3) in
      ⟨q, p, by rw [← h4, ← h5]; simp [mul_assoc]⟩,
    by rw ← HP; from list.rec_on L (by simp) (λ hd tl ih,
      by rw [list.reverse_cons, list.map_append, list.prod_append, ih]; simp)⟩,
  normal := λ x ⟨L, HL, HP⟩ g, ⟨L.map $ λ z, g * z * g⁻¹,
    λ x hx, let ⟨y, h3, h4⟩ := list.exists_of_mem_map hx in
      let ⟨p, q, h5⟩ := HL y h3 in
      ⟨g * p * g⁻¹, g * q * g⁻¹,
      by rw [← h4, ← h5]; simp [mul_assoc]⟩,
    by rw ← HP; from list.rec_on L (by simp) (λ hd tl ih,
      by rw [list.map_cons, list.prod_cons, ih]; simp [mul_assoc])⟩, }

def abelianization : Type u :=
quotient_group.quotient $ commutator α

namespace abelianization

local attribute [instance] quotient_group.left_rel normal_subgroup.to_is_subgroup

instance : comm_group (abelianization α) :=
{ mul_comm := λ x y, quotient.induction_on₂ x y $ λ m n,
    quotient.sound $ ⟨[n⁻¹*m⁻¹*n*m],
      by simp; refine ⟨n⁻¹, m⁻¹, _⟩; simp,
      by simp [mul_assoc]⟩,
  .. quotient_group.group _ }

variable {α}

def of (x : α) : abelianization α :=
quotient.mk x

instance of.is_group_hom : is_group_hom (@of α _) :=
⟨λ _ _, rfl⟩

section lift

variables {β : Type v} [comm_group β] (f : α → β) [is_group_hom f]

def lift : abelianization α → β :=
quotient_group.lift _ f $ λ x ⟨L, HL, hx⟩,
hx ▸ list.rec_on L (λ _, is_group_hom.one f) (λ hd tl HL ih,
  by rw [list.forall_mem_cons] at ih;
    rcases ih with ⟨⟨p, q, hpq⟩, ih⟩;
    specialize HL ih; rw [list.prod_cons, is_group_hom.mul f, ← hpq, HL];
    simp [is_group_hom.mul f, is_group_hom.inv f, mul_comm]) HL

instance lift.is_group_hom : is_group_hom (lift f) :=
quotient_group.is_group_hom_quotient_lift _ _ _

@[simp] lemma lift.of (x : α) : lift f (of x) = f x := rfl

theorem lift.unique
  (g : abelianization α → β) [is_group_hom g]
  (hg : ∀ x, g (of x) = f x) {x} :
  g x = lift f x :=
quotient.induction_on x $ λ m, hg m

end lift

end abelianization