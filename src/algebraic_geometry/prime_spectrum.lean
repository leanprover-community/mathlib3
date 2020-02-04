/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import topology.opens
import ring_theory.ideals

/-!
# Prime spectrum of a commutative ring

The prime spectrum of a commutative ring is the type of all prime ideals.
It is naturally endowed with a topology: the Zariski topology.

(It is also naturally endowed with a sheaf of rings,
but that sheaf is not constructed in this file.
It should be contributed to mathlib in future work.)

## Inspiration/contributors

The contents of this file draw inspiration from
https://github.com/ramonfmir/lean-scheme
which has contributions from Ramon Fernandez Mir, Kevin Buzzard, Kenny Lau,
and Chris Hughes (on an earlier repository).

-/

universe variables u

section move_this

def topological_space.of_closed {α : Type u} (T : set (set α))
  (empty_mem : ∅ ∈ T) (sInter_mem : ∀ A ⊆ T, ⋂₀ A ∈ T) (union_mem : ∀ A B ∈ T, A ∪ B ∈ T) :
  topological_space α :=
{ is_open := λ X, -X ∈ T,
  is_open_univ := by simp [empty_mem],
  is_open_inter := λ s t hs ht, by simpa [set.compl_inter] using union_mem (-s) (-t) hs ht,
  is_open_sUnion := λ s hs,
    by rw set.compl_sUnion; exact sInter_mem (set.compl '' s)
    (λ z ⟨y, hy, hz⟩, by simpa [hz.symm] using hs y hy) }

end move_this

variables (R : Type u) [comm_ring R]

def prime_spectrum := {I : ideal R // I.is_prime}

variable {R}

namespace prime_spectrum

abbreviation as_ideal (x : prime_spectrum R) : ideal R := x.val

lemma as_ideal_is_prime (x : prime_spectrum R) :
  x.as_ideal.is_prime := x.2

def zero_locus (I : set R) : set (prime_spectrum R) :=
{x | I ⊆ x.as_ideal}

lemma mem_zero_locus (x : prime_spectrum R) (I : set R) :
  x ∈ zero_locus I ↔ I ⊆ x.as_ideal := iff.rfl

lemma zero_locus_empty_of_one_mem (I : set R) (h : (1:R) ∈ I) :
  zero_locus I = ∅ :=
begin
  rw set.eq_empty_iff_forall_not_mem,
  intros x hx,
  rw mem_zero_locus at hx,
  have x_prime := x.as_ideal_is_prime,
  have eq_top : x.as_ideal = ⊤, { rw ideal.eq_top_iff_one, exact hx h },
  apply x_prime.1 eq_top,
end

@[simp] lemma zero_locus_univ :
  zero_locus (set.univ : set R) = ∅ :=
zero_locus_empty_of_one_mem _ (set.mem_univ 1)

lemma zero_locus_union (I J : set R) :
  zero_locus I ∪ zero_locus J = zero_locus ((ideal.span I) ⊓ (ideal.span J) : ideal R) :=
begin
  ext x,
  split,
  { rintro (h|h),
    all_goals
    { rw mem_zero_locus at h ⊢,
      have hx : ideal.span _ ≤ x.as_ideal := ideal.span_le.mpr h,
      refine set.subset.trans _ hx,
      intros r hr, cases hr, assumption } },
  { rintro h,
    rw set.mem_union,
    simp only [mem_zero_locus] at h ⊢,
    sorry,
    },
end

instance Zariski_topology : topological_space (prime_spectrum R) :=
topological_space.of_closed {Z | ∃ I, Z = prime_spectrum.zero_locus I}
 _ _ _

end prime_spectrum
