/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Johan Commelin
-/

import topology.opens
import ring_theory.graded_algebra.homogeneous_ideal

/-!
# Projective spectrum of a graded ring

The projective spectrum of a graded commutative ring is the subtype of all homogenous ideals that
are prime and not containing all the irrelevant ideal.
It is naturally endowed with a topology: the Zariski topology.

## Notation
- `R` is a commutative semiring;
- `A` is a commutative ring and an `R`-algebra;
- `𝒜 : ℕ → submodule R A` is the grading of `A`;

## Main definitions

* `projective_spectrum 𝒜`: The projective spectrum of a graded ring `A`, or equivalently, the set of
  all homogeneous ideals of `A` that is both prime and relevant i.e. not containing all irrelevant
  ideal. Henceforth, we call elements of projective spectrum relevant prime homogeneous ideals.
* `zero_locus s`: The zero locus of a subset `s` of `A`
  is the subset of `projective_spectrum 𝒜` consisting of all relevant prime homogeneous ideals
  that contain `s`.
* `vanishing_ideal t`: The vanishing ideal of a subset `t` of `projective_spectrum 𝒜`
  is the intersection of points in `t` (viewed as relevant prime homogeneous ideals).

## Implementation note
The type of `vanishing_ideal` is an `ideal` but instead of `homogeneous_ideal` is to take advantage
of `ideal_gc` so that setting up a galois connection is easier.
-/

noncomputable theory
open_locale direct_sum big_operators pointwise
open direct_sum set_like

variables {R A: Type*}
variables [comm_semiring R] [comm_ring A] [algebra R A]
variables (𝒜 : ℕ → submodule R A) [graded_algebra 𝒜]

/--
The projective spectrum of a graded commutative ring is the subtype of all homogenous ideals that
are prime and not containing all the irrelevant ideal.
-/
@[nolint has_inhabited_instance]
def projective_spectrum :=
{I : homogeneous_ideal 𝒜 // I.1.is_prime ∧ ¬(homogeneous_ideal.irrelevant 𝒜 ≤ I)}

namespace projective_spectrum


variable {𝒜}
/-- A method to view a point in the projective spectrum of a graded ring
as a homogeneous ideal of that ring. -/
abbreviation as_homogeneous_ideal (x : projective_spectrum 𝒜) : homogeneous_ideal 𝒜 := x.val

lemma as_homogeneous_ideal.explicit (x : projective_spectrum 𝒜) :
  x.as_homogeneous_ideal = x.1 := rfl

instance is_prime (x : projective_spectrum 𝒜) :
  x.as_homogeneous_ideal.1.is_prime := x.2.1

@[ext] lemma ext {x y : projective_spectrum 𝒜} :
  x = y ↔ x.as_homogeneous_ideal = y.as_homogeneous_ideal :=
subtype.ext_iff_val

variable (𝒜)
/-- The zero locus of a set `s` of elements of a commutative ring `A`
is the set of all relevant prime homogeneous ideals of the ring that contain the set `s`.

An element `f` of `A` can be thought of as a dependent function on the projective spectrum of `𝒜`.
At a point `x` (a prime homogeneous ideal)
the function (i.e., element) `f` takes values in the quotient ring `A` modulo the prime ideal `x`.
In this manner, `zero_locus s` is exactly the subset of `projective_spectrum 𝒜`
where all "functions" in `s` vanish simultaneously.
-/
def zero_locus (s : set A) : set (projective_spectrum 𝒜) :=
{x | s ⊆ x.as_homogeneous_ideal}

@[simp] lemma mem_zero_locus (x : projective_spectrum 𝒜) (s : set A) :
  x ∈ zero_locus 𝒜 s ↔ s ⊆ x.as_homogeneous_ideal := iff.rfl

@[simp] lemma zero_locus_span (s : set A) :
  zero_locus 𝒜 (ideal.span s) = zero_locus 𝒜 s :=
by { ext x, exact (submodule.gi _ _).gc s x.as_homogeneous_ideal }

/-- The vanishing ideal of a set `t` of points
of the projective spectrum of a commutative ring `R`
is the intersection of all the prime ideals in the set `t`.

An element `f` of `A` can be thought of as a dependent function on the projective spectrum of `𝒜`.
At a point `x` (a prime homogeneous ideal)
the function (i.e., element) `f` takes values in the quotient ring `A` modulo the prime ideal `x`.
In this manner, `vanishing_ideal t` is exactly the ideal of `A`
consisting of all "functions" that vanish on all of `t`.
-/
def vanishing_ideal (t : set (projective_spectrum 𝒜)) : ideal A :=
⨅ (x : projective_spectrum 𝒜) (h : x ∈ t), x.as_homogeneous_ideal.1

lemma vanishing_ideal.is_homogeneous (t : set (projective_spectrum 𝒜)) :
  ideal.is_homogeneous 𝒜 $ vanishing_ideal 𝒜 t :=
ideal.is_homogeneous.Inf $ λ I hI, begin
  obtain ⟨y, rfl⟩ := hI,
  apply ideal.is_homogeneous.Inf (λ I hI, _),
  obtain ⟨_, rfl⟩ := hI,
  exact y.1.2,
end

lemma coe_vanishing_ideal (t : set (projective_spectrum 𝒜)) :
  (vanishing_ideal 𝒜 t : set A) =
  {f | ∀ x : projective_spectrum 𝒜, x ∈ t → f ∈ x.as_homogeneous_ideal} :=
begin
  ext f,
  rw [vanishing_ideal, set_like.mem_coe, submodule.mem_infi],
  apply forall_congr, intro x,
  rw [submodule.mem_infi], refl,
end

lemma mem_vanishing_ideal (t : set (projective_spectrum 𝒜)) (f : A) :
  f ∈ vanishing_ideal 𝒜 t ↔
  ∀ x : projective_spectrum 𝒜, x ∈ t → f ∈ x.as_homogeneous_ideal :=
by rw [← set_like.mem_coe, coe_vanishing_ideal, set.mem_set_of_eq]

@[simp] lemma vanishing_ideal_singleton (x : projective_spectrum 𝒜) :
  vanishing_ideal 𝒜 ({x} : set (projective_spectrum 𝒜)) = x.as_homogeneous_ideal :=
by simp [vanishing_ideal]

lemma subset_zero_locus_iff_le_vanishing_ideal (t : set (projective_spectrum 𝒜))
  (I : ideal A) :
  t ⊆ zero_locus 𝒜 I ↔ I ≤ vanishing_ideal 𝒜 t :=
⟨λ h f k, (mem_vanishing_ideal _ _ _).mpr (λ x j, (mem_zero_locus _ _ _).mpr (h j) k), λ h,
  λ x j, (mem_zero_locus _ _ _).mpr (le_trans h (λ f h, ((mem_vanishing_ideal _ _ _).mp h) x j))⟩

end projective_spectrum
