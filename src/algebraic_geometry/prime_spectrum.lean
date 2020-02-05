/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import topology.opens
import ring_theory.ideal_operations

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

universe variables u v

variables (R : Type u) [comm_ring R]

/-- The prime spectrum of a commutative ring `R`
is the type of all prime ideal of `R`.

It is naturally endowed with a topology (the Zariski topology),
and a sheaf of commutative rings (not yet in mathlib).
It is a fundamental building block in algebraic geometry. -/
def prime_spectrum := {I : ideal R // I.is_prime}

variable {R}

namespace prime_spectrum

/-- A method to view a point in the prime spectrum of a commutative ring
as an ideal of that ring. -/
abbreviation as_ideal (x : prime_spectrum R) : ideal R := x.val

instance as_ideal.is_prime (x : prime_spectrum R) :
  x.as_ideal.is_prime := x.2

@[ext] lemma ext {x y : prime_spectrum R} :
  x = y ↔ x.as_ideal = y.as_ideal :=
subtype.ext

/-- The zero locus of a set `I` of elements of a commutative ring `R`
is the set of all prime ideals of the ring that contain the set `I`.

An element `f` in `I` can be thought of as dependent functions
on the prime spectrum of `R`.
At a point `x` (a prime ideal)
the function (i.e., element) `f` takes values in the quotient ring `R` modulo the prime ideal `x`.
In this manner, `zero_locus I` is exactly the subset or `prime_spectrum R`
where all "functions" in `I` vanish simultaneously.
-/
def zero_locus (I : set R) : set (prime_spectrum R) :=
{x | I ⊆ x.as_ideal}

@[simp] lemma mem_zero_locus (x : prime_spectrum R) (I : set R) :
  x ∈ zero_locus I ↔ I ⊆ x.as_ideal := iff.rfl

lemma zero_locus_empty_of_one_mem (I : set R) (h : (1:R) ∈ I) :
  zero_locus I = ∅ :=
begin
  rw set.eq_empty_iff_forall_not_mem,
  intros x hx,
  rw mem_zero_locus at hx,
  have x_prime : x.as_ideal.is_prime := by apply_instance,
  have eq_top : x.as_ideal = ⊤, { rw ideal.eq_top_iff_one, exact hx h },
  apply x_prime.1 eq_top,
end

@[simp] lemma zero_locus_univ :
  zero_locus (set.univ : set R) = ∅ :=
zero_locus_empty_of_one_mem _ (set.mem_univ 1)

lemma union_zero_locus (I J : set R) :
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
    rw classical.or_iff_not_imp_right,
    intros hI r hr,
    rw set.not_subset at hI,
    rcases hI with ⟨s, hs1, hs2⟩,
    apply (ideal.is_prime.mem_or_mem (by apply_instance) _).resolve_left hs2,
    apply h,
    rw [submodule.mem_coe, submodule.mem_inf],
    split,
    { exact ideal.mul_mem_left _ (ideal.subset_span hr) },
    { exact ideal.mul_mem_right _ (ideal.subset_span hs1) } }
end

lemma zero_locus_Union {ι : Type*} (I : ι → set R) :
  zero_locus (⋃ i, I i) = (⋂ i, zero_locus (I i)) :=
by { ext x, simp only [mem_zero_locus, set.mem_Inter, set.Union_subset_iff] }

lemma Inter_zero_locus {ι : Type*} (I : ι → set R) :
  (⋂ i, zero_locus (I i)) = zero_locus (⋃ i, I i) :=
(zero_locus_Union I).symm

/-- The Zariski topology on the prime spectrum of a commutative ring
is defined via the closed sets of the topology:
they are exactly those sets that are the zero locus of a subset of the ring. -/
instance Zariski_topology : topological_space (prime_spectrum R) :=
topological_space.of_closed {Z | ∃ I, Z = prime_spectrum.zero_locus I}
(⟨set.univ, by simp⟩)
begin
  intros Zs h,
  rw set.sInter_eq_Inter,
  let f : Zs → set R := λ i, classical.some (h i.2),
  have hf : ∀ i : Zs, i.1 = zero_locus (f i) := λ i, classical.some_spec (h i.2),
  simp only [hf],
  exact ⟨_, Inter_zero_locus _⟩
end
(by { rintro _ _ ⟨I, rfl⟩ ⟨J, rfl⟩, exact ⟨_, union_zero_locus I J⟩ })

lemma is_open_iff (U : set (prime_spectrum R)) :
  is_open U ↔ ∃ I, -U = zero_locus I :=
iff.rfl

lemma is_closed_iff_zero_locus (Z : set (prime_spectrum R)) :
  is_closed Z ↔ ∃ I, Z = zero_locus I :=
by rw [is_closed, is_open_iff, set.compl_compl]

lemma zero_locus_is_closed (I : set R) :
  is_closed (zero_locus I) :=
by { rw [is_closed_iff_zero_locus], exact ⟨I, rfl⟩ }

section comap
variables {S : Type v} [comm_ring S] {S' : Type*} [comm_ring S']

/-- The function between prime spectra of commutative rings induced by a ring homomorphism.
This function is continuous. -/
def comap (f : R →+* S) : prime_spectrum S → prime_spectrum R :=
λ y, ⟨ideal.comap f y.as_ideal, by { refine ideal.is_prime.comap _, apply_instance }⟩

variables (f : R →+* S)

@[simp] lemma comap_as_ideal (y : prime_spectrum S) :
  (comap f y).as_ideal = ideal.comap f y.as_ideal :=
rfl

@[simp] lemma comap_id : comap (ring_hom.id R) = id :=
funext $ λ x, ext.mpr $ by { rw [comap_as_ideal], apply ideal.ext, intros r, simp }

@[simp] lemma comap_comp (f : R →+* S) (g : S →+* S') :
  comap (g.comp f) = comap f ∘ comap g :=
funext $ λ x, ext.mpr $ by { simp, refl }

@[simp] lemma preimage_comap_zero_locus (I : set R) :
  (comap f) ⁻¹' (zero_locus I) = zero_locus (f '' I) :=
begin
  ext x,
  simp only [mem_zero_locus, set.mem_preimage, comap_as_ideal, set.image_subset_iff],
  refl
end

lemma comap_continuous (f : R →+* S) : continuous (comap f) :=
begin
  rw continuous_iff_is_closed,
  simp only [is_closed_iff_zero_locus],
  rintro _ ⟨I, rfl⟩,
  exact ⟨_, preimage_comap_zero_locus f I⟩
end

end comap

end prime_spectrum
