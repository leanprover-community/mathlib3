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

noncomputable theory
open_locale classical

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

/-- The zero locus of a set `s` of elements of a commutative ring `R`
is the set of all prime ideals of the ring that contain the set `s`.

An element `f` of `R` can be thought of as a dependent function
on the prime spectrum of `R`.
At a point `x` (a prime ideal)
the function (i.e., element) `f` takes values in the quotient ring `R` modulo the prime ideal `x`.
In this manner, `zero_locus s` is exactly the subset of `prime_spectrum R`
where all "functions" in `s` vanish simultaneously.
-/
def zero_locus (s : set R) : set (prime_spectrum R) :=
{x | s ⊆ x.as_ideal}

@[simp] lemma mem_zero_locus (x : prime_spectrum R) (s : set R) :
  x ∈ zero_locus s ↔ s ⊆ x.as_ideal := iff.rfl

/-- The vanishing ideal of a set `s` of points
of the prime spectrum of a commutative ring `R`
is the largest ideal of the ring that is contained in all the prime ideals in the set `s`.

An element `f` of `R` can be thought of as a dependent function
on the prime spectrum of `R`.
At a point `x` (a prime ideal)
the function (i.e., element) `f` takes values in the quotient ring `R` modulo the prime ideal `x`.
In this manner, `vanishing_ideal s` is exactly the ideal of `R`
consisting of all "functions" that vanish on all of `s`.
-/
def vanishing_ideal (s : set (prime_spectrum R)) : ideal R :=
⨅ (x : prime_spectrum R) (h : x ∈ s), x.as_ideal

lemma coe_vanishing_ideal (s : set (prime_spectrum R)) :
  (vanishing_ideal s : set R) = {f : R | ∀ x : prime_spectrum R, x ∈ s → f ∈ x.as_ideal} :=
begin
  ext f,
  rw [vanishing_ideal, submodule.mem_coe, submodule.mem_infi],
  apply forall_congr, intro x,
  rw [submodule.mem_infi],
end

lemma mem_vanishing_ideal (s : set (prime_spectrum R)) (f : R) :
  f ∈ vanishing_ideal s ↔ ∀ x : prime_spectrum R, x ∈ s → f ∈ x.as_ideal :=
by rw [← submodule.mem_coe, coe_vanishing_ideal, set.mem_set_of_eq]

def gc : galois_connection vanishing_ideal (λ I, zero_locus (I : set R))

lemma zero_locus_empty_of_one_mem {s : set R} (h : (1:R) ∈ s) :
  zero_locus s = ∅ :=
begin
  rw set.eq_empty_iff_forall_not_mem,
  intros x hx,
  rw mem_zero_locus at hx,
  have x_prime : x.as_ideal.is_prime := by apply_instance,
  have eq_top : x.as_ideal = ⊤, { rw ideal.eq_top_iff_one, exact hx h },
  apply x_prime.1 eq_top,
end

lemma zero_locus_empty_iff_eq_top {I : ideal R} :
  zero_locus (I : set R) = ∅ ↔ I = ⊤ :=
begin
  split,
  { contrapose!,
    intro h,
    apply set.ne_empty_iff_nonempty.mpr,
    rcases ideal.exists_le_maximal I h with ⟨M, hM, hIM⟩,
    exact ⟨⟨M, hM.is_prime⟩, hIM⟩ },
  { rintro rfl, apply zero_locus_empty_of_one_mem, trivial }
end

@[simp] lemma zero_locus_univ :
  zero_locus (set.univ : set R) = ∅ :=
zero_locus_empty_of_one_mem (set.mem_univ 1)

@[simp] lemma zero_locus_span (s : set R) :
  zero_locus (ideal.span s : set R) = zero_locus s :=
begin
  ext x,
  simp only [mem_zero_locus],
  split,
  { exact set.subset.trans ideal.subset_span },
  { intro h, rwa ← ideal.span_le at h }
end

lemma union_zero_locus_ideal (I J : ideal R) :
  zero_locus (I : set R) ∪ zero_locus J = zero_locus (I ⊓ J : ideal R) :=
begin
  ext x,
  split,
  { rintro (h|h),
    all_goals
    { rw mem_zero_locus at h ⊢,
      refine set.subset.trans _ h,
      intros r hr, cases hr, assumption } },
  { rintro h,
    rw set.mem_union,
    simp only [mem_zero_locus] at h ⊢,
    -- TODO: The rest of this proof should be factored out.
    rw classical.or_iff_not_imp_right,
    intros hs r hr,
    rw set.not_subset at hs,
    rcases hs with ⟨s, hs1, hs2⟩,
    apply (ideal.is_prime.mem_or_mem (by apply_instance) _).resolve_left hs2,
    apply h,
    rw [submodule.mem_coe, submodule.mem_inf],
    split,
    { exact ideal.mul_mem_left _ hr },
    { exact ideal.mul_mem_right _ hs1 } }
end

lemma union_zero_locus (s t : set R) :
  zero_locus s ∪ zero_locus t = zero_locus ((ideal.span s) ⊓ (ideal.span t) : ideal R) :=
by { rw ← union_zero_locus_ideal, simp }

lemma zero_locus_Union {ι : Type*} (s : ι → set R) :
  zero_locus (⋃ i, s i) = (⋂ i, zero_locus (s i)) :=
by { ext x, simp only [mem_zero_locus, set.mem_Inter, set.Union_subset_iff] }

lemma Inter_zero_locus {ι : Type*} (s : ι → set R) :
  (⋂ i, zero_locus (s i)) = zero_locus (⋃ i, s i) :=
(zero_locus_Union s).symm

lemma zero_locus_union (s t : set R) :
  zero_locus (s ∪ t) = zero_locus s ∩ zero_locus t :=
begin
  ext x,
  simp only [set.union_subset_iff, set.mem_inter_eq, iff_self, prime_spectrum.mem_zero_locus]
end

-- TODO: we actually get the radical ideal,
-- but I think that isn't in mathlib yet.
lemma subset_vanishing_ideal_zero_locus (s : set R) :
  s ⊆ vanishing_ideal (zero_locus s) :=
begin
  intros f hf,
  rw coe_vanishing_ideal,
  intro x,
  rw mem_zero_locus,
  intro hsx,
  exact hsx hf
end

lemma le_vanishing_ideal_zero_locus (I : ideal R) :
  I ≤ vanishing_ideal (zero_locus I) :=
subset_vanishing_ideal_zero_locus I

lemma vanishing_ideal_union (s t : set (prime_spectrum R)) :
  vanishing_ideal (s ∪ t) = vanishing_ideal s ⊓ vanishing_ideal t :=
begin
  ext f,
  simp only [mem_vanishing_ideal, or_imp_distrib, forall_and_distrib,
    submodule.mem_inf, iff_self, set.mem_union_eq]
end

lemma vanishing_ideal_Union {ι : Type*} (s : ι → set (prime_spectrum R)) :
  vanishing_ideal (⋃ i, s i) = (⨅ i, vanishing_ideal (s i)) :=
begin
  ext f,
  simp only [mem_vanishing_ideal, set.mem_Union, exists_imp_distrib, submodule.mem_infi],
  rw forall_swap
end

/-- The Zariski topology on the prime spectrum of a commutative ring
is defined via the closed sets of the topology:
they are exactly those sets that are the zero locus of a subset of the ring. -/
instance zariski_topology : topological_space (prime_spectrum R) :=
topological_space.of_closed (set.range prime_spectrum.zero_locus)
  (⟨set.univ, by simp⟩)
  begin
    intros Zs h,
    rw set.sInter_eq_Inter,
    let f : Zs → set R := λ i, classical.some (h i.2),
    have hf : ∀ i : Zs, i.1 = zero_locus (f i) := λ i, (classical.some_spec (h i.2)).symm,
    simp only [hf],
    exact ⟨_, (Inter_zero_locus _).symm⟩
  end
  (by { rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩, exact ⟨_, (union_zero_locus s t).symm⟩ })

lemma is_open_iff (U : set (prime_spectrum R)) :
  is_open U ↔ ∃ s, -U = zero_locus s :=
by simp only [@eq_comm _ (-U)]; refl

lemma is_closed_iff_zero_locus (Z : set (prime_spectrum R)) :
  is_closed Z ↔ ∃ s, Z = zero_locus s :=
by rw [is_closed, is_open_iff, set.compl_compl]

lemma zero_locus_is_closed (s : set R) :
  is_closed (zero_locus s) :=
by { rw [is_closed_iff_zero_locus], exact ⟨s, rfl⟩ }

section comap
variables {S : Type v} [comm_ring S] {S' : Type*} [comm_ring S']

/-- The function between prime spectra of commutative rings induced by a ring homomorphism.
This function is continuous. -/
def comap (f : R →+* S) : prime_spectrum S → prime_spectrum R :=
λ y, ⟨ideal.comap f y.as_ideal, by exact ideal.is_prime.comap _⟩

variables (f : R →+* S)

@[simp] lemma comap_as_ideal (y : prime_spectrum S) :
  (comap f y).as_ideal = ideal.comap f y.as_ideal :=
rfl

@[simp] lemma comap_id : comap (ring_hom.id R) = id :=
funext $ λ x, ext.mpr $ by { rw [comap_as_ideal], apply ideal.ext, intros r, simp }

@[simp] lemma comap_comp (f : R →+* S) (g : S →+* S') :
  comap (g.comp f) = comap f ∘ comap g :=
funext $ λ x, ext.mpr $ by { simp, refl }

@[simp] lemma preimage_comap_zero_locus (s : set R) :
  (comap f) ⁻¹' (zero_locus s) = zero_locus (f '' s) :=
begin
  ext x,
  simp only [mem_zero_locus, set.mem_preimage, comap_as_ideal, set.image_subset_iff],
  refl
end

lemma comap_continuous (f : R →+* S) : continuous (comap f) :=
begin
  rw continuous_iff_is_closed,
  simp only [is_closed_iff_zero_locus],
  rintro _ ⟨s, rfl⟩,
  exact ⟨_, preimage_comap_zero_locus f s⟩
end

end comap

lemma zero_locus_vanishing_ideal_eq_closure (s : set (prime_spectrum R)) :
  zero_locus (vanishing_ideal s : set R) = closure s :=
begin
  apply set.subset.antisymm,
  { intros x hx,
    rw mem_zero_locus at hx,
    sorry },
end

lemma submodule.exists_finset_of_mem_supr {R : Type u} {M : Type v}
  [ring R] [add_comm_group M] [module R M] {ι : Sort*}
  (p : ι → submodule R M) {m : M} (hm : m ∈ ⨆ (i : ι), p i) :
  ∃ s : finset ι, m ∈ ⨆ i ∈ s, p i :=
begin
  sorry,
end

instance : compact_space (prime_spectrum R) :=
{ compact_univ :=
  begin
    apply compact_of_finite_subcover,
    intros U h_open h_cover,
    rw set.univ_subset_iff at h_cover,
    have H : -⋃₀ U = ∅, { simp [h_cover] },
    rw [set.compl_sUnion, set.sInter_image, set.bInter_eq_Inter] at H,
    change (⋂ (x : U), - x.val) = ∅ at H,
    -- TODO: define vanishing_ideal and get rid of choice
    let f : U → set R := λ i, classical.some (h_open _ i.2),
    have hf : ∀ i : U, -i.1 = zero_locus (f i) := λ i, (classical.some_spec (h_open _ i.2)).symm,
    simp only [hf] at H,
    rw [Inter_zero_locus, ← zero_locus_span,
        zero_locus_empty_iff_eq_top, ideal.eq_top_iff_one] at H,
    have aux : ideal.span (⋃ i : U, f i) = ⨆ i : U, ideal.span (f i),
    { exact submodule.span_Union _, },
    rw aux at H, clear aux,
    rcases submodule.exists_finset_of_mem_supr _ H with ⟨s, hs⟩,
    have aux : ideal.span (⋃ (i : U) (H : i ∈ s), f i) = ⨆ (i : U) (H : i ∈ s), ideal.span (f i),
    { sorry },
    rw ← aux at hs, clear aux,
    rw [←ideal.eq_top_iff_one, ←zero_locus_empty_iff_eq_top,
        zero_locus_span, ←Inter_zero_locus] at hs,
    refine ⟨subtype.val '' (↑s : set U), _, _, _⟩,
    { rw set.image_subset_iff, intros u hu, exact u.2 },
    { apply set.finite_image, exact finset.finite_to_set s },
    rw set.univ_subset_iff,
    rw [set.sUnion_image, set.bUnion_eq_Union],
  end }

end prime_spectrum
