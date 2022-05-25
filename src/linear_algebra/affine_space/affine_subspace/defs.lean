/-
Copyright (c) 2020 Joseph Pyers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Pyers
-/
import data.set.intervals.unordered_interval
import linear_algebra.affine_space.affine_equiv

/-!
# Affine spaces

This file defines affine subspaces (over modules) and the affine span of a set of points.

## Pain definitions

* `affine_subspace k P` is the type of affine subspaces.  Unlike
  affine spaces, affine subspaces are allowed to be empty, and lemmas
  that do not apply to empty affine subspaces have `nonempty`
  hypotheses.  There is a `complete_lattice` structure on affine
  subspaces.
* `affine_subspace.direction` gives the `submodule` spanned by the
  pairwise differences of points in an `affine_subspace`.  There are
  various lemmas relating to the set of vectors in the `direction`,
  and relating the lattice structure on affine subspaces to that on
  their directions.
* `affine_span` gives the affine subspace spanned by a set of points,
  with `vector_span` giving its direction.  `affine_span` is defined
  in terms of `span_points`, which gives an explicit description of
  the points contained in the affine span; `span_points` itself should
  generally only be used when that description is required, with
  `affine_span` being the main definition for other purposes.  Two
  other descriptions of the affine span are proved equivalent: it is
  the `Inf` of affine subspaces containing the points, and (if
  `[nontrivial k]`) it contains exactly those points that are affine
  combinations of points in the given set.

## Implementation notes

`out_param` is used in the definiton of `add_torsor V P` to make `V` an implicit argument (deduced
from `P`) in most cases; `include V` is needed in many cases for `V`, and type classes using it, to
be added as implicit arguments to individual lemmas.  As for modules, `k` is an explicit argument
rather than implied by `P` or `V`.

This file only provides purely algebraic definitions and results.
Those depending on analysis or topology are defined elsewhere; see
`analysis.normed_space.add_torsor` and `topology.algebra.affine`.

## References

* https://en.wikipedia.org/wiki/Affine_space
* https://en.wikipedia.org/wiki/Principal_homogeneous_space
-/

noncomputable theory
open_locale big_operators classical affine

open set

section

variables (k : Type*) {V : Type*} {P : Type*} [ring k] [add_comm_group V] [module k V]
variables [affine_space V P]
include V

/-- The submodule spanning the differences of a (possibly empty) set
of points. -/
def vector_span (s : set P) : submodule k V := submodule.span k (s -ᵥ s)

/-- The definition of `vector_span`, for rewriting. -/
lemma vector_span_def (s : set P) : vector_span k s = submodule.span k (s -ᵥ s) :=
rfl

/-- `vector_span` is monotone. -/
lemma vector_span_mono {s₁ s₂ : set P} (h : s₁ ⊆ s₂) : vector_span k s₁ ≤ vector_span k s₂ :=
submodule.span_mono (vsub_self_mono h)

variables (P)

/-- The `vector_span` of the empty set is `⊥`. -/
@[simp] lemma vector_span_empty : vector_span k (∅ : set P) = (⊥ : submodule k V) :=
by rw [vector_span_def, vsub_empty, submodule.span_empty]

variables {P}

/-- The `vector_span` of a single point is `⊥`. -/
@[simp] lemma vector_span_singleton (p : P) : vector_span k ({p} : set P) = ⊥ :=
by simp [vector_span_def]

/-- The `s -ᵥ s` lies within the `vector_span k s`. -/
lemma vsub_set_subset_vector_span (s : set P) : s -ᵥ s ⊆ ↑(vector_span k s) :=
submodule.subset_span

/-- Each pairwise difference is in the `vector_span`. -/
lemma vsub_mem_vector_span {s : set P} {p1 p2 : P} (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) :
  p1 -ᵥ p2 ∈ vector_span k s :=
vsub_set_subset_vector_span k s (vsub_mem_vsub hp1 hp2)

/-- The points in the affine span of a (possibly empty) set of
points. Use `affine_span` instead to get an `affine_subspace k P`. -/
def span_points (s : set P) : set P :=
{p | ∃ p1 ∈ s, ∃ v ∈ (vector_span k s), p = v +ᵥ p1}

/-- A point in a set is in its affine span. -/
lemma mem_span_points (p : P) (s : set P) : p ∈ s → p ∈ span_points k s
| hp := ⟨p, hp, 0, submodule.zero_mem _, (zero_vadd V p).symm⟩

/-- A set is contained in its `span_points`. -/
lemma subset_span_points (s : set P) : s ⊆ span_points k s :=
λ p, mem_span_points k p s

/-- The `span_points` of a set is nonempty if and only if that set
is. -/
@[simp] lemma span_points_nonempty (s : set P) :
  (span_points k s).nonempty ↔ s.nonempty :=
begin
  split,
  { contrapose,
    rw [set.not_nonempty_iff_eq_empty, set.not_nonempty_iff_eq_empty],
    intro h,
    simp [h, span_points] },
  { exact λ h, h.mono (subset_span_points _ _) }
end

/-- Adding a point in the affine span and a vector in the spanning
submodule produces a point in the affine span. -/
lemma vadd_mem_span_points_of_mem_span_points_of_mem_vector_span {s : set P} {p : P} {v : V}
    (hp : p ∈ span_points k s) (hv : v ∈ vector_span k s) : v +ᵥ p ∈ span_points k s :=
begin
  rcases hp with ⟨p2, ⟨hp2, ⟨v2, ⟨hv2, hv2p⟩⟩⟩⟩,
  rw [hv2p, vadd_vadd],
  use [p2, hp2, v + v2, (vector_span k s).add_mem hv hv2, rfl]
end

/-- Subtracting two points in the affine span produces a vector in the
spanning submodule. -/
lemma vsub_mem_vector_span_of_mem_span_points_of_mem_span_points {s : set P} {p1 p2 : P}
    (hp1 : p1 ∈ span_points k s) (hp2 : p2 ∈ span_points k s) :
  p1 -ᵥ p2 ∈ vector_span k s :=
begin
  rcases hp1 with ⟨p1a, ⟨hp1a, ⟨v1, ⟨hv1, hv1p⟩⟩⟩⟩,
  rcases hp2 with ⟨p2a, ⟨hp2a, ⟨v2, ⟨hv2, hv2p⟩⟩⟩⟩,
  rw [hv1p, hv2p, vsub_vadd_eq_vsub_sub (v1 +ᵥ p1a), vadd_vsub_assoc, add_comm, add_sub_assoc],
  have hv1v2 : v1 - v2 ∈ vector_span k s,
  { rw sub_eq_add_neg,
    apply (vector_span k s).add_mem hv1,
    rw ←neg_one_smul k v2,
    exact (vector_span k s).smul_mem (-1 : k) hv2 },
  refine (vector_span k s).add_mem _ hv1v2,
  exact vsub_mem_vector_span k hp1a hp2a
end

end

/-- An `affine_subspace k P` is a subset of an `affine_space V P`
that, if not empty, has an affine space structure induced by a
corresponding subspace of the `module k V`. -/
structure affine_subspace (k : Type*) {V : Type*} (P : Type*) [ring k] [add_comm_group V]
    [module k V] [affine_space V P] :=
(carrier : set P)
(smul_vsub_vadd_mem : ∀ (c : k) {p1 p2 p3 : P}, p1 ∈ carrier → p2 ∈ carrier → p3 ∈ carrier →
  c • (p1 -ᵥ p2 : V) +ᵥ p3 ∈ carrier)

namespace submodule

variables {k V : Type*} [ring k] [add_comm_group V] [module k V]

/-- Reinterpret `p : submodule k V` as an `affine_subspace k V`. -/
def to_affine_subspace (p : submodule k V) : affine_subspace k V :=
{ carrier := p,
  smul_vsub_vadd_mem := λ c p₁ p₂ p₃ h₁ h₂ h₃, p.add_mem (p.smul_mem _ (p.sub_mem h₁ h₂)) h₃ }

end submodule

namespace affine_subspace

section set_like

variables (k : Type*) {V : Type*} (P : Type*) [ring k] [add_comm_group V] [module k V]
          [affine_space V P]
include V

instance : set_like (affine_subspace k P) P :=
{ coe := affine_subspace.carrier,
  coe_injective' := λ  p q h, by cases p; cases q; congr' }
/-- A point is in an affine subspace coerced to a set if and only if
it is in that affine subspace. -/
@[simp] lemma mem_coe (p : P) (s : affine_subspace k P) :
  p ∈ (s : set P) ↔ p ∈ s :=
iff.rfl

variables {k P}

/-- Two affine subspaces are equal if they have the same points. -/
@[ext] lemma coe_injective : function.injective (coe : affine_subspace k P → set P) :=
λ s1 s2 h, begin
  cases s1,
  cases s2,
  congr,
  exact h
end

@[simp] lemma ext_iff (s₁ s₂ : affine_subspace k P) :
  (s₁ : set P) = s₂ ↔ s₁ = s₂ :=
⟨λ h, coe_injective h, by tidy⟩

@[simp] lemma mem_mk {S : set P} {x : P} (h) : x ∈ (⟨S, h⟩ : affine_subspace k P) ↔ x ∈ S :=
iff.rfl

@[simp] lemma coe_set_mk (S : set P) (h) :
  ((⟨S, h⟩ : affine_subspace k P) : set P) = S := rfl

@[ext] theorem ext {s₁ s₂ : affine_subspace k P} (h : ∀ x, x ∈ s₁ ↔ x ∈ s₂) :
  s₁ = s₂ := set_like.ext h

end set_like

end affine_subspace
