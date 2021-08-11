/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Heather Macbeth
-/
import topology.algebra.weak_dual_topology
import analysis.normed_space.dual
import analysis.normed_space.operator_norm

/-!
# Weak dual of normed space

This file proves properties of the weak-* topology on the dual of a normed space.

It is shown that the canconical mapping `dual 𝕜 E → weak_dual 𝕜 E` is continuous, and as a
consequence the weak-* topology is coarser than the topology induced by the dual norm (operator
norm).

## Main definitions

The main definitions concern the canconical mapping `dual 𝕜 E → weak_dual 𝕜 E`.

* `normed_space.dual.to_weak_dual` is a linear equivalence from `dual 𝕜 E`to `weak_dual 𝕜 E`.
* `normed_space.dual.continuous_linear_map_to_weak_dual` is a continuous linear mapping from
  `dual 𝕜 E` to `weak_dual 𝕜 E`.

## Main results

The main results concern the comparison of the operator norm topology on `dual 𝕜 E` and the weak-*
topology on (it type synonym) `weak_dual 𝕜 E`.

* `dual_norm_topology_le_weak_dual_topology` is the statement that the weak-* topology on the dual
  of a normed space is coarser (not necessarily strictly) than the operator norm topology.

## Notations

No new notation is introduced.

## Implementation notes

Weak-* topology is defined generally in the file <topology.algebra.weak_dual_topology>.

When `E` is a normed space, the duals `dual 𝕜 E` and `weak_dual 𝕜 E` are type synonyms with
different topology instances.

## References

* https://en.wikipedia.org/wiki/Weak_topology#Weak-*_topology

## Tags

weak-star, weak dual

-/

noncomputable theory
open filter
open_locale topological_space

section weak_star_topology_for_duals_of_normed_spaces
/-!
### Weak star topology on duals of normed spaces
In this section, we prove properties about the weak-* topology on duals of normed spaces.
We prove in particular that the canonical mapping `dual 𝕜 E → weak_dual 𝕜 E` is continuous,
i.e., that the weak-* topology is coarser (not necessarily strictly) than the topology given
by the dual-norm (i.e. the operator-norm).
-/

open normed_space

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]

/-- For normed spaces `E`, there is a canonical map `dual 𝕜 E → weak_dual 𝕜 E` (the "identity"
    mapping). It is a linear equivalence. -/
def normed_space.dual.to_weak_dual : dual 𝕜 E ≃ₗ[𝕜] weak_dual 𝕜 E :=
linear_equiv.refl 𝕜 (E →L[𝕜] 𝕜)

/-- For normed spaces `E`, there is a canonical map `weak_dual 𝕜 E → dual 𝕜 E` (the "identity"
    mapping). It is a linear equivalence. Here it is implemented as the inverse of the linear
    equivalence `normed_space.dual.to_weak_dual` in the other direction. -/
def weak_dual.to_original_dual : weak_dual 𝕜 E ≃ₗ[𝕜] dual 𝕜 E :=
normed_space.dual.to_weak_dual.symm

@[simp] lemma weak_dual.coe_to_fun_eq_original_coe_to_fun (x' : dual 𝕜 E) :
  (x'.to_weak_dual : E → 𝕜) = x' := rfl

@[simp] lemma to_weak_dual_inj_iff (x' y' : dual 𝕜 E) :
  x'.to_weak_dual = y'.to_weak_dual ↔ x' = y' := iff.rfl

@[simp] lemma to_original_dual_inj_iff (x' y' : weak_dual 𝕜 E) :
  x'.to_original_dual = y'.to_original_dual ↔ x' = y' := iff.rfl

theorem to_weak_dual_continuous :
  continuous (λ (x' : dual 𝕜 E), x'.to_weak_dual) :=
begin
  apply weak_dual.continuous_of_continuous_eval,
  intros z,
  exact (inclusion_in_double_dual 𝕜 E z).continuous,
end

/-- For a normed space `E`, according to `to_weak_dual_continuous` the "identity mapping"
`dual 𝕜 E → weak_dual 𝕜 E` is continuous. The following definition implements it as a continuous
linear map. -/
def normed_space.dual.continuous_linear_map_to_weak_dual : dual 𝕜 E →L[𝕜] weak_dual 𝕜 E :=
{ cont := to_weak_dual_continuous,
  .. normed_space.dual.to_weak_dual, }

/-- The weak-star topology is coarser than the dual-norm topology: all weak-star open sets are open
in the operator norm topology. -/
lemma open_set_of_weak_dual_open_set (s : set (dual 𝕜 E))
  (s_weak_dual_open : is_open (normed_space.dual.to_weak_dual '' s)) : is_open s :=
begin
  have eq : (normed_space.dual.to_weak_dual)⁻¹' (normed_space.dual.to_weak_dual '' s) = s,
  { ext x',
    simp only [set.mem_preimage, set.mem_image, to_weak_dual_inj_iff, exists_eq_right], },
  rw ←eq,
  apply continuous_def.mp to_weak_dual_continuous _ s_weak_dual_open,
end

-- TODO: The proof below may be abusing definitional equality... And it looks like it needs golf.
private lemma to_weak_dual_image (s : set (dual 𝕜 E)) :
  (normed_space.dual.to_weak_dual '' s) = s :=
begin
  ext x',
  split,
  { intros hx',
    rcases hx' with ⟨y', hy', h_eq⟩,
    rwa ←h_eq, },
  { intros hx',
    use x',
    exact ⟨ hx', by refl ⟩, },
end

-- TODO: The proof and even the statement below may be abusing definitional equality...
-- But I don't think this can be stated using `≤` on topologies without such abuse.
/-- The weak-star topology is coarser than the dual-norm topology. -/
theorem dual_norm_topology_le_weak_dual_topology :
  (by apply_instance : topological_space (dual 𝕜 E)) ≤ weak_dual.weak_dual_topology 𝕜 E :=
begin
  intros U hU,
  apply open_set_of_weak_dual_open_set U,
  rwa to_weak_dual_image,
end

end weak_star_topology_for_duals_of_normed_spaces
