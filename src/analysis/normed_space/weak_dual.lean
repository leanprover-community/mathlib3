/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import topology.algebra.weak_dual_topology
import analysis.normed_space.dual
import analysis.normed_space.operator_norm

/-!
# Weak dual of normed space

Let `E` be a normed space over a field `𝕜`. This file is concerned with properties of the weak-*
topology on the dual of `E`. By the dual, we mean either of the type synonyms
`normed_space.dual 𝕜 E` or `weak_dual 𝕜 E`, depending on whether it is viewed as equipped with its
usual operator norm topology or the weak-* topology.

It is shown that the canonical mapping `normed_space.dual 𝕜 E → weak_dual 𝕜 E` is continuous, and
as a consequence the weak-* topology is coarser than the topology obtained from the operator norm
(dual norm).

In this file, we also establish the Banach-Alaoglu theorem about the compactness of closed balls
in the dual of `E` (as well as sets of somewhat more general form) with respect to the weak-*
topology.

## Main definitions

The main definitions concern the canonical mapping `dual 𝕜 E → weak_dual 𝕜 E`.

* `normed_space.dual.to_weak_dual` and `weak_dual.to_normed_dual`: Linear equivalences from
  `dual 𝕜 E` to `weak_dual 𝕜 E` and in the converse direction.
* `normed_space.dual.continuous_linear_map_to_weak_dual`: A continuous linear mapping from
  `dual 𝕜 E` to `weak_dual 𝕜 E` (same as `normed_space.dual.to_weak_dual` but different bundled
  data).

## Main results

The first main result concerns the comparison of the operator norm topology on `dual 𝕜 E` and the
weak-* topology on (its type synonym) `weak_dual 𝕜 E`:
* `dual_norm_topology_le_weak_dual_topology`: The weak-* topology on the dual of a normed space is
  coarser (not necessarily strictly) than the operator norm topology.
* `weak_dual.is_compact_polar` (a version of the Banach-Alaoglu theorem): The polar set of a
  neighborhood of the origin in a normed space `E` over `𝕜` is compact in `weak_dual _ E`, if the
  nondiscrete normed field `𝕜` is proper as a topological space.
* `weak_dual.is_compact_closed_ball` (the most common special case of the Banach-Alaoglu theorem):
  Closed balls in the dual of a normed space `E` over `ℝ` or `ℂ` are compact in the weak-star
  topology.

TODOs:
* Add that in finite dimensions, the weak-* topology and the dual norm topology coincide.
* Add that in infinite dimensions, the weak-* topology is strictly coarser than the dual norm
  topology.
* Add metrizability of the dual unit ball (more generally weak-star compact subsets) of
  `weak_dual 𝕜 E` under the assumption of separability of `E`.
* Add the sequential Banach-Alaoglu theorem: the dual unit ball of a separable normed space `E`
  is sequentially compact in the weak-star topology. (Would follow from the metrizability above.)

## Notations

No new notation is introduced.

## Implementation notes

Weak-* topology is defined generally in the file `topology.algebra.weak_dual_topology`.

When `E` is a normed space, the duals `dual 𝕜 E` and `weak_dual 𝕜 E` are type synonyms with
different topology instances.

For the proof of Banach-Alaoglu theorem, the weak dual of `E` is embedded in the space of
functions `E → 𝕜` with the topology of pointwise convergence. The fact that this is an embedding
is `weak_dual.to_Pi_embedding`.

The polar set `polar 𝕜 s` of a subset `s` of `E` is originally defined as a subset of the dual
`dual 𝕜 E`. We care about properties of these w.r.t. weak-* topology, and for this purpose give
the definition `weak_dual.polar 𝕜 s` for the "same" subset viewed as a subset of `weak_dual 𝕜 E`
(a type synonym of the dual but with a different topology instance).

## References

* https://en.wikipedia.org/wiki/Weak_topology#Weak-*_topology
* https://en.wikipedia.org/wiki/Banach%E2%80%93Alaoglu_theorem

## Tags

weak-star, weak dual

-/

noncomputable theory
open filter
open_locale topological_space filter

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
def weak_dual.to_normed_dual : weak_dual 𝕜 E ≃ₗ[𝕜] dual 𝕜 E :=
normed_space.dual.to_weak_dual.symm

@[simp] lemma weak_dual.coe_to_fun_eq_normed_coe_to_fun (x' : dual 𝕜 E) :
  (x'.to_weak_dual : E → 𝕜) = x' := rfl

namespace normed_space.dual

@[simp] lemma to_weak_dual_eq_iff (x' y' : dual 𝕜 E) :
  x'.to_weak_dual = y'.to_weak_dual ↔ x' = y' :=
to_weak_dual.injective.eq_iff

@[simp] lemma _root_.weak_dual.to_normed_dual_eq_iff (x' y' : weak_dual 𝕜 E) :
  x'.to_normed_dual = y'.to_normed_dual ↔ x' = y' :=
weak_dual.to_normed_dual.injective.eq_iff

theorem to_weak_dual_continuous :
  continuous (λ (x' : dual 𝕜 E), x'.to_weak_dual) :=
begin
  apply weak_dual.continuous_of_continuous_eval,
  intros z,
  exact (inclusion_in_double_dual 𝕜 E z).continuous,
end

/-- For a normed space `E`, according to `to_weak_dual_continuous` the "identity mapping"
`dual 𝕜 E → weak_dual 𝕜 E` is continuous. This definition implements it as a continuous linear
map. -/
def continuous_linear_map_to_weak_dual : dual 𝕜 E →L[𝕜] weak_dual 𝕜 E :=
{ cont := to_weak_dual_continuous, .. to_weak_dual, }

/-- The weak-star topology is coarser than the dual-norm topology. -/
theorem dual_norm_topology_le_weak_dual_topology :
  (by apply_instance : topological_space (dual 𝕜 E)) ≤
    (by apply_instance : topological_space (weak_dual 𝕜 E)) :=
begin
  refine continuous.le_induced _,
  apply continuous_pi_iff.mpr,
  intros z,
  exact (inclusion_in_double_dual 𝕜 E z).continuous,
end

end normed_space.dual

namespace weak_dual

variables (𝕜)

/-- The polar set `polar 𝕜 s` of `s : set E` seen as a subset of the dual of `E` with the
weak-star topology is `weak_dual.polar 𝕜 s`. -/
def polar (s : set E) : set (weak_dual 𝕜 E) := to_normed_dual ⁻¹' (polar 𝕜 s)

lemma polar_def (s : set E) : polar 𝕜 s = {f : weak_dual 𝕜 E | ∀ x ∈ s, ∥f x∥ ≤ 1} := rfl

lemma polar_eq_preimage (s : set E) :
  polar 𝕜 s = (λ (f : weak_dual 𝕜 E) (x : E), f x) ⁻¹' {f : E → 𝕜 | ∀ x ∈ s, ∥f x∥ ≤ 1} := rfl

end weak_dual

end weak_star_topology_for_duals_of_normed_spaces

section polar_sets_in_weak_dual

open metric set normed_space

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]

lemma pi.is_closed_polar {α : Type*} (s : set α) :
  is_closed {f : α → E | ∀ x ∈ s, ∥f x∥ ≤ 1} :=
begin
  simp only [set_of_forall],
  exact is_closed_bInter (λ x hx, is_closed_Iic.preimage (@continuous_apply α (λ _, E) _ x).norm)
end

/-- The polar `polar 𝕜 s` of a set `s : E` is a closed subset when the weak star topology
is used, i.e., when `polar 𝕜 s` is interpreted as a subset of `weak_dual 𝕜 E`. -/
lemma weak_dual.is_closed_polar (s : set E) : is_closed (weak_dual.polar 𝕜 s) :=
(pi.is_closed_polar s).preimage (weak_dual.coe_fn_continuous 𝕜 E)

end polar_sets_in_weak_dual

section embedding_to_Pi

variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]

open metric set normed_space

namespace weak_dual

/-- The image under `weak_dual.to_Pi : weak_dual 𝕜 E → (E → 𝕜)` of a polar `polar 𝕜 s` of a
neighborhood `s` of the origin is a closed set. -/
lemma is_closed_image_polar {s : set E} (s_nhd : s ∈ 𝓝 (0 : E)) :
  is_closed ((λ (f : weak_dual 𝕜 E) (x : E), f x) '' (weak_dual.polar 𝕜 s)) :=
begin
  set t : set (E → 𝕜) := {f | ∀ x ∈ s, ∥f x∥ ≤ 1},
  have htc : is_closed t, from pi.is_closed_polar s,
  change weak_dual.polar 𝕜 s with (λ (f : weak_dual 𝕜 E) (x : E), f x) ⁻¹' t,
  rw image_preimage_eq_inter_range,
  exact continuous_linear_map.is_closed_inter_range_coe htc
    (bounded_polar_of_mem_nhds_zero _ s_nhd)
end

/-- The image under `weak_dual.to_Pi : weak_dual 𝕜 E → (E → 𝕜)` of the polar `polar s` of
a neighborhood `s` of the origin is compact if the field `𝕜` is a proper topological space. -/
lemma is_compact_image_polar [proper_space 𝕜] {s : set E} (s_nhd : s ∈ 𝓝 (0 : E)) :
  is_compact ((λ (f : weak_dual 𝕜 E) (x : E), f x) '' (weak_dual.polar 𝕜 s)) :=
begin
  rw [← (is_closed_image_polar 𝕜 s_nhd).closure_eq],
  exact continuous_linear_map.is_compact_closure_image_coe_bounded
    (bounded_polar_of_mem_nhds_zero 𝕜 s_nhd)
end

/-- The **Banach-Alaoglu theorem**: the polar set of a neighborhood `s` of the origin in a
normed space `E` is a compact subset of `weak_dual 𝕜 E`. -/
theorem weak_dual.is_compact_polar [proper_space 𝕜] {s : set E} (s_nhd : s ∈ 𝓝 (0 : E)) :
  is_compact (weak_dual.polar 𝕜 s) :=
(coe_fn_embedding 𝕜 E).is_compact_iff_is_compact_image.mpr (is_compact_image_polar 𝕜 s_nhd)

end weak_dual

/-- The Banach-Alaoglu theorem: closed balls of the dual of a normed space `E` over `ℝ` or `ℂ`
are compact in the weak-star topology. -/
theorem weak_dual.is_compact_closed_ball
  {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [normed_group E] [normed_space 𝕜 E] (r : ℝ) (hr : 0 < r) :
  is_compact (id (closed_ball 0 r : set (normed_space.dual 𝕜 E)) : set (weak_dual 𝕜 E)) :=
begin
  have as_polar := @polar_closed_ball 𝕜 _ E _ _ r⁻¹ (inv_pos.mpr hr),
  simp only [one_div, inv_inv₀] at as_polar,
  rw ←as_polar,
  exact weak_dual.is_compact_polar (closed_ball_mem_nhds (0 : E) (inv_pos.mpr hr)),
end

end embedding_to_Pi
