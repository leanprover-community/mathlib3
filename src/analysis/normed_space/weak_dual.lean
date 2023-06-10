/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Yury Kudryashov
-/
import topology.algebra.module.weak_dual
import analysis.normed_space.dual
import analysis.normed_space.operator_norm

/-!
# Weak dual of normed space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
  nontrivially normed field `𝕜` is proper as a topological space.
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
  is sequentially compact in the weak-star topology. This would follow from the metrizability above.

## Notations

No new notation is introduced.

## Implementation notes

Weak-* topology is defined generally in the file `topology.algebra.module.weak_dual`.

When `E` is a normed space, the duals `dual 𝕜 E` and `weak_dual 𝕜 E` are type synonyms with
different topology instances.

For the proof of Banach-Alaoglu theorem, the weak dual of `E` is embedded in the space of
functions `E → 𝕜` with the topology of pointwise convergence.

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
open filter function metric set
open_locale topology filter

/-!
### Weak star topology on duals of normed spaces

In this section, we prove properties about the weak-* topology on duals of normed spaces.
We prove in particular that the canonical mapping `dual 𝕜 E → weak_dual 𝕜 E` is continuous,
i.e., that the weak-* topology is coarser (not necessarily strictly) than the topology given
by the dual-norm (i.e. the operator-norm).
-/

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
variables {E : Type*} [seminormed_add_comm_group E] [normed_space 𝕜 E]

namespace normed_space

namespace dual

/-- For normed spaces `E`, there is a canonical map `dual 𝕜 E → weak_dual 𝕜 E` (the "identity"
mapping). It is a linear equivalence. -/
def to_weak_dual : dual 𝕜 E ≃ₗ[𝕜] weak_dual 𝕜 E := linear_equiv.refl 𝕜 (E →L[𝕜] 𝕜)

@[simp] lemma coe_to_weak_dual (x' : dual 𝕜 E) : ⇑(x'.to_weak_dual) = x' := rfl

@[simp] lemma to_weak_dual_eq_iff (x' y' : dual 𝕜 E) :
  x'.to_weak_dual = y'.to_weak_dual ↔ x' = y' :=
to_weak_dual.injective.eq_iff

theorem to_weak_dual_continuous : continuous (λ (x' : dual 𝕜 E), x'.to_weak_dual) :=
weak_bilin.continuous_of_continuous_eval _ $ λ z, (inclusion_in_double_dual 𝕜 E z).continuous

/-- For a normed space `E`, according to `to_weak_dual_continuous` the "identity mapping"
`dual 𝕜 E → weak_dual 𝕜 E` is continuous. This definition implements it as a continuous linear
map. -/
def continuous_linear_map_to_weak_dual : dual 𝕜 E →L[𝕜] weak_dual 𝕜 E :=
{ cont := to_weak_dual_continuous, .. to_weak_dual, }

/-- The weak-star topology is coarser than the dual-norm topology. -/
theorem dual_norm_topology_le_weak_dual_topology :
  (by apply_instance : topological_space (dual 𝕜 E)) ≤
    (by apply_instance : topological_space (weak_dual 𝕜 E)) :=
by { convert to_weak_dual_continuous.le_induced, exact induced_id.symm }

end dual
end normed_space

namespace weak_dual

open normed_space

/-- For normed spaces `E`, there is a canonical map `weak_dual 𝕜 E → dual 𝕜 E` (the "identity"
mapping). It is a linear equivalence. Here it is implemented as the inverse of the linear
equivalence `normed_space.dual.to_weak_dual` in the other direction. -/
def to_normed_dual : weak_dual 𝕜 E ≃ₗ[𝕜] dual 𝕜 E := normed_space.dual.to_weak_dual.symm

lemma to_normed_dual_apply (x : weak_dual 𝕜 E) (y : E) : (to_normed_dual x) y = x y := rfl

@[simp] lemma coe_to_normed_dual (x' : weak_dual 𝕜 E) : ⇑(x'.to_normed_dual) = x' := rfl

@[simp] lemma to_normed_dual_eq_iff (x' y' : weak_dual 𝕜 E) :
  x'.to_normed_dual = y'.to_normed_dual ↔ x' = y' :=
weak_dual.to_normed_dual.injective.eq_iff

lemma is_closed_closed_ball (x' : dual 𝕜 E) (r : ℝ) :
  is_closed (to_normed_dual ⁻¹' closed_ball x' r) :=
is_closed_induced_iff'.2 (continuous_linear_map.is_weak_closed_closed_ball x' r)

/-!
### Polar sets in the weak dual space
-/

variables (𝕜)

/-- The polar set `polar 𝕜 s` of `s : set E` seen as a subset of the dual of `E` with the
weak-star topology is `weak_dual.polar 𝕜 s`. -/
def polar (s : set E) : set (weak_dual 𝕜 E) := to_normed_dual ⁻¹' polar 𝕜 s

lemma polar_def (s : set E) : polar 𝕜 s = {f : weak_dual 𝕜 E | ∀ x ∈ s, ‖f x‖ ≤ 1} := rfl

/-- The polar `polar 𝕜 s` of a set `s : E` is a closed subset when the weak star topology
is used. -/
lemma is_closed_polar (s : set E) : is_closed (polar 𝕜 s) :=
begin
  simp only [polar_def, set_of_forall],
  exact is_closed_bInter (λ x hx, is_closed_Iic.preimage (weak_bilin.eval_continuous _ _).norm)
end

variable {𝕜}

/-- While the coercion `coe_fn : weak_dual 𝕜 E → (E → 𝕜)` is not a closed map, it sends *bounded*
closed sets to closed sets. -/
lemma is_closed_image_coe_of_bounded_of_closed {s : set (weak_dual 𝕜 E)}
  (hb : bounded (dual.to_weak_dual ⁻¹' s)) (hc : is_closed s) :
  is_closed ((coe_fn : weak_dual 𝕜 E → E → 𝕜) '' s) :=
continuous_linear_map.is_closed_image_coe_of_bounded_of_weak_closed hb (is_closed_induced_iff'.1 hc)

lemma is_compact_of_bounded_of_closed [proper_space 𝕜] {s : set (weak_dual 𝕜 E)}
  (hb : bounded (dual.to_weak_dual ⁻¹' s)) (hc : is_closed s) :
  is_compact s :=
(embedding.is_compact_iff_is_compact_image fun_like.coe_injective.embedding_induced).mpr $
  continuous_linear_map.is_compact_image_coe_of_bounded_of_closed_image hb $
  is_closed_image_coe_of_bounded_of_closed hb hc

variable (𝕜)

/-- The image under `coe_fn : weak_dual 𝕜 E → (E → 𝕜)` of a polar `weak_dual.polar 𝕜 s` of a
neighborhood `s` of the origin is a closed set. -/
lemma is_closed_image_polar_of_mem_nhds {s : set E} (s_nhd : s ∈ 𝓝 (0 : E)) :
  is_closed ((coe_fn : weak_dual 𝕜 E → E → 𝕜) '' polar 𝕜 s) :=
is_closed_image_coe_of_bounded_of_closed (bounded_polar_of_mem_nhds_zero 𝕜 s_nhd)
  (is_closed_polar _ _)

/-- The image under `coe_fn : normed_space.dual 𝕜 E → (E → 𝕜)` of a polar `polar 𝕜 s` of a
neighborhood `s` of the origin is a closed set. -/
lemma _root_.normed_space.dual.is_closed_image_polar_of_mem_nhds {s : set E}
  (s_nhd : s ∈ 𝓝 (0 : E)) : is_closed ((coe_fn : dual 𝕜 E → E → 𝕜) '' normed_space.polar 𝕜 s) :=
is_closed_image_polar_of_mem_nhds 𝕜 s_nhd

/-- The **Banach-Alaoglu theorem**: the polar set of a neighborhood `s` of the origin in a
normed space `E` is a compact subset of `weak_dual 𝕜 E`. -/
theorem is_compact_polar [proper_space 𝕜] {s : set E} (s_nhd : s ∈ 𝓝 (0 : E)) :
  is_compact (polar 𝕜 s) :=
is_compact_of_bounded_of_closed (bounded_polar_of_mem_nhds_zero 𝕜 s_nhd) (is_closed_polar _ _)

/-- The **Banach-Alaoglu theorem**: closed balls of the dual of a normed space `E` are compact in
the weak-star topology. -/
theorem is_compact_closed_ball [proper_space 𝕜] (x' : dual 𝕜 E) (r : ℝ) :
  is_compact (to_normed_dual ⁻¹' (closed_ball x' r)) :=
is_compact_of_bounded_of_closed bounded_closed_ball (is_closed_closed_ball x' r)

end weak_dual
