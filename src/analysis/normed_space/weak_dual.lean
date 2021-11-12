/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import topology.algebra.weak_dual_topology
import analysis.normed_space.dual
import analysis.normed_space.operator_norm
import analysis.seminorm
import analysis.normed_space.is_R_or_C

/-!
# Weak dual of normed space

Let `E` be a normed space over a field `𝕜`. This file is concerned with properties of the weak-*
topology on the dual of `E`. By the dual, we mean either of the type synonyms
`normed_space.dual 𝕜 E` or `weak_dual 𝕜 E`, depending on whether it is viewed as equipped with its
usual operator norm topology or the weak-* topology.

It is shown that the canonical mapping `normed_space.dual 𝕜 E → weak_dual 𝕜 E` is continuous, and
as a consequence the weak-* topology is coarser than the topology obtained from the operator norm
(dual norm).

The file is a stub, some TODOs below.

## Main definitions

The main definitions concern the canonical mapping `dual 𝕜 E → weak_dual 𝕜 E`.

* `normed_space.dual.to_weak_dual` and `weak_dual.to_normed_dual`: Linear equivalences from
  `dual 𝕜 E` to `weak_dual 𝕜 E` and in the converse direction.
* `normed_space.dual.continuous_linear_map_to_weak_dual`: A continuous linear mapping from
  `dual 𝕜 E` to `weak_dual 𝕜 E` (same as `normed_space.dual.to_weak_dual` but different bundled
  data).
* `polar s` is the subset of `weak_dual 𝕜 E` consisting of those functionals `x'` for which
  `∥x' z∥ ≤ 1` for every `z ∈ s`.

## Main results

The first main result concerns the comparison of the operator norm topology on `dual 𝕜 E` and the
weak-* topology on (its type synonym) `weak_dual 𝕜 E`:
* `dual_norm_topology_le_weak_dual_topology`: The weak-* topology on the dual of a normed space is
  coarser (not necessarily strictly) than the operator norm topology.

TODOs:
* Add that in finite dimensions, the weak-* topology and the dual norm topology coincide.
* Add that in infinite dimensions, the weak-* topology is strictly coarser than the dual norm
  topology.
* Add Banach-Alaoglu theorem (general version maybe in `topology.algebra.weak_dual_topology`).
* Add metrizability of the dual unit ball (more generally bounded subsets) of `weak_dual 𝕜 E`
  under the assumption of separability of `E`. Sequential Banach-Alaoglu theorem would then follow
  from the general one.

## Notations

No new notation is introduced.

## Implementation notes

Weak-* topology is defined generally in the file `topology.algebra.weak_dual_topology`.

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

end weak_star_topology_for_duals_of_normed_spaces

section polar_sets_in_weak_dual

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]

open metric set

/-- Given a subset `s` in a normed space `E` (over a field `𝕜`), the polar
`polar s` is the subset of `weak_dual 𝕜 E` consisting of those functionals which
evaluate to something of norm at most one at all points `z ∈ s`. -/
def polar (s : set E) : set (weak_dual 𝕜 E) :=
{x' : weak_dual 𝕜 E | ∀ z ∈ s, ∥ x' z ∥ ≤ 1 }

namespace polar

@[simp] lemma zero_mem (s : set E) :
  (0 : weak_dual 𝕜 E) ∈ (@polar 𝕜 _ E _ _ s) :=
λ _ _, by simp only [zero_le_one, continuous_linear_map.zero_apply, norm_zero]

lemma eq_Inter (s : set E) :
  (@polar 𝕜 _ E _ _ s) = ⋂ z ∈ s, {x' : weak_dual 𝕜 E | ∥ x' z ∥ ≤ 1 } :=
by { dunfold polar, ext, simp only [mem_bInter_iff, mem_set_of_eq], }

/-- The polar `polar s` of a set `s : E` is a closed subset of `weak_dual 𝕜 E`. -/
lemma is_closed (s : set E) : is_closed (@polar 𝕜 _ E _ _ s) :=
begin
  rw eq_Inter,
  apply is_closed_bInter,
  intros z hz,
  have eq : {x' : weak_dual 𝕜 E | ∥x' z∥ ≤ 1} = (λ (x' : weak_dual 𝕜 E), ∥x' z∥)⁻¹' (Iic 1),
  by refl,
  rw eq,
  refine is_closed.preimage _ (is_closed_Iic),
  apply continuous.comp continuous_norm (weak_dual.eval_continuous _ _ z),
end

/-- If `x'` is a dual element such that the norms `∥ x' z ∥` are bounded for `z ∈ s`, then a
small scalar multiple of `x'` is in `polar s`. -/
lemma smul_mem {s : set E} {x' : weak_dual 𝕜 E} {c : 𝕜}
  (hc : ∀ z, z ∈ s → ∥ x' z ∥ ≤ ∥c∥) : (c⁻¹ • x') ∈ (@polar 𝕜 _ E _ _ s) :=
begin
  by_cases c_zero : c = 0,
  { rw c_zero,
    dunfold polar,
    simp only [zero_le_one, continuous_linear_map.zero_apply, norm_zero,
               mem_set_of_eq, implies_true_iff, inv_zero, zero_smul], },
  have eq : ∀ z, ∥ c⁻¹ • (x' z) ∥ = ∥ c⁻¹ ∥ * ∥ x' z ∥ := λ z, norm_smul c⁻¹ _,
  have le : ∀ z, z ∈ s → ∥ c⁻¹ • (x' z) ∥ ≤ ∥ c⁻¹ ∥ * ∥ c ∥,
  { intros z hzs,
    rw eq z,
    apply mul_le_mul (le_of_eq rfl) (hc z hzs) (norm_nonneg _) (norm_nonneg _), },
  have cancel : ∥ c⁻¹ ∥ * ∥ c ∥ = 1,
  by simp only [c_zero, norm_eq_zero, ne.def, not_false_iff,
                inv_mul_cancel, normed_field.norm_inv],
  rwa cancel at le,
end

/-- The `polar` of closed unit ball in a normed space `E` is the closed unit ball of the (normed)
dual (seen as a subset of the weak dual). -/
lemma of_closed_unit_ball
  {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [normed_group E] [normed_space 𝕜 E] :
  (@polar 𝕜 _ E _ _ (closed_ball (0 : E) 1))
    = {x' : weak_dual 𝕜 E | (∥ x'.to_normed_dual ∥ ≤ 1) } :=
begin
  ext x',
  simp only [mem_closed_ball, mem_set_of_eq, dist_zero_right],
  split,
  { intros h,
    apply continuous_linear_map.op_norm_le_of_ball zero_lt_one zero_le_one,
    intros z hz,
    have key := linear_map.bound_of_ball_bound zero_lt_one 1 x'.to_normed_dual.to_linear_map h z,
    simp only [continuous_linear_map.to_linear_map_eq_coe,
               continuous_linear_map.coe_coe, div_one] at key,
    exact key, },
  { intros h z hz,
    simp only [mem_closed_ball, dist_zero_right] at hz,
    apply (continuous_linear_map.unit_le_op_norm x'.to_normed_dual z hz).trans h, },
end

/-- If `s` is a neighborhood of the origin in a normed space `E`, then at any point `z : E`
there exists a bound for the norms of the values `x' z` of the elements `x' ∈ polar s` of the
polar of `s`. -/
lemma eval_bounded_of_nbhd_zero {s : set E} (s_nhd : s ∈ 𝓝 (0 : E)) (z : E) :
  ∃ (r : ℝ), ∀ (x' : weak_dual 𝕜 E), x' ∈ @polar 𝕜 _ E _ _ s → (∥ x' z ∥ ≤ r) :=
begin
  have s_absnt : absorbent 𝕜 s := absorbent_nhds_zero s_nhd,
  rcases s_absnt z with ⟨c, ⟨c_pos, hc⟩⟩,
  cases normed_field.exists_lt_norm 𝕜 c with a ha,
  specialize hc a ha.le,
  have a_norm_pos : 0 < ∥ a ∥ := lt_trans c_pos ha,
  have a_ne_zero : a ≠ 0 := norm_pos_iff.mp a_norm_pos,
  have w_in_s : a⁻¹ • z ∈ s,
  { rcases hc with ⟨ w , ⟨hws, haw⟩⟩,
    rwa [← haw, ← mul_smul, inv_mul_cancel a_ne_zero, one_smul], },
  use ∥a∥,
  intros x' hx',
  specialize hx' _ w_in_s,
  simp only [algebra.id.smul_eq_mul, normed_field.norm_mul,
             continuous_linear_map.map_smul, normed_field.norm_inv] at hx',
  have key := mul_le_mul (@rfl _ ∥ a ∥).ge hx' _ (norm_nonneg a),
  rwa [mul_one, ← mul_assoc, mul_inv_cancel (ne_of_gt a_norm_pos), one_mul] at key,
  apply mul_nonneg _ (norm_nonneg _),
  simp only [inv_nonneg, norm_nonneg],
end

/-- If `s` is a neighborhood of the origin in a normed space `E`, then there exists a
function `r : E → ℝ` such that for all elements `x' ∈ polar s` one has `∥ x' z ∥ ≤ r(z)`. -/
lemma finite_values_of_nbhd_zero {s : set E} (s_nhd : s ∈ 𝓝 (0 : E)) :
  ∃ (r : E → ℝ), ∀ (x' : weak_dual 𝕜 E) (z : E), x' ∈ (@polar 𝕜 _ E _ _ s) → ∥ x' z ∥ ≤ r z :=
begin
  cases classical.axiom_of_choice (@eval_bounded_of_nbhd_zero 𝕜 _ E _ _ s s_nhd) with r hr,
  use r,
  intros x' z,
  exact hr z x',
end

/-- Given a neighborhood `s` of the origin in a normed space `E` over `ℝ` or `ℂ`, the dual norms
of all elements of the polar `polar s` are bounded by a constant. -/
lemma bounded_of_nbhd_zero
  {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {s : set E} (s_nhd : s ∈ 𝓝 (0 : E)) :
  ∃ (c : ℝ), ∀ (x' : weak_dual 𝕜 E), x' ∈ @polar 𝕜 _ E _ _ s → (∥ x'.to_normed_dual ∥ ≤ c) :=
begin
  rcases metric.mem_nhds_iff.mp s_nhd with ⟨r, ⟨r_pos, r_ball⟩⟩,
  have half_r_pos : 0 < r / 2 := by linarith,
  use 2 / r,
  intros x' hx',
  have key := continuous_linear_map.op_norm_bound_of_ball_bound half_r_pos 1 x',
  simp only [one_div_div] at key,
  apply key,
  intros z hz,
  have z_mem_ball : z ∈ ball (0 : E) r,
  { simp only [mem_ball_zero_iff],
    simp only [mem_closed_ball, dist_zero_right] at hz,
    linarith, },
  exact hx' z (r_ball z_mem_ball),
end

/-- Given a neighborhood `s` of the origin in a normed space `E`, for any `z : E` it
is possible to choose a real number `r` such that for any functional `x' ∈ polar s` in
the polar of `s`, the value at `z` satisfies the norm bound `∥ x' z ∥ ≤ r`. Such an `r`
is given by `bounds_fun _ z`. -/
def bounds_fun {s : set E} (s_nhd : s ∈ 𝓝 (0 : E)) : E → ℝ :=
classical.some (classical.axiom_of_choice (@eval_bounded_of_nbhd_zero 𝕜 _ E _ _ s s_nhd))

lemma bounds_fun_spec {s : set E} (s_nhd : s ∈ 𝓝 (0 : E))
  (x' : weak_dual 𝕜 E) (z : E) :
  x' ∈ @polar 𝕜 _ E _ _ s → ∥ x' z ∥ ≤ @bounds_fun 𝕜 _ E _ _ s s_nhd z :=
classical.some_spec
  (classical.axiom_of_choice (@eval_bounded_of_nbhd_zero 𝕜 _ E _ _ s s_nhd)) z x'

end polar

end polar_sets_in_weak_dual
