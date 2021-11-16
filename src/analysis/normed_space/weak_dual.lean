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

The file is a stub, some TODOs below.

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
* `polar_nhd_weak_star_compact` (a version of the Banach-Alaoglu theorem): The polar set of a
  neighborhood of the origin in a normed space `E` over `ℝ` or `ℂ` is compact in `weak_dual _ E`.
* `unit_ball_weak_star_compact` (the most common special case of the Banach-Alaoglu theorem):
  The dual unit ball of a normed space `E` over `ℝ` or `ℂ` is compact in the weak-star topology.

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

open metric set normed_space

namespace polar

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]

lemma to_weak_dual_image_norm_eval_le_one (z : E) :
  (dual.to_weak_dual '' {x' : dual 𝕜 E | ∥ x' z ∥ ≤ 1}) = {x' : weak_dual 𝕜 E | ∥ x' z ∥ ≤ 1} :=
begin
  ext x',
  split,
  { rintros ⟨x'', ⟨h₁, h₂⟩⟩, rw ← h₂, exact h₁, },
  { intros h, use x', exact ⟨h, rfl⟩, },
end

/-- The polar `polar 𝕜 s` of a set `s : E` is a closed subset when the weak star topology
is used, i.e., when `polar 𝕜 s` is interpreted as a subset of `weak_dual 𝕜 E`. -/
lemma is_weak_dual_closed (s : set E) : is_closed (dual.to_weak_dual '' polar 𝕜 s) :=
begin
  by_cases s_emp : s = ∅,
  { rw [s_emp, of_empty, image_univ, range_iff_surjective.mpr dual.to_weak_dual.surjective],
    exact is_closed_univ, },
  rw [eq_Inter, inj_on.image_bInter_eq],
  { simp_rw to_weak_dual_image_norm_eval_le_one,
    apply is_closed_bInter,
    intros z hz,
    have eq : {x' : weak_dual 𝕜 E | ∥x' z∥ ≤ 1} = (λ (x' : weak_dual 𝕜 E), ∥x' z∥)⁻¹' (Iic 1),
    by refl,
    rw eq,
    refine is_closed.preimage _ (is_closed_Iic),
    apply continuous.comp continuous_norm (weak_dual.eval_continuous _ _ z), },
  { exact nonempty_def.mp (ne_empty_iff_nonempty.mp s_emp), },
  { apply dual.to_weak_dual.injective.inj_on, },
end

end polar

end polar_sets_in_weak_dual

section embedding_to_Pi

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]

open metric set

/-- The (weak) dual `weak_dual 𝕜 E` of a normed space `E` consists of bounded linear
functionals `E → 𝕜`. Such functionals can be interpreted as elements of the Cartesian
product `Π (_ : E), 𝕜` via the function `weak_dual.to_Pi : weak_dual 𝕜 E → Π (_ : E), 𝕜`. -/
def _root_.weak_dual.to_Pi (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
  (E : Type*) [topological_space E] [add_comm_group E] [module 𝕜 E]
  (x' : weak_dual 𝕜 E) := ((λ z, (x' z)) : (Π (_ : E), 𝕜))

/-- In the product of copies of a normed field, sets of the form `{g | ∥ f(i) - g(i) ∥ < ε}` for
`ε > 0` are neighborhoods of `f`. -/
lemma _root_.basic_nhd_of_Pi_normed_field {ι : Type*}
  (f : (Π (_ : ι), 𝕜)) (i : ι) {ε : ℝ} (ε_pos : 0 < ε) :
  {g : (Π (_ : ι), 𝕜) | ∥ f i - g i ∥ < ε} ∈ 𝓝 f :=
begin
  have eq : { g : (Π (_ : ι), 𝕜) | ∥ f i - g i ∥ < ε}
            = set.pi ({i} : set ι) (λ _, ball (f i) ε),
  { ext g,
    simp only [mem_ball, singleton_pi, mem_set_of_eq, mem_preimage],
    rw dist_comm,
    exact mem_ball_iff_norm.symm, },
  rw eq,
  apply set_pi_mem_nhds,
  exact finite_singleton i,
  intros j hj,
  have eq₀ : j = i := hj,
  rw eq₀,
  exact ball_mem_nhds (f i) ε_pos,
end

lemma pi_ball_bounds_fun_cpt [proper_space 𝕜] {s : set E} (s_nhd : s ∈ 𝓝 (0 : E)) :
  is_compact (set.pi (univ : set E)
    (λ z, (closed_ball (0 : 𝕜) (polar.bounds_fun 𝕜 s_nhd z)))) :=
begin
  apply is_compact_univ_pi,
  exact λ z, proper_space.is_compact_closed_ball 0 _,
end

/-- The function `weak_dual.to_Pi : weak_dual 𝕜 E → Π (_ : E), 𝕜` is an embedding. -/
lemma embedding_weak_dual_to_Pi :
  embedding (λ (x' : weak_dual 𝕜 E), weak_dual.to_Pi 𝕜 E x') :=
{ induced := eq_of_nhds_eq_nhds (congr_fun rfl),
  inj := begin
    intros φ₁ φ₂ h,
    ext z,
    exact congr_fun h z,
  end, }

namespace embedding_weak_dual_to_Pi

/-- The image of the polar `polar s` of a neighborhood `s` of the origin under
`weak_dual.to_Pi : weak_dual 𝕜 E → Π (_ : E), 𝕜` is contained in a product of closed balls. -/
lemma image_polar_nhd_subset {s : set E} (s_nhd : s ∈ 𝓝 (0 : E)) :
  (weak_dual.to_Pi 𝕜 E) '' (polar 𝕜 s) ⊆
    (set.pi (univ : set E) (λ z, (closed_ball (0 : 𝕜) (polar.bounds_fun 𝕜 s_nhd z)))) :=
begin
  intros f hf,
  simp at hf,
  rcases hf with ⟨x', hx', f_eq⟩,
  simp only [mem_closed_ball, dist_zero_right, mem_univ_pi],
  intros z,
  have key := polar.bounds_fun_spec 𝕜 s_nhd x' z,
  have eq : x' z = f z := congr_fun f_eq z,
  rw eq at key,
  exact key hx',
end

/-- Elements of the closure of the range of the embedding
`weak_dual.to_Pi : weak_dual 𝕜 E → Π (_ : E), 𝕜` are linear. Here it is stated as the elements
respecting linear combinations. -/
lemma linear_of_mem_closure_range'
  (f : (Π (_ : E), 𝕜)) (hf : f ∈ closure (range (weak_dual.to_Pi 𝕜 E)))
  (c₁ c₂ : 𝕜) (z₁ z₂ : E) : f (c₁ • z₁ + c₂ • z₂) = c₁ • f(z₁) + c₂ • f(z₂) :=
begin
  set φ : (Π (_ : E), 𝕜) → 𝕜 := (λ g, g (c₁ • z₁ + c₂ • z₂) - c₁ • g(z₁) - c₂ • g(z₂)) with hφ,
  have φ_cont : continuous φ,
  { apply continuous.sub,
    { apply continuous.sub,
      { exact continuous_apply (c₁ • z₁ + c₂ • z₂), },
      exact continuous.smul continuous_const (continuous_apply _), },
    exact continuous.smul continuous_const (continuous_apply _), },
  have sin_closed : is_closed ({0} : set 𝕜) := t1_space.t1 0,
  have preim_cl : is_closed (φ⁻¹' ({0} : set 𝕜)) := is_closed.preimage φ_cont sin_closed,
  suffices : range (weak_dual.to_Pi 𝕜 E) ⊆ φ⁻¹' ({0} : set 𝕜),
  { have key := (is_closed.closure_subset_iff preim_cl).mpr this hf,
    exact sub_eq_iff_eq_add'.mp (sub_eq_zero.mp key), },
  intros g hg,
  cases hg with g₀ hg₀,
  simp only [algebra.id.smul_eq_mul, mem_singleton_iff, norm_eq_zero, mem_preimage],
  rw [hφ, ← hg₀],
  dunfold weak_dual.to_Pi,
  rw add_comm,
  simp only [algebra.id.smul_eq_mul, continuous_linear_map.map_add, add_sub_cancel,
             sub_self, continuous_linear_map.map_smul],
end

/-- Elements of the closure of the range of the embedding
`weak_dual.to_Pi : weak_dual 𝕜 E → Π (_ : E), 𝕜` can be viewed as linear maps `E → 𝕜`. -/
def linear_of_mem_closure_range
  (f : (Π (_ : E), 𝕜)) (hf : f ∈ closure (range (weak_dual.to_Pi 𝕜 E))) :
  E →ₗ[𝕜] 𝕜 :=
{ to_fun := f,
  map_add' := begin
    intros z₁ z₂,
    have key := embedding_weak_dual_to_Pi.linear_of_mem_closure_range' f hf (1 : 𝕜) (1 : 𝕜) z₁ z₂,
    rwa [one_smul, one_smul, one_smul 𝕜 _, one_smul 𝕜 _] at key,
  end,
  map_smul' := begin
    intros c z,
    have key := embedding_weak_dual_to_Pi.linear_of_mem_closure_range' f hf c (0 : 𝕜) z (0 : E),
    rwa [zero_smul, zero_smul, add_zero, add_zero] at key,
  end, }

lemma linear_of_mem_closure_range_apply
  (f : (Π (_ : E), 𝕜)) (hf : f ∈ closure (range (@weak_dual.to_Pi 𝕜 _ E _ _ _))) (z : E) :
  embedding_weak_dual_to_Pi.linear_of_mem_closure_range f hf z = f z := rfl

/-- Elements of the closure of the image under `weak_dual.to_Pi : weak_dual 𝕜 E → Π (_ : E), 𝕜` of
a subset defined by a non-strict bound on the norm still satisfy the same bound. -/
lemma norm_eval_le_of_mem_closure_norm_eval_le
  (z : E) (c : ℝ) (f : (Π (_ : E), 𝕜))
  (hf : f ∈ closure ((weak_dual.to_Pi 𝕜 E) '' {x' : weak_dual 𝕜 E | ∥ x' z ∥ ≤ c})) :
  ∥ f z ∥ ≤ c :=
begin
  suffices : ∀ (ε : ℝ), 0 < ε → ∥ f (z) ∥ ≤ c + ε,
  { exact le_of_forall_pos_le_add this, },
  intros ε ε_pos,
  have nhd := basic_nhd_of_Pi_normed_field f z ε_pos,
  have clos := mem_closure_iff_nhds.mp hf _ nhd,
  cases clos with g hg,
  simp only [mem_image, mem_inter_eq, mem_set_of_eq] at hg,
  rcases hg with ⟨tri, ⟨y', ⟨at_z_le, eq_g⟩⟩⟩,
  have eq : y'.to_Pi z = y' z := rfl,
  rw [← eq_g, eq] at tri,
  have key := norm_add_le_of_le tri.le at_z_le,
  rwa [sub_add_cancel, add_comm] at key,
end

/-- Elements of the closure of the image under `weak_dual.to_Pi : weak_dual 𝕜 E → Π (_ : E), 𝕜` of
a polar `polar s` of a neighborhood `s` of the origin are continuous (linear) functions. -/
lemma continuous_of_mem_closure_polar_nhd
  {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {s : set E} (s_nhd : s ∈ 𝓝 (0 : E)) (φ : (Π (_ : E), 𝕜))
  (hφ : φ ∈ closure ((weak_dual.to_Pi 𝕜 E) '' (polar 𝕜 s))) :
  @continuous E 𝕜 _ _ φ :=
begin
  cases @polar.bounded_of_nbhd_zero 𝕜 _ E _ _ s s_nhd with c hc,
  have c_nn : 0 ≤ c := le_trans (norm_nonneg _) (hc 0 (polar.zero_mem s)),
  have hφ' : φ ∈ closure (range (weak_dual.to_Pi 𝕜 E)),
  { apply mem_of_mem_of_subset hφ _,
    apply closure_mono,
    simp only [preimage_range, subset_univ, image_subset_iff], },
  set flin := embedding_weak_dual_to_Pi.linear_of_mem_closure_range φ hφ' with hflin,
  suffices : continuous flin,
  { assumption, },
  apply linear_map.continuous_of_bound flin c,
  intros z,
  set θ := λ (ψ : Π (_ : E), 𝕜), ∥ ψ z ∥ with hθ,
  have θ_cont : continuous θ,
  { apply continuous.comp continuous_norm,
    exact continuous_apply z, },
  have sin_closed : is_closed (Icc (-c * ∥z∥) (c * ∥z∥) : set ℝ) := is_closed_Icc,
  have preim_cl := is_closed.preimage θ_cont sin_closed,
  suffices :
    (weak_dual.to_Pi 𝕜 E) '' (polar 𝕜 s) ⊆ θ⁻¹' (Icc (-c * ∥z∥) (c * ∥z∥)),
  { exact ((is_closed.closure_subset_iff preim_cl).mpr this hφ).right, },
  intros ψ hψ,
  rcases hψ with ⟨x', ⟨polar_x', ψ_x'⟩⟩,
  rw ← ψ_x',
  simp only [neg_mul_eq_neg_mul_symm, mem_preimage, mem_Icc, hθ],
  split,
  { apply le_trans _ (norm_nonneg _),
    rw right.neg_nonpos_iff,
    exact mul_nonneg c_nn (norm_nonneg _), },
  apply le_trans (continuous_linear_map.le_op_norm x' z) _,
  exact mul_le_mul (hc x' polar_x') rfl.ge (norm_nonneg z) c_nn,
end

/-- The image under `weak_dual.to_Pi : weak_dual 𝕜 E → Π (_ : E), 𝕜` of a polar `polar s` of a
neighborhood `s` of the origin is a closed set. -/
lemma image_polar_nhd_closed
  {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {s : set E} (s_nhd : s ∈ 𝓝 (0 : E)) :
  is_closed ((weak_dual.to_Pi 𝕜 E) '' (polar 𝕜 s)) :=
begin
  apply is_closed_iff_cluster_pt.mpr,
  intros f hf,
  simp only [mem_image, mem_set_of_eq],
  have f_in_closure : f ∈ closure ((weak_dual.to_Pi 𝕜 E) '' (polar 𝕜 s)),
  from mem_closure_iff_cluster_pt.mpr hf,
  have f_in_closure₀ : f ∈ closure (range (weak_dual.to_Pi 𝕜 E)),
  { apply closure_mono (image_subset_range _ _),
    exact mem_closure_iff_cluster_pt.mpr hf, },
  set f_lin := embedding_weak_dual_to_Pi.linear_of_mem_closure_range f f_in_closure₀ with h_f_lin,
  have f_cont := embedding_weak_dual_to_Pi.continuous_of_mem_closure_polar_nhd
    s_nhd f f_in_closure,
  set φ : weak_dual 𝕜 E :=
    { to_fun := f,
      map_add' := begin
        intros z₁ z₂,
        have key := f_lin.map_add z₁ z₂,
        rw h_f_lin at key,
        repeat {rwa embedding_weak_dual_to_Pi.linear_of_mem_closure_range_apply
          f f_in_closure₀ _ at key, },
      end,
      map_smul' := begin
        intros c z,
        have key := f_lin.map_smul c z,
        rw h_f_lin at key,
        repeat {rwa embedding_weak_dual_to_Pi.linear_of_mem_closure_range_apply
          f f_in_closure₀ _ at key, },
      end,
      cont := f_cont, } with hφ,
  use φ,
  split,
  { dunfold polar,
    simp,
    intros z hz,
    apply embedding_weak_dual_to_Pi.norm_eval_le_of_mem_closure_norm_eval_le z 1 f,
    have ss : polar s ⊆ {x' : weak_dual 𝕜 E | ∥x' z∥ ≤ 1},
    { intros x' hx',
      exact hx' z hz, },
    apply closure_mono (image_subset _ ss),
    exact mem_closure_iff_cluster_pt.mpr hf, },
  { ext z,
    dunfold weak_dual.to_Pi,
    rw hφ,
    simp, },
end

/-- The image under `weak_dual.to_Pi : weak_dual 𝕜 E → Π (_ : E), 𝕜` of the polar `polar s` of
a neighborhood `s` of the origin is compact. -/
lemma image_polar_nhd_compact
  {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {s : set E} (s_nhd : s ∈ 𝓝 (0 : E)) :
  is_compact ((weak_dual.to_Pi 𝕜 E) '' (polar 𝕜 s)) :=
begin
  apply compact_of_is_closed_subset _ _ (embedding_weak_dual_to_Pi.image_polar_nhd_subset s_nhd),
  exact pi_ball_bounds_fun_cpt s_nhd,
  exact embedding_weak_dual_to_Pi.image_polar_nhd_closed s_nhd,
end

end embedding_weak_dual_to_Pi

/-- The Banach-Alaoglu theorem: the polar `polar s` of a neighborhood `s` of the origin in a
normed space `E` over `𝕜` is compact subset of `weak_dual 𝕜 E` (assuming `[is_R_or_C 𝕜]`). -/
theorem polar_nhd_weak_star_compact
  {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {s : set E} (s_nhd : s ∈ 𝓝 (0 : E)) : is_compact (polar 𝕜 s) :=
begin
  apply (embedding_weak_dual_to_Pi 𝕜 E).is_compact_iff_is_compact_image.mpr,
  exact embedding_weak_dual_to_Pi.image_polar_nhd_compact s_nhd,
end

/-- The Banach-Alaoglu theorem: the dual unit ball is compact in the weak-star topology. -/
theorem unit_ball_weak_star_compact
  {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [normed_group E] [normed_space 𝕜 E] :
  is_compact {x' : weak_dual 𝕜 E | (∥ x'.to_normed_dual ∥ ≤ 1)} :=
begin
  rw ← polar.closed_unit_ball,
  apply polar_nhd_weak_star_compact (closed_ball_mem_nhds (0 : E) (@zero_lt_one ℝ _ _)),
end

end embedding_to_Pi
