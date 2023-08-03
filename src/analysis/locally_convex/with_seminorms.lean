/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Anatole Dedecker
-/

import analysis.seminorm
import analysis.locally_convex.bounded
import topology.algebra.filter_basis
import topology.algebra.module.locally_convex

/-!
# Topology induced by a family of seminorms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `seminorm_family.basis_sets`: The set of open seminorm balls for a family of seminorms.
* `seminorm_family.module_filter_basis`: A module filter basis formed by the open balls.
* `seminorm.is_bounded`: A linear map `f : E →ₗ[𝕜] F` is bounded iff every seminorm in `F` can be
bounded by a finite number of seminorms in `E`.

## Main statements

* `with_seminorms.to_locally_convex_space`: A space equipped with a family of seminorms is locally
convex.
* `with_seminorms.first_countable`: A space is first countable if it's topology is induced by a
countable family of seminorms.

## Continuity of semilinear maps

If `E` and `F` are topological vector space with the topology induced by a family of seminorms, then
we have a direct method to prove that a linear map is continuous:
* `seminorm.continuous_from_bounded`: A bounded linear map `f : E →ₗ[𝕜] F` is continuous.

If the topology of a space `E` is induced by a family of seminorms, then we can characterize von
Neumann boundedness in terms of that seminorm family. Together with
`linear_map.continuous_of_locally_bounded` this gives general criterion for continuity.

* `with_seminorms.is_vonN_bounded_iff_finset_seminorm_bounded`
* `with_seminorms.is_vonN_bounded_iff_seminorm_bounded`
* `with_seminorms.image_is_vonN_bounded_iff_finset_seminorm_bounded`
* `with_seminorms.image_is_vonN_bounded_iff_seminorm_bounded`

## Tags

seminorm, locally convex
-/

open normed_field set seminorm topological_space
open_locale big_operators nnreal pointwise topology

variables {𝕜 𝕜₂ 𝕝 𝕝₂ E F G ι ι' : Type*}

section filter_basis

variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E]

variables (𝕜 E ι)

/-- An abbreviation for indexed families of seminorms. This is mainly to allow for dot-notation. -/
abbreviation seminorm_family := ι → seminorm 𝕜 E

variables {𝕜 E ι}

namespace seminorm_family

/-- The sets of a filter basis for the neighborhood filter of 0. -/
def basis_sets (p : seminorm_family 𝕜 E ι) : set (set E) :=
⋃ (s : finset ι) r (hr : 0 < r), singleton $ ball (s.sup p) (0 : E) r

variables (p : seminorm_family 𝕜 E ι)

lemma basis_sets_iff {U : set E} :
  U ∈ p.basis_sets ↔ ∃ (i : finset ι) r (hr : 0 < r), U = ball (i.sup p) 0 r :=
by simp only [basis_sets, mem_Union, mem_singleton_iff]

lemma basis_sets_mem (i : finset ι) {r : ℝ} (hr : 0 < r) :
  (i.sup p).ball 0 r ∈ p.basis_sets :=
(basis_sets_iff _).mpr ⟨i,_,hr,rfl⟩

lemma basis_sets_singleton_mem (i : ι) {r : ℝ} (hr : 0 < r) :
  (p i).ball 0 r ∈ p.basis_sets :=
(basis_sets_iff _).mpr ⟨{i},_,hr, by rw finset.sup_singleton⟩

lemma basis_sets_nonempty [nonempty ι] : p.basis_sets.nonempty :=
begin
  let i := classical.arbitrary ι,
  refine set.nonempty_def.mpr ⟨(p i).ball 0 1, _⟩,
  exact p.basis_sets_singleton_mem i zero_lt_one,
end

lemma basis_sets_intersect
  (U V : set E) (hU : U ∈ p.basis_sets) (hV : V ∈ p.basis_sets) :
  ∃ (z : set E) (H : z ∈ p.basis_sets), z ⊆ U ∩ V :=
begin
  classical,
  rcases p.basis_sets_iff.mp hU with ⟨s, r₁, hr₁, hU⟩,
  rcases p.basis_sets_iff.mp hV with ⟨t, r₂, hr₂, hV⟩,
  use ((s ∪ t).sup p).ball 0 (min r₁ r₂),
  refine ⟨p.basis_sets_mem (s ∪ t) (lt_min_iff.mpr ⟨hr₁, hr₂⟩), _⟩,
  rw [hU, hV, ball_finset_sup_eq_Inter _ _ _ (lt_min_iff.mpr ⟨hr₁, hr₂⟩),
    ball_finset_sup_eq_Inter _ _ _ hr₁, ball_finset_sup_eq_Inter _ _ _ hr₂],
  exact set.subset_inter
    (set.Inter₂_mono' $ λ i hi, ⟨i, finset.subset_union_left _ _ hi, ball_mono $ min_le_left _ _⟩)
    (set.Inter₂_mono' $ λ i hi, ⟨i, finset.subset_union_right _ _ hi, ball_mono $
    min_le_right _ _⟩),
end

lemma basis_sets_zero (U) (hU : U ∈ p.basis_sets) :
  (0 : E) ∈ U :=
begin
  rcases p.basis_sets_iff.mp hU with ⟨ι', r, hr, hU⟩,
  rw [hU, mem_ball_zero, map_zero],
  exact hr,
end

lemma basis_sets_add (U) (hU : U ∈ p.basis_sets) :
  ∃ (V : set E) (H : V ∈ p.basis_sets), V + V ⊆ U :=
begin
  rcases p.basis_sets_iff.mp hU with ⟨s, r, hr, hU⟩,
  use (s.sup p).ball 0 (r/2),
  refine ⟨p.basis_sets_mem s (div_pos hr zero_lt_two), _⟩,
  refine set.subset.trans (ball_add_ball_subset (s.sup p) (r/2) (r/2) 0 0) _,
  rw [hU, add_zero, add_halves'],
end

lemma basis_sets_neg (U) (hU' : U ∈ p.basis_sets) :
  ∃ (V : set E) (H : V ∈ p.basis_sets), V ⊆ (λ (x : E), -x) ⁻¹' U :=
begin
  rcases p.basis_sets_iff.mp hU' with ⟨s, r, hr, hU⟩,
  rw [hU, neg_preimage, neg_ball (s.sup p), neg_zero],
  exact ⟨U, hU', eq.subset hU⟩,
end

/-- The `add_group_filter_basis` induced by the filter basis `seminorm_basis_zero`. -/
protected def add_group_filter_basis [nonempty ι] : add_group_filter_basis E :=
add_group_filter_basis_of_comm p.basis_sets p.basis_sets_nonempty
  p.basis_sets_intersect p.basis_sets_zero p.basis_sets_add p.basis_sets_neg

lemma basis_sets_smul_right (v : E) (U : set E)
  (hU : U ∈ p.basis_sets) : ∀ᶠ (x : 𝕜) in 𝓝 0, x • v ∈ U :=
begin
  rcases p.basis_sets_iff.mp hU with ⟨s, r, hr, hU⟩,
  rw [hU, filter.eventually_iff],
  simp_rw [(s.sup p).mem_ball_zero, map_smul_eq_mul],
  by_cases h : 0 < (s.sup p) v,
  { simp_rw (lt_div_iff h).symm,
    rw ←_root_.ball_zero_eq,
    exact metric.ball_mem_nhds 0 (div_pos hr h) },
  simp_rw [le_antisymm (not_lt.mp h) (map_nonneg _ v), mul_zero, hr],
  exact is_open.mem_nhds is_open_univ (mem_univ 0),
end

variables [nonempty ι]

lemma basis_sets_smul (U) (hU : U ∈ p.basis_sets) :
  ∃ (V : set 𝕜) (H : V ∈ 𝓝 (0 : 𝕜)) (W : set E)
  (H : W ∈ p.add_group_filter_basis.sets), V • W ⊆ U :=
begin
  rcases p.basis_sets_iff.mp hU with ⟨s, r, hr, hU⟩,
  refine ⟨metric.ball 0 r.sqrt, metric.ball_mem_nhds 0 (real.sqrt_pos.mpr hr), _⟩,
  refine ⟨(s.sup p).ball 0 r.sqrt, p.basis_sets_mem s (real.sqrt_pos.mpr hr), _⟩,
  refine set.subset.trans (ball_smul_ball (s.sup p) r.sqrt r.sqrt) _,
  rw [hU, real.mul_self_sqrt (le_of_lt hr)],
end

lemma basis_sets_smul_left (x : 𝕜) (U : set E)
  (hU : U ∈ p.basis_sets) : ∃ (V : set E)
  (H : V ∈ p.add_group_filter_basis.sets), V ⊆ (λ (y : E), x • y) ⁻¹' U :=
begin
  rcases p.basis_sets_iff.mp hU with ⟨s, r, hr, hU⟩,
  rw hU,
  by_cases h : x ≠ 0,
  { rw [(s.sup p).smul_ball_preimage 0 r x h, smul_zero],
    use (s.sup p).ball 0 (r / ‖x‖),
    exact ⟨p.basis_sets_mem s (div_pos hr (norm_pos_iff.mpr h)), subset.rfl⟩ },
  refine ⟨(s.sup p).ball 0 r, p.basis_sets_mem s hr, _⟩,
  simp only [not_ne_iff.mp h, subset_def, mem_ball_zero, hr, mem_univ, map_zero,
    implies_true_iff, preimage_const_of_mem, zero_smul],
end

/-- The `module_filter_basis` induced by the filter basis `seminorm_basis_zero`. -/
protected def module_filter_basis : module_filter_basis 𝕜 E :=
{ to_add_group_filter_basis := p.add_group_filter_basis,
  smul' := p.basis_sets_smul,
  smul_left' := p.basis_sets_smul_left,
  smul_right' := p.basis_sets_smul_right }

lemma filter_eq_infi (p : seminorm_family 𝕜 E ι) :
  p.module_filter_basis.to_filter_basis.filter = ⨅ i, (𝓝 0).comap (p i) :=
begin
  refine le_antisymm (le_infi $ λ i, _) _,
  { rw p.module_filter_basis.to_filter_basis.has_basis.le_basis_iff
      (metric.nhds_basis_ball.comap _),
    intros ε hε,
    refine ⟨(p i).ball 0 ε, _, _⟩,
    { rw ← (finset.sup_singleton : _ = p i),
      exact p.basis_sets_mem {i} hε, },
    { rw [id, (p i).ball_zero_eq_preimage_ball] } },
  { rw p.module_filter_basis.to_filter_basis.has_basis.ge_iff,
    rintros U (hU : U ∈ p.basis_sets),
    rcases p.basis_sets_iff.mp hU with ⟨s, r, hr, rfl⟩,
    rw [id, seminorm.ball_finset_sup_eq_Inter _ _ _ hr, s.Inter_mem_sets],
    exact λ i hi, filter.mem_infi_of_mem i ⟨metric.ball 0 r, metric.ball_mem_nhds 0 hr,
      eq.subset ((p i).ball_zero_eq_preimage_ball).symm⟩, },
end

end seminorm_family

end filter_basis

section bounded

namespace seminorm

variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E]
variables [normed_field 𝕜₂] [add_comm_group F] [module 𝕜₂ F]
variables {σ₁₂ : 𝕜 →+* 𝕜₂} [ring_hom_isometric σ₁₂]

-- Todo: This should be phrased entirely in terms of the von Neumann bornology.

/-- The proposition that a linear map is bounded between spaces with families of seminorms. -/
def is_bounded (p : ι → seminorm 𝕜 E) (q : ι' → seminorm 𝕜₂ F) (f : E →ₛₗ[σ₁₂] F) : Prop :=
  ∀ i, ∃ s : finset ι, ∃ C : ℝ≥0, (q i).comp f ≤ C • s.sup p

lemma is_bounded_const (ι' : Type*) [nonempty ι']
  {p : ι → seminorm 𝕜 E} {q : seminorm 𝕜₂ F} (f : E →ₛₗ[σ₁₂] F) :
  is_bounded p (λ _ : ι', q) f ↔ ∃ (s : finset ι) C : ℝ≥0, q.comp f ≤ C • s.sup p :=
by simp only [is_bounded, forall_const]

lemma const_is_bounded (ι : Type*) [nonempty ι]
  {p : seminorm 𝕜 E} {q : ι' → seminorm 𝕜₂ F} (f : E →ₛₗ[σ₁₂] F) :
  is_bounded (λ _ : ι, p) q f ↔ ∀ i, ∃ C : ℝ≥0, (q i).comp f ≤ C • p :=
begin
  split; intros h i,
  { rcases h i with ⟨s, C, h⟩,
    exact ⟨C, le_trans h (smul_le_smul (finset.sup_le (λ _ _, le_rfl)) le_rfl)⟩ },
  use [{classical.arbitrary ι}],
  simp only [h, finset.sup_singleton],
end

lemma is_bounded_sup {p : ι → seminorm 𝕜 E} {q : ι' → seminorm 𝕜₂ F}
  {f : E →ₛₗ[σ₁₂] F} (hf : is_bounded p q f) (s' : finset ι') :
  ∃ (C : ℝ≥0) (s : finset ι), (s'.sup q).comp f ≤ C • (s.sup p) :=
begin
  classical,
  obtain rfl | hs' := s'.eq_empty_or_nonempty,
  { exact ⟨1, ∅, by simp [seminorm.bot_eq_zero]⟩ },
  choose fₛ fC hf using hf,
  use [s'.card • s'.sup fC, finset.bUnion s' fₛ],
  have hs : ∀ i : ι', i ∈ s' → (q i).comp f ≤ s'.sup fC • ((finset.bUnion s' fₛ).sup p) :=
  begin
    intros i hi,
    refine (hf i).trans (smul_le_smul _ (finset.le_sup hi)),
    exact finset.sup_mono (finset.subset_bUnion_of_mem fₛ hi),
  end,
  refine (comp_mono f (finset_sup_le_sum q s')).trans _,
  simp_rw [←pullback_apply, add_monoid_hom.map_sum, pullback_apply],
  refine (finset.sum_le_sum hs).trans _,
  rw [finset.sum_const, smul_assoc],
  exact le_rfl,
end

end seminorm

end bounded

section topology

variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E] [nonempty ι]

/-- The proposition that the topology of `E` is induced by a family of seminorms `p`. -/
structure with_seminorms (p : seminorm_family 𝕜 E ι) [t : topological_space E] : Prop :=
(topology_eq_with_seminorms : t = p.module_filter_basis.topology)

lemma with_seminorms.with_seminorms_eq {p : seminorm_family 𝕜 E ι} [t : topological_space E]
  (hp : with_seminorms p) : t = p.module_filter_basis.topology := hp.1

variables [topological_space E]
variables {p : seminorm_family 𝕜 E ι}

lemma with_seminorms.topological_add_group (hp : with_seminorms p) : topological_add_group E :=
begin
  rw hp.with_seminorms_eq,
  exact add_group_filter_basis.is_topological_add_group _
end

lemma with_seminorms.has_basis (hp : with_seminorms p) : (𝓝 (0 : E)).has_basis
  (λ (s : set E), s ∈ p.basis_sets) id :=
begin
  rw (congr_fun (congr_arg (@nhds E) hp.1) 0),
  exact add_group_filter_basis.nhds_zero_has_basis _,
end

lemma with_seminorms.has_basis_zero_ball (hp : with_seminorms p) : (𝓝 (0 : E)).has_basis
  (λ sr : finset ι × ℝ, 0 < sr.2) (λ sr, (sr.1.sup p).ball 0 sr.2) :=
begin
  refine ⟨λ V, _⟩,
  simp only [hp.has_basis.mem_iff, seminorm_family.basis_sets_iff, prod.exists],
  split,
  { rintros ⟨-, ⟨s, r, hr, rfl⟩, hV⟩,
    exact ⟨s, r, hr, hV⟩ },
  { rintros ⟨s, r, hr, hV⟩,
    exact ⟨_, ⟨s, r, hr, rfl⟩, hV⟩ }
end

lemma with_seminorms.has_basis_ball (hp : with_seminorms p) {x : E} : (𝓝 (x : E)).has_basis
  (λ sr : finset ι × ℝ, 0 < sr.2) (λ sr, (sr.1.sup p).ball x sr.2) :=
begin
  haveI : topological_add_group E := hp.topological_add_group,
  rw [← map_add_left_nhds_zero],
  convert (hp.has_basis_zero_ball.map ((+) x)),
  ext sr : 1,
  have : (sr.fst.sup p).ball (x +ᵥ 0) sr.snd = x +ᵥ (sr.fst.sup p).ball 0 sr.snd
    := eq.symm (seminorm.vadd_ball (sr.fst.sup p)),
  rwa [vadd_eq_add, add_zero] at this,
end

/-- The `x`-neighbourhoods of a space whose topology is induced by a family of seminorms
are exactly the sets which contain seminorm balls around `x`.-/
lemma with_seminorms.mem_nhds_iff (hp : with_seminorms p) (x : E) (U : set E) :
  U ∈ nhds x ↔ ∃ (s : finset ι) (r > 0), (s.sup p).ball x r ⊆ U :=
by rw [hp.has_basis_ball.mem_iff, prod.exists]

/-- The open sets of a space whose topology is induced by a family of seminorms
are exactly the sets which contain seminorm balls around all of their points.-/
lemma with_seminorms.is_open_iff_mem_balls (hp : with_seminorms p) (U : set E) :
  is_open U ↔ ∀ x ∈ U, ∃ (s : finset ι) (r > 0), (s.sup p).ball x r ⊆ U :=
by simp_rw [←with_seminorms.mem_nhds_iff hp _ U, is_open_iff_mem_nhds]

/- Note that through the following lemmas, one also immediately has that separating families
of seminorms induce T₂ and T₃ topologies by `topological_add_group.t2_space`
and `topological_add_group.t3_space` -/
/-- A separating family of seminorms induces a T₁ topology. -/
lemma with_seminorms.t1_of_separating (hp : with_seminorms p) (h : ∀ x ≠ 0, ∃ i, p i x ≠ 0) :
  t1_space E :=
begin
  haveI := hp.topological_add_group,
  refine topological_add_group.t1_space _ _,
  rw [← is_open_compl_iff, hp.is_open_iff_mem_balls],
  rintros x (hx : x ≠ 0),
  cases h x hx with i pi_nonzero,
  refine ⟨{i}, p i x, by positivity, subset_compl_singleton_iff.mpr _⟩,
  rw [finset.sup_singleton, mem_ball, zero_sub, map_neg_eq_map, not_lt]
end

/-- A family of seminorms inducing a T₁ topology is separating. -/
lemma with_seminorms.separating_of_t1 [t1_space E] (hp : with_seminorms p) (x : E) (hx : x ≠ 0) :
  ∃ i, p i x ≠ 0 :=
begin
  have := ((t1_space_tfae E).out 0 9).mp infer_instance,
  by_contra' h,
  refine hx (this _),
  rw hp.has_basis_zero_ball.specializes_iff,
  rintros ⟨s, r⟩ (hr : 0 < r),
  simp only [ball_finset_sup_eq_Inter _ _ _ hr, mem_Inter₂, mem_ball_zero, h, hr, forall_true_iff],
end

/-- A family of seminorms is separating iff it induces a T₁ topology. -/
lemma with_seminorms.separating_iff_t1 (hp : with_seminorms p) :
  (∀ x ≠ 0, ∃ i, p i x ≠ 0) ↔ t1_space E :=
begin
  refine ⟨with_seminorms.t1_of_separating hp, _⟩,
  introI,
  exact with_seminorms.separating_of_t1 hp,
end

end topology

section tendsto

variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E] [nonempty ι] [topological_space E]
variables {p : seminorm_family 𝕜 E ι}

/-- Convergence along filters for `with_seminorms`.

Variant with `finset.sup`. -/
lemma with_seminorms.tendsto_nhds' (hp : with_seminorms p) (u : F → E) {f : filter F} (y₀ : E) :
  filter.tendsto u f (𝓝 y₀) ↔ ∀ (s : finset ι) ε, 0 < ε → ∀ᶠ x in f, s.sup p (u x - y₀) < ε :=
by simp [hp.has_basis_ball.tendsto_right_iff]

/-- Convergence along filters for `with_seminorms`. -/
lemma with_seminorms.tendsto_nhds (hp : with_seminorms p) (u : F → E) {f : filter F} (y₀ : E) :
  filter.tendsto u f (𝓝 y₀) ↔ ∀ i ε, 0 < ε → ∀ᶠ x in f, p i (u x - y₀) < ε :=
begin
  rw hp.tendsto_nhds' u y₀,
  exact ⟨λ h i, by simpa only [finset.sup_singleton] using h {i},
    λ h s ε hε, (s.eventually_all.2 $ λ i _, h i ε hε).mono (λ _, finset_sup_apply_lt hε)⟩,
end

variables [semilattice_sup F] [nonempty F]

/-- Limit `→ ∞` for `with_seminorms`. -/
lemma with_seminorms.tendsto_nhds_at_top (hp : with_seminorms p) (u : F → E) (y₀ : E) :
  filter.tendsto u filter.at_top (𝓝 y₀) ↔ ∀ i ε, 0 < ε → ∃ x₀, ∀ x, x₀ ≤ x → p i (u x - y₀) < ε :=
begin
  rw hp.tendsto_nhds u y₀,
  exact forall₃_congr (λ _ _ _, filter.eventually_at_top),
end

end tendsto

section topological_add_group

variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E]
variables [t : topological_space E] [topological_add_group E]
variables [nonempty ι]

include t

lemma seminorm_family.with_seminorms_of_nhds (p : seminorm_family 𝕜 E ι)
  (h : 𝓝 (0 : E) = p.module_filter_basis.to_filter_basis.filter) :
  with_seminorms p :=
begin
  refine ⟨topological_add_group.ext infer_instance
    (p.add_group_filter_basis.is_topological_add_group) _⟩,
  rw add_group_filter_basis.nhds_zero_eq,
  exact h,
end

lemma seminorm_family.with_seminorms_of_has_basis (p : seminorm_family 𝕜 E ι)
  (h : (𝓝 (0 : E)).has_basis (λ (s : set E), s ∈ p.basis_sets) id) :
  with_seminorms p :=
p.with_seminorms_of_nhds $ filter.has_basis.eq_of_same_basis h
  p.add_group_filter_basis.to_filter_basis.has_basis

lemma seminorm_family.with_seminorms_iff_nhds_eq_infi (p : seminorm_family 𝕜 E ι) :
  with_seminorms p ↔ (𝓝 0 : filter E) = ⨅ i, (𝓝 0).comap (p i) :=
begin
  rw ← p.filter_eq_infi,
  refine ⟨λ h, _, p.with_seminorms_of_nhds⟩,
  rw h.topology_eq_with_seminorms,
  exact add_group_filter_basis.nhds_zero_eq _,
end

lemma with_seminorms.continuous_seminorm [nontrivially_normed_field 𝕝]
  [module 𝕝 E] [has_continuous_const_smul 𝕝 E] {p : seminorm_family 𝕝 E ι} (hp : with_seminorms p)
  (i : ι) : continuous (p i) :=
begin
  refine seminorm.continuous one_pos _,
  rw [p.with_seminorms_iff_nhds_eq_infi.mp hp, ball_zero_eq_preimage_ball],
  exact filter.mem_infi_of_mem i (filter.preimage_mem_comap $ metric.ball_mem_nhds _ one_pos)
end

/-- The topology induced by a family of seminorms is exactly the infimum of the ones induced by
each seminorm individually. We express this as a characterization of `with_seminorms p`. -/
lemma seminorm_family.with_seminorms_iff_topological_space_eq_infi (p : seminorm_family 𝕜 E ι) :
  with_seminorms p ↔ t = ⨅ i, (p i).to_add_group_seminorm.to_seminormed_add_comm_group
    .to_uniform_space.to_topological_space :=
begin
  rw [p.with_seminorms_iff_nhds_eq_infi, topological_add_group.ext_iff infer_instance
        (topological_add_group_infi $ λ i, infer_instance), nhds_infi],
  congrm (_ = ⨅ i, _),
  exact @comap_norm_nhds_zero _ (p i).to_add_group_seminorm.to_seminormed_add_group,
  all_goals {apply_instance}
end

omit t

/-- The uniform structure induced by a family of seminorms is exactly the infimum of the ones
induced by each seminorm individually. We express this as a characterization of
`with_seminorms p`. -/
lemma seminorm_family.with_seminorms_iff_uniform_space_eq_infi [u : uniform_space E]
  [uniform_add_group E] (p : seminorm_family 𝕜 E ι) :
  with_seminorms p ↔ u = ⨅ i, (p i).to_add_group_seminorm.to_seminormed_add_comm_group
    .to_uniform_space :=
begin
  rw [p.with_seminorms_iff_nhds_eq_infi, uniform_add_group.ext_iff infer_instance
        (uniform_add_group_infi $ λ i, infer_instance), to_topological_space_infi, nhds_infi],
  congrm (_ = ⨅ i, _),
  exact @comap_norm_nhds_zero _ (p i).to_add_group_seminorm.to_seminormed_add_group,
  all_goals {apply_instance}
end

end topological_add_group

section normed_space

/-- The topology of a `normed_space 𝕜 E` is induced by the seminorm `norm_seminorm 𝕜 E`. -/
lemma norm_with_seminorms (𝕜 E) [normed_field 𝕜] [seminormed_add_comm_group E] [normed_space 𝕜 E] :
  with_seminorms (λ (_ : fin 1), norm_seminorm 𝕜 E) :=
begin
  let p : seminorm_family 𝕜 E (fin 1) := λ _, norm_seminorm 𝕜 E,
  refine ⟨seminormed_add_comm_group.to_topological_add_group.ext
    p.add_group_filter_basis.is_topological_add_group _⟩,
  refine filter.has_basis.eq_of_same_basis metric.nhds_basis_ball _,
  rw ←ball_norm_seminorm 𝕜 E,
  refine filter.has_basis.to_has_basis p.add_group_filter_basis.nhds_zero_has_basis _
    (λ r hr, ⟨(norm_seminorm 𝕜 E).ball 0 r, p.basis_sets_singleton_mem 0 hr, rfl.subset⟩),
  rintros U (hU : U ∈ p.basis_sets),
  rcases p.basis_sets_iff.mp hU with ⟨s, r, hr, hU⟩,
  use [r, hr],
  rw [hU, id.def],
  by_cases h : s.nonempty,
  { rw finset.sup_const h },
  rw [finset.not_nonempty_iff_eq_empty.mp h, finset.sup_empty, ball_bot _ hr],
  exact set.subset_univ _,
end

end normed_space

section nontrivially_normed_field

variables [nontrivially_normed_field 𝕜] [add_comm_group E] [module 𝕜 E] [nonempty ι]
variables {p : seminorm_family 𝕜 E ι}
variables [topological_space E]

lemma with_seminorms.is_vonN_bounded_iff_finset_seminorm_bounded {s : set E}
  (hp : with_seminorms p) :
  bornology.is_vonN_bounded 𝕜 s ↔ ∀ I : finset ι, ∃ r (hr : 0 < r), ∀ (x ∈ s), I.sup p x < r :=
begin
  rw (hp.has_basis).is_vonN_bounded_basis_iff,
  split,
  { intros h I,
    simp only [id.def] at h,
    specialize h ((I.sup p).ball 0 1) (p.basis_sets_mem I zero_lt_one),
    rcases h with ⟨r, hr, h⟩,
    cases normed_field.exists_lt_norm 𝕜 r with a ha,
    specialize h a (le_of_lt ha),
    rw [seminorm.smul_ball_zero (norm_pos_iff.1 $ hr.trans ha), mul_one] at h,
    refine ⟨‖a‖, lt_trans hr ha, _⟩,
    intros x hx,
    specialize h hx,
    exact (finset.sup I p).mem_ball_zero.mp h },
  intros h s' hs',
  rcases p.basis_sets_iff.mp hs' with ⟨I, r, hr, hs'⟩,
  rw [id.def, hs'],
  rcases h I with ⟨r', hr', h'⟩,
  simp_rw ←(I.sup p).mem_ball_zero at h',
  refine absorbs.mono_right _ h',
  exact (finset.sup I p).ball_zero_absorbs_ball_zero hr,
end

lemma with_seminorms.image_is_vonN_bounded_iff_finset_seminorm_bounded (f : G → E) {s : set G}
  (hp : with_seminorms p) : bornology.is_vonN_bounded 𝕜 (f '' s) ↔
  ∀ I : finset ι, ∃ r (hr : 0 < r), ∀ (x ∈ s), I.sup p (f x) < r :=
by simp_rw [hp.is_vonN_bounded_iff_finset_seminorm_bounded, set.ball_image_iff]

lemma with_seminorms.is_vonN_bounded_iff_seminorm_bounded {s : set E} (hp : with_seminorms p) :
  bornology.is_vonN_bounded 𝕜 s ↔ ∀ i : ι, ∃ r (hr : 0 < r), ∀ (x ∈ s), p i x < r :=
begin
  rw hp.is_vonN_bounded_iff_finset_seminorm_bounded,
  split,
  { intros hI i,
    convert hI {i},
    rw [finset.sup_singleton] },
  intros hi I,
  by_cases hI : I.nonempty,
  { choose r hr h using hi,
    have h' : 0 < I.sup' hI r :=
    by { rcases hI.bex with ⟨i, hi⟩, exact lt_of_lt_of_le (hr i) (finset.le_sup' r hi) },
    refine ⟨I.sup' hI r, h', λ x hx, finset_sup_apply_lt h' (λ i hi, _)⟩,
    refine lt_of_lt_of_le (h i x hx) _,
    simp only [finset.le_sup'_iff, exists_prop],
    exact ⟨i, hi, (eq.refl _).le⟩ },
  simp only [finset.not_nonempty_iff_eq_empty.mp hI, finset.sup_empty, coe_bot, pi.zero_apply,
    exists_prop],
  exact ⟨1, zero_lt_one, λ _ _, zero_lt_one⟩,
end

lemma with_seminorms.image_is_vonN_bounded_iff_seminorm_bounded (f : G → E) {s : set G}
  (hp : with_seminorms p) :
  bornology.is_vonN_bounded 𝕜 (f '' s) ↔ ∀ i : ι, ∃ r (hr : 0 < r), ∀ (x ∈ s), p i (f x) < r :=
by simp_rw [hp.is_vonN_bounded_iff_seminorm_bounded, set.ball_image_iff]

end nontrivially_normed_field
section continuous_bounded

namespace seminorm

variables [nontrivially_normed_field 𝕜] [add_comm_group E] [module 𝕜 E]
variables [normed_field 𝕝] [module 𝕝 E]
variables [nontrivially_normed_field 𝕜₂] [add_comm_group F] [module 𝕜₂ F]
variables [normed_field 𝕝₂] [module 𝕝₂ F]
variables {σ₁₂ : 𝕜 →+* 𝕜₂} [ring_hom_isometric σ₁₂]
variables {τ₁₂ : 𝕝 →+* 𝕝₂} [ring_hom_isometric τ₁₂]
variables [nonempty ι] [nonempty ι']

lemma continuous_of_continuous_comp {q : seminorm_family 𝕝₂ F ι'}
  [topological_space E] [topological_add_group E]
  [topological_space F] [topological_add_group F] (hq : with_seminorms q)
  (f : E →ₛₗ[τ₁₂] F) (hf : ∀ i, continuous ((q i).comp f)) : continuous f :=
begin
  refine continuous_of_continuous_at_zero f _,
  simp_rw [continuous_at, f.map_zero, q.with_seminorms_iff_nhds_eq_infi.mp hq, filter.tendsto_infi,
            filter.tendsto_comap_iff],
  intros i,
  convert (hf i).continuous_at,
  exact (map_zero _).symm
end

lemma continuous_iff_continuous_comp
  {q : seminorm_family 𝕜₂ F ι'} [topological_space E] [topological_add_group E]
  [topological_space F] [topological_add_group F] [has_continuous_const_smul 𝕜₂ F]
  (hq : with_seminorms q) (f : E →ₛₗ[σ₁₂] F) :
  continuous f ↔ ∀ i, continuous ((q i).comp f) :=
⟨λ h i, continuous.comp (hq.continuous_seminorm i) h, continuous_of_continuous_comp hq f⟩

lemma continuous_from_bounded {p : seminorm_family 𝕝 E ι} {q : seminorm_family 𝕝₂ F ι'}
  [topological_space E] [topological_add_group E] (hp : with_seminorms p)
  [topological_space F] [topological_add_group F] (hq : with_seminorms q)
  (f : E →ₛₗ[τ₁₂] F) (hf : seminorm.is_bounded p q f) : continuous f :=
begin
  refine continuous_of_continuous_comp hq _ (λ i, seminorm.continuous_of_continuous_at_zero _),
  rw [metric.continuous_at_iff', map_zero],
  intros r hr,
  rcases hf i with ⟨s₁, C, hf⟩,
  have hC' : 0 < C + 1 := by positivity,
  rw hp.has_basis.eventually_iff,
  refine ⟨(s₁.sup p).ball 0 (r/(C + 1)), p.basis_sets_mem _ (by positivity), _⟩,
  simp_rw [ ←metric.mem_ball, ←mem_preimage, ←ball_zero_eq_preimage_ball],
  refine subset.trans _ (ball_antitone hf),
  norm_cast,
  rw ← ball_smul (s₁.sup p) hC',
  refine ball_antitone (smul_le_smul le_rfl _),
  simp only [le_add_iff_nonneg_right, zero_le'],
end

lemma cont_with_seminorms_normed_space (F) [seminormed_add_comm_group F] [normed_space 𝕝₂ F]
  [uniform_space E] [uniform_add_group E]
  {p : ι → seminorm 𝕝 E} (hp : with_seminorms p) (f : E →ₛₗ[τ₁₂] F)
  (hf : ∃ (s : finset ι) C : ℝ≥0, (norm_seminorm 𝕝₂ F).comp f ≤ C • s.sup p) :
  continuous f :=
begin
  rw ←seminorm.is_bounded_const (fin 1) at hf,
  exact continuous_from_bounded hp (norm_with_seminorms 𝕝₂ F) f hf,
end

lemma cont_normed_space_to_with_seminorms (E) [seminormed_add_comm_group E] [normed_space 𝕝 E]
  [uniform_space F] [uniform_add_group F]
  {q : ι → seminorm 𝕝₂ F} (hq : with_seminorms q) (f : E →ₛₗ[τ₁₂] F)
  (hf : ∀ i : ι, ∃ C : ℝ≥0, (q i).comp f ≤ C • (norm_seminorm 𝕝 E)) : continuous f :=
begin
  rw ←seminorm.const_is_bounded (fin 1) at hf,
  exact continuous_from_bounded (norm_with_seminorms 𝕝 E) hq f hf,
end

end seminorm

end continuous_bounded

section locally_convex_space

open locally_convex_space

variables [nonempty ι] [normed_field 𝕜] [normed_space ℝ 𝕜]
  [add_comm_group E] [module 𝕜 E] [module ℝ E] [is_scalar_tower ℝ 𝕜 E] [topological_space E]
  [topological_add_group E]

lemma with_seminorms.to_locally_convex_space {p : seminorm_family 𝕜 E ι} (hp : with_seminorms p) :
  locally_convex_space ℝ E :=
begin
  apply of_basis_zero ℝ E id (λ s, s ∈ p.basis_sets),
  { rw [hp.1, add_group_filter_basis.nhds_eq _, add_group_filter_basis.N_zero],
    exact filter_basis.has_basis _ },
  { intros s hs,
    change s ∈ set.Union _ at hs,
    simp_rw [set.mem_Union, set.mem_singleton_iff] at hs,
    rcases hs with ⟨I, r, hr, rfl⟩,
    exact convex_ball _ _ _ }
end

end locally_convex_space

section normed_space

variables (𝕜) [normed_field 𝕜] [normed_space ℝ 𝕜] [seminormed_add_comm_group E]

/-- Not an instance since `𝕜` can't be inferred. See `normed_space.to_locally_convex_space` for a
slightly weaker instance version. -/
lemma normed_space.to_locally_convex_space' [normed_space 𝕜 E] [module ℝ E]
  [is_scalar_tower ℝ 𝕜 E] : locally_convex_space ℝ E :=
(norm_with_seminorms 𝕜 E).to_locally_convex_space

/-- See `normed_space.to_locally_convex_space'` for a slightly stronger version which is not an
instance. -/
instance normed_space.to_locally_convex_space [normed_space ℝ E] :
  locally_convex_space ℝ E :=
normed_space.to_locally_convex_space' ℝ

end normed_space

section topological_constructions

variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E]
variables [normed_field 𝕜₂] [add_comm_group F] [module 𝕜₂ F]
variables {σ₁₂ : 𝕜 →+* 𝕜₂} [ring_hom_isometric σ₁₂]

/-- The family of seminorms obtained by composing each seminorm by a linear map. -/
def seminorm_family.comp (q : seminorm_family 𝕜₂ F ι) (f : E →ₛₗ[σ₁₂] F) :
  seminorm_family 𝕜 E ι :=
λ i, (q i).comp f

lemma seminorm_family.comp_apply (q : seminorm_family 𝕜₂ F ι) (i : ι) (f : E →ₛₗ[σ₁₂] F) :
  q.comp f i = (q i).comp f :=
rfl

lemma seminorm_family.finset_sup_comp (q : seminorm_family 𝕜₂ F ι) (s : finset ι)
  (f : E →ₛₗ[σ₁₂] F) : (s.sup q).comp f = s.sup (q.comp f) :=
begin
  ext x,
  rw [seminorm.comp_apply, seminorm.finset_sup_apply, seminorm.finset_sup_apply],
  refl
end

variables [topological_space F] [topological_add_group F]

lemma linear_map.with_seminorms_induced [hι : nonempty ι] {q : seminorm_family 𝕜₂ F ι}
  (hq : with_seminorms q) (f : E →ₛₗ[σ₁₂] F) :
  @with_seminorms 𝕜 E ι _ _ _ _ (q.comp f) (induced f infer_instance) :=
begin
  letI : topological_space E := induced f infer_instance,
  letI : topological_add_group E := topological_add_group_induced f,
  rw [(q.comp f).with_seminorms_iff_nhds_eq_infi, nhds_induced, map_zero,
      q.with_seminorms_iff_nhds_eq_infi.mp hq, filter.comap_infi],
  refine infi_congr (λ i, _),
  exact filter.comap_comap
end

lemma inducing.with_seminorms [hι : nonempty ι] {q : seminorm_family 𝕜₂ F ι}
  (hq : with_seminorms q) [topological_space E] {f : E →ₛₗ[σ₁₂] F} (hf : inducing f) :
  with_seminorms (q.comp f) :=
begin
  rw hf.induced,
  exact f.with_seminorms_induced hq
end

end topological_constructions

section topological_properties

variables [nontrivially_normed_field 𝕜] [add_comm_group E] [module 𝕜 E] [nonempty ι] [countable ι]
variables {p : seminorm_family 𝕜 E ι}
variables [uniform_space E] [uniform_add_group E]

/-- If the topology of a space is induced by a countable family of seminorms, then the topology
is first countable. -/
lemma with_seminorms.first_countable (hp : with_seminorms p) :
  topological_space.first_countable_topology E :=
begin
  haveI : (𝓝 (0 : E)).is_countably_generated,
  { rw p.with_seminorms_iff_nhds_eq_infi.mp hp,
    exact filter.infi.is_countably_generated _ },
  haveI : (uniformity E).is_countably_generated := uniform_add_group.uniformity_countably_generated,
  exact uniform_space.first_countable_topology E,
end

end topological_properties
