/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import analysis.locally_convex.basic
import analysis.locally_convex.balanced_core_hull
import analysis.seminorm
import topology.bornology.basic
import topology.algebra.uniform_group
import topology.uniform_space.cauchy

/-!
# Von Neumann Boundedness

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines natural or von Neumann bounded sets and proves elementary properties.

## Main declarations

* `bornology.is_vonN_bounded`: A set `s` is von Neumann-bounded if every neighborhood of zero
absorbs `s`.
* `bornology.vonN_bornology`: The bornology made of the von Neumann-bounded sets.

## Main results

* `bornology.is_vonN_bounded.of_topological_space_le`: A coarser topology admits more
von Neumann-bounded sets.
* `bornology.is_vonN_bounded.image`: A continuous linear image of a bounded set is bounded.
* `bornology.is_vonN_bounded_iff_smul_tendsto_zero`: Given any sequence `ε` of scalars which tends
  to `𝓝[≠] 0`, we have that a set `S` is bounded if and only if for any sequence `x : ℕ → S`,
  `ε • x` tends to 0. This shows that bounded sets are completely determined by sequences, which is
  the key fact for proving that sequential continuity implies continuity for linear maps defined on
  a bornological space

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

-/

variables {𝕜 𝕜' E E' F ι : Type*}

open set filter
open_locale topology pointwise

namespace bornology

section semi_normed_ring

section has_zero

variables (𝕜)
variables [semi_normed_ring 𝕜] [has_smul 𝕜 E] [has_zero E]
variables [topological_space E]

/-- A set `s` is von Neumann bounded if every neighborhood of 0 absorbs `s`. -/
def is_vonN_bounded (s : set E) : Prop := ∀ ⦃V⦄, V ∈ 𝓝 (0 : E) → absorbs 𝕜 V s

variables (E)

@[simp] lemma is_vonN_bounded_empty : is_vonN_bounded 𝕜 (∅ : set E) :=
λ _ _, absorbs_empty

variables {𝕜 E}

lemma is_vonN_bounded_iff (s : set E) : is_vonN_bounded 𝕜 s ↔ ∀ V ∈ 𝓝 (0 : E), absorbs 𝕜 V s :=
iff.rfl

lemma _root_.filter.has_basis.is_vonN_bounded_basis_iff {q : ι → Prop} {s : ι → set E} {A : set E}
  (h : (𝓝 (0 : E)).has_basis q s) :
  is_vonN_bounded 𝕜 A ↔ ∀ i (hi : q i), absorbs 𝕜 (s i) A :=
begin
  refine ⟨λ hA i hi, hA (h.mem_of_mem hi), λ hA V hV, _⟩,
  rcases h.mem_iff.mp hV with ⟨i, hi, hV⟩,
  exact (hA i hi).mono_left hV,
end

/-- Subsets of bounded sets are bounded. -/
lemma is_vonN_bounded.subset {s₁ s₂ : set E} (h : s₁ ⊆ s₂) (hs₂ : is_vonN_bounded 𝕜 s₂) :
  is_vonN_bounded 𝕜 s₁ :=
λ V hV, (hs₂ hV).mono_right h

/-- The union of two bounded sets is bounded. -/
lemma is_vonN_bounded.union {s₁ s₂ : set E} (hs₁ : is_vonN_bounded 𝕜 s₁)
  (hs₂ : is_vonN_bounded 𝕜 s₂) :
  is_vonN_bounded 𝕜 (s₁ ∪ s₂) :=
λ V hV, (hs₁ hV).union (hs₂ hV)

end has_zero

end semi_normed_ring

section multiple_topologies

variables [semi_normed_ring 𝕜] [add_comm_group E] [module 𝕜 E]

/-- If a topology `t'` is coarser than `t`, then any set `s` that is bounded with respect to
`t` is bounded with respect to `t'`. -/
lemma is_vonN_bounded.of_topological_space_le {t t' : topological_space E} (h : t ≤ t') {s : set E}
  (hs : @is_vonN_bounded 𝕜 E _ _ _ t s) : @is_vonN_bounded 𝕜 E _ _ _ t' s :=
λ V hV, hs $ (le_iff_nhds t t').mp h 0 hV

end multiple_topologies

section image

variables {𝕜₁ 𝕜₂ : Type*} [normed_division_ring 𝕜₁] [normed_division_ring 𝕜₂]
  [add_comm_group E] [module 𝕜₁ E] [add_comm_group F] [module 𝕜₂ F]
  [topological_space E] [topological_space F]

/-- A continuous linear image of a bounded set is bounded. -/
lemma is_vonN_bounded.image {σ : 𝕜₁ →+* 𝕜₂} [ring_hom_surjective σ] [ring_hom_isometric σ]
  {s : set E} (hs : is_vonN_bounded 𝕜₁ s) (f : E →SL[σ] F) :
  is_vonN_bounded 𝕜₂ (f '' s) :=
begin
  let σ' := ring_equiv.of_bijective σ ⟨σ.injective, σ.is_surjective⟩,
  have σ_iso : isometry σ := add_monoid_hom_class.isometry_of_norm σ
    (λ x, ring_hom_isometric.is_iso),
  have σ'_symm_iso : isometry σ'.symm := σ_iso.right_inv σ'.right_inv,
  have f_tendsto_zero := f.continuous.tendsto 0,
  rw map_zero at f_tendsto_zero,
  intros V hV,
  rcases hs (f_tendsto_zero hV) with ⟨r, hrpos, hr⟩,
  refine ⟨r, hrpos, λ a ha, _⟩,
  rw ← σ'.apply_symm_apply a,
  have hanz : a ≠ 0 := norm_pos_iff.mp (hrpos.trans_le ha),
  have : σ'.symm a ≠ 0 := (map_ne_zero σ'.symm.to_ring_hom).mpr hanz,
  change _ ⊆ σ _ • _,
  rw [set.image_subset_iff, preimage_smul_setₛₗ _ _ _ f this.is_unit],
  refine hr (σ'.symm a) _,
  rwa σ'_symm_iso.norm_map_of_map_zero (map_zero _)
end

end image

section sequence

variables {𝕝 : Type*} [normed_field 𝕜] [nontrivially_normed_field 𝕝] [add_comm_group E] [module 𝕜 E]
  [module 𝕝 E] [topological_space E] [has_continuous_smul 𝕝 E]

lemma is_vonN_bounded.smul_tendsto_zero {S : set E} {ε : ι → 𝕜} {x : ι → E} {l : filter ι}
  (hS : is_vonN_bounded 𝕜 S) (hxS : ∀ᶠ n in l, x n ∈ S) (hε : tendsto ε l (𝓝 0)) :
  tendsto (ε • x) l (𝓝 0) :=
begin
  rw tendsto_def at *,
  intros V hV,
  rcases hS hV with ⟨r, r_pos, hrS⟩,
  filter_upwards [hxS, hε _ (metric.ball_mem_nhds 0 $ inv_pos.mpr r_pos)] with n hnS hnr,
  by_cases this : ε n = 0,
  { simp [this, mem_of_mem_nhds hV] },
  { rw [mem_preimage, mem_ball_zero_iff, lt_inv (norm_pos_iff.mpr this) r_pos, ← norm_inv] at hnr,
    rw [mem_preimage, pi.smul_apply', ← set.mem_inv_smul_set_iff₀ this],
    exact hrS _ (hnr.le) hnS },
end

lemma is_vonN_bounded_of_smul_tendsto_zero {ε : ι → 𝕝} {l : filter ι} [l.ne_bot]
  (hε : ∀ᶠ n in l, ε n ≠ 0) {S : set E}
  (H : ∀ x : ι → E, (∀ n, x n ∈ S) → tendsto (ε • x) l (𝓝 0)) :
  is_vonN_bounded 𝕝 S :=
begin
  rw (nhds_basis_balanced 𝕝 E).is_vonN_bounded_basis_iff,
  by_contra' H',
  rcases H' with ⟨V, ⟨hV, hVb⟩, hVS⟩,
  have : ∀ᶠ n in l, ∃ x : S, (ε n) • (x : E) ∉ V,
  { filter_upwards [hε] with n hn,
    rw absorbs at hVS,
    push_neg at hVS,
    rcases hVS _ (norm_pos_iff.mpr $ inv_ne_zero hn) with ⟨a, haε, haS⟩,
    rcases set.not_subset.mp haS with ⟨x, hxS, hx⟩,
    refine ⟨⟨x, hxS⟩, λ hnx, _⟩,
    rw ← set.mem_inv_smul_set_iff₀ hn at hnx,
    exact hx (hVb.smul_mono haε hnx) },
  rcases this.choice with ⟨x, hx⟩,
  refine filter.frequently_false l (filter.eventually.frequently _),
  filter_upwards [hx, (H (coe ∘ x) (λ n, (x n).2)).eventually (eventually_mem_set.mpr hV)]
    using λ n, id
end

/-- Given any sequence `ε` of scalars which tends to `𝓝[≠] 0`, we have that a set `S` is bounded
  if and only if for any sequence `x : ℕ → S`, `ε • x` tends to 0. This actually works for any
  indexing type `ι`, but in the special case `ι = ℕ` we get the important fact that convergent
  sequences fully characterize bounded sets. -/
lemma is_vonN_bounded_iff_smul_tendsto_zero {ε : ι → 𝕝} {l : filter ι} [l.ne_bot]
  (hε : tendsto ε l (𝓝[≠] 0)) {S : set E} :
  is_vonN_bounded 𝕝 S ↔ ∀ x : ι → E, (∀ n, x n ∈ S) → tendsto (ε • x) l (𝓝 0) :=
⟨λ hS x hxS, hS.smul_tendsto_zero (eventually_of_forall hxS) (le_trans hε nhds_within_le_nhds),
  is_vonN_bounded_of_smul_tendsto_zero (hε self_mem_nhds_within)⟩

end sequence

section normed_field

variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E]
variables [topological_space E] [has_continuous_smul 𝕜 E]

/-- Singletons are bounded. -/
lemma is_vonN_bounded_singleton (x : E) : is_vonN_bounded 𝕜 ({x} : set E) :=
λ V hV, (absorbent_nhds_zero hV).absorbs

/-- The union of all bounded set is the whole space. -/
lemma is_vonN_bounded_covers : ⋃₀ (set_of (is_vonN_bounded 𝕜)) = (set.univ : set E) :=
set.eq_univ_iff_forall.mpr (λ x, set.mem_sUnion.mpr
  ⟨{x}, is_vonN_bounded_singleton _, set.mem_singleton _⟩)

variables (𝕜 E)

/-- The von Neumann bornology defined by the von Neumann bounded sets.

Note that this is not registered as an instance, in order to avoid diamonds with the
metric bornology.-/
@[reducible] -- See note [reducible non-instances]
def vonN_bornology : bornology E :=
bornology.of_bounded (set_of (is_vonN_bounded 𝕜)) (is_vonN_bounded_empty 𝕜 E)
  (λ _ hs _ ht, hs.subset ht) (λ _ hs _, hs.union) is_vonN_bounded_singleton

variables {E}

@[simp] lemma is_bounded_iff_is_vonN_bounded {s : set E} :
  @is_bounded _ (vonN_bornology 𝕜 E) s ↔ is_vonN_bounded 𝕜 s :=
is_bounded_of_bounded_iff _

end normed_field

end bornology

section uniform_add_group

variables (𝕜) [nontrivially_normed_field 𝕜] [add_comm_group E] [module 𝕜 E]
variables [uniform_space E] [uniform_add_group E] [has_continuous_smul 𝕜 E]

lemma totally_bounded.is_vonN_bounded {s : set E} (hs : totally_bounded s) :
  bornology.is_vonN_bounded 𝕜 s :=
begin
  rw totally_bounded_iff_subset_finite_Union_nhds_zero at hs,
  intros U hU,
  have h : filter.tendsto (λ (x : E × E), x.fst + x.snd) (𝓝 (0,0)) (𝓝 ((0 : E) + (0 : E))) :=
    tendsto_add,
  rw add_zero at h,
  have h' := (nhds_basis_balanced 𝕜 E).prod (nhds_basis_balanced 𝕜 E),
  simp_rw [←nhds_prod_eq, id.def] at h',
  rcases h.basis_left h' U hU with ⟨x, hx, h''⟩,
  rcases hs x.snd hx.2.1 with ⟨t, ht, hs⟩,
  refine absorbs.mono_right _ hs,
  rw ht.absorbs_Union,
  have hx_fstsnd : x.fst + x.snd ⊆ U,
  { intros z hz,
    rcases set.mem_add.mp hz with ⟨z1, z2, hz1, hz2, hz⟩,
    have hz' : (z1, z2) ∈ x.fst ×ˢ x.snd := ⟨hz1, hz2⟩,
    simpa only [hz] using h'' hz' },
  refine λ y hy, absorbs.mono_left _ hx_fstsnd,
  rw [←set.singleton_vadd, vadd_eq_add],
  exact (absorbent_nhds_zero hx.1.1).absorbs.add hx.2.2.absorbs_self,
end

end uniform_add_group

section vonN_bornology_eq_metric

variables (𝕜 E) [nontrivially_normed_field 𝕜] [seminormed_add_comm_group E] [normed_space 𝕜 E]

namespace normed_space

lemma is_vonN_bounded_ball (r : ℝ) :
  bornology.is_vonN_bounded 𝕜 (metric.ball (0 : E) r) :=
begin
  rw [metric.nhds_basis_ball.is_vonN_bounded_basis_iff, ← ball_norm_seminorm 𝕜 E],
  exact λ ε hε, (norm_seminorm 𝕜 E).ball_zero_absorbs_ball_zero hε
end

lemma is_vonN_bounded_closed_ball (r : ℝ) :
  bornology.is_vonN_bounded 𝕜 (metric.closed_ball (0 : E) r) :=
(is_vonN_bounded_ball 𝕜 E (r+1)).subset (metric.closed_ball_subset_ball $ by linarith)

lemma is_vonN_bounded_iff (s : set E) :
  bornology.is_vonN_bounded 𝕜 s ↔ bornology.is_bounded s :=
begin
  rw [← metric.bounded_iff_is_bounded, metric.bounded_iff_subset_ball (0 : E)],
  split,
  { intros h,
    rcases h (metric.ball_mem_nhds 0 zero_lt_one) with ⟨ρ, hρ, hρball⟩,
    rcases normed_field.exists_lt_norm 𝕜 ρ with ⟨a, ha⟩,
    specialize hρball a ha.le,
    rw [← ball_norm_seminorm 𝕜 E, seminorm.smul_ball_zero (norm_pos_iff.1 $ hρ.trans ha),
        ball_norm_seminorm, mul_one] at hρball,
    exact ⟨‖a‖, hρball.trans metric.ball_subset_closed_ball⟩ },
  { exact λ ⟨C, hC⟩, (is_vonN_bounded_closed_ball 𝕜 E C).subset hC }
end

lemma is_vonN_bounded_iff' (s : set E) :
  bornology.is_vonN_bounded 𝕜 s ↔ ∃ r : ℝ, ∀ (x : E) (hx : x ∈ s), ‖x‖ ≤ r :=
by rw [normed_space.is_vonN_bounded_iff, ←metric.bounded_iff_is_bounded, bounded_iff_forall_norm_le]

lemma image_is_vonN_bounded_iff (f : E' → E) (s : set E') :
  bornology.is_vonN_bounded 𝕜 (f '' s) ↔ ∃ r : ℝ, ∀ (x : E') (hx : x ∈ s), ‖f x‖ ≤ r :=
by simp_rw [is_vonN_bounded_iff', set.ball_image_iff]

/-- In a normed space, the von Neumann bornology (`bornology.vonN_bornology`) is equal to the
metric bornology. -/
lemma vonN_bornology_eq : bornology.vonN_bornology 𝕜 E = pseudo_metric_space.to_bornology :=
begin
  rw bornology.ext_iff_is_bounded,
  intro s,
  rw bornology.is_bounded_iff_is_vonN_bounded,
  exact is_vonN_bounded_iff 𝕜 E s
end

variable (𝕜)

lemma is_bounded_iff_subset_smul_ball {s : set E} :
  bornology.is_bounded s ↔ ∃ a : 𝕜, s ⊆ a • metric.ball 0 1 :=
begin
  rw ← is_vonN_bounded_iff 𝕜,
  split,
  { intros h,
    rcases h (metric.ball_mem_nhds 0 zero_lt_one) with ⟨ρ, hρ, hρball⟩,
    rcases normed_field.exists_lt_norm 𝕜 ρ with ⟨a, ha⟩,
    exact ⟨a, hρball a ha.le⟩ },
  { rintros ⟨a, ha⟩,
    exact ((is_vonN_bounded_ball 𝕜 E 1).image (a • 1 : E →L[𝕜] E)).subset ha }
end

lemma is_bounded_iff_subset_smul_closed_ball {s : set E} :
  bornology.is_bounded s ↔ ∃ a : 𝕜, s ⊆ a • metric.closed_ball 0 1 :=
begin
  split,
  { rw is_bounded_iff_subset_smul_ball 𝕜,
    exact exists_imp_exists
      (λ a ha, ha.trans $ set.smul_set_mono $ metric.ball_subset_closed_ball) },
  { rw ← is_vonN_bounded_iff 𝕜,
    rintros ⟨a, ha⟩,
    exact ((is_vonN_bounded_closed_ball 𝕜 E 1).image (a • 1 : E →L[𝕜] E)).subset ha }
end

end normed_space

end vonN_bornology_eq_metric
