/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import topology.metric_space.basic
import topology.algebra.uniform_group
import topology.algebra.ring
import ring_theory.subring.basic
import group_theory.archimedean
import algebra.periodic
import order.filter.archimedean
import topology.instances.int

/-!
# Topological properties of ℝ
-/

noncomputable theory
open classical filter int metric set topological_space
open_locale classical topological_space filter uniformity interval

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

instance : noncompact_space ℝ := int.closed_embedding_coe_real.noncompact_space

theorem real.uniform_continuous_add : uniform_continuous (λp : ℝ × ℝ, p.1 + p.2) :=
metric.uniform_continuous_iff.2 $ λ ε ε0,
let ⟨δ, δ0, Hδ⟩ := rat_add_continuous_lemma abs ε0 in
⟨δ, δ0, λ a b h, let ⟨h₁, h₂⟩ := max_lt_iff.1 h in Hδ h₁ h₂⟩


theorem real.uniform_continuous_neg : uniform_continuous (@has_neg.neg ℝ _) :=
metric.uniform_continuous_iff.2 $ λ ε ε0, ⟨_, ε0, λ a b h,
  by rw dist_comm at h; simpa [real.dist_eq] using h⟩

instance : uniform_add_group ℝ :=
uniform_add_group.mk' real.uniform_continuous_add real.uniform_continuous_neg

 -- short-circuit type class inference
instance : topological_add_group ℝ := by apply_instance

instance : proper_space ℝ :=
{ is_compact_closed_ball := λx r, by { rw real.closed_ball_eq_Icc, apply is_compact_Icc } }

instance : second_countable_topology ℝ := second_countable_of_proper

lemma real.is_topological_basis_Ioo_rat :
  @is_topological_basis ℝ _ (⋃(a b : ℚ) (h : a < b), {Ioo a b}) :=
is_topological_basis_of_open_of_nhds
  (by simp [is_open_Ioo] {contextual:=tt})
  (assume a v hav hv,
    let ⟨l, u, ⟨hl, hu⟩, h⟩ := mem_nhds_iff_exists_Ioo_subset.mp (is_open.mem_nhds hv hav),
        ⟨q, hlq, hqa⟩ := exists_rat_btwn hl,
        ⟨p, hap, hpu⟩ := exists_rat_btwn hu in
    ⟨Ioo q p,
      by { simp only [mem_Union], exact ⟨q, p, rat.cast_lt.1 $ hqa.trans hap, rfl⟩ },
      ⟨hqa, hap⟩, assume a' ⟨hqa', ha'p⟩, h ⟨hlq.trans hqa', ha'p.trans hpu⟩⟩)

@[simp] lemma real.cocompact_eq : cocompact ℝ = at_bot ⊔ at_top :=
by simp only [← comap_dist_right_at_top_eq_cocompact (0 : ℝ), real.dist_eq, sub_zero,
  comap_abs_at_top]

/- TODO(Mario): Prove that these are uniform isomorphisms instead of uniform embeddings
lemma uniform_embedding_add_rat {r : ℚ} : uniform_embedding (λp:ℚ, p + r) :=
_

lemma uniform_embedding_mul_rat {q : ℚ} (hq : q ≠ 0) : uniform_embedding ((*) q) :=
_ -/

lemma real.mem_closure_iff {s : set ℝ} {x : ℝ} :
  x ∈ closure s ↔ ∀ ε > 0, ∃ y ∈ s, |y - x| < ε :=
by simp [mem_closure_iff_nhds_basis nhds_basis_ball, real.dist_eq]

lemma real.uniform_continuous_inv (s : set ℝ) {r : ℝ} (r0 : 0 < r) (H : ∀ x ∈ s, r ≤ |x|) :
  uniform_continuous (λp:s, p.1⁻¹) :=
metric.uniform_continuous_iff.2 $ λ ε ε0,
let ⟨δ, δ0, Hδ⟩ := rat_inv_continuous_lemma abs ε0 r0 in
⟨δ, δ0, λ a b h, Hδ (H _ a.2) (H _ b.2) h⟩

lemma real.uniform_continuous_abs : uniform_continuous (abs : ℝ → ℝ) :=
metric.uniform_continuous_iff.2 $ λ ε ε0,
  ⟨ε, ε0, λ a b, lt_of_le_of_lt (abs_abs_sub_abs_le_abs_sub _ _)⟩

lemma real.tendsto_inv {r : ℝ} (r0 : r ≠ 0) : tendsto (λq, q⁻¹) (𝓝 r) (𝓝 r⁻¹) :=
by rw ← abs_pos at r0; exact
tendsto_of_uniform_continuous_subtype
  (real.uniform_continuous_inv {x | |r| / 2 < |x|} (half_pos r0) (λ x h, le_of_lt h))
  (is_open.mem_nhds ((is_open_lt' (|r| / 2)).preimage continuous_abs) (half_lt_self r0))

lemma real.continuous_inv : continuous (λa:{r:ℝ // r ≠ 0}, a.val⁻¹) :=
continuous_iff_continuous_at.mpr $ assume ⟨r, hr⟩,
  tendsto.comp (real.tendsto_inv hr) (continuous_iff_continuous_at.mp continuous_subtype_val _)

lemma real.continuous.inv [topological_space α] {f : α → ℝ} (h : ∀a, f a ≠ 0) (hf : continuous f) :
  continuous (λa, (f a)⁻¹) :=
show continuous ((has_inv.inv ∘ @subtype.val ℝ (λr, r ≠ 0)) ∘ λa, ⟨f a, h a⟩),
  from real.continuous_inv.comp (continuous_subtype_mk _ hf)

lemma real.uniform_continuous_mul_const {x : ℝ} : uniform_continuous ((*) x) :=
metric.uniform_continuous_iff.2 $ λ ε ε0, begin
  cases exists_gt (|x|) with y xy,
  have y0 := lt_of_le_of_lt (abs_nonneg _) xy,
  refine ⟨_, div_pos ε0 y0, λ a b h, _⟩,
  rw [real.dist_eq, ← mul_sub, abs_mul, ← mul_div_cancel' ε (ne_of_gt y0)],
  exact mul_lt_mul' (le_of_lt xy) h (abs_nonneg _) y0
end

lemma real.uniform_continuous_mul (s : set (ℝ × ℝ))
  {r₁ r₂ : ℝ} (H : ∀ x ∈ s, |(x : ℝ × ℝ).1| < r₁ ∧ |x.2| < r₂) :
  uniform_continuous (λp:s, p.1.1 * p.1.2) :=
metric.uniform_continuous_iff.2 $ λ ε ε0,
let ⟨δ, δ0, Hδ⟩ := rat_mul_continuous_lemma abs ε0 in
⟨δ, δ0, λ a b h,
  let ⟨h₁, h₂⟩ := max_lt_iff.1 h in Hδ (H _ a.2).1 (H _ b.2).2 h₁ h₂⟩

protected lemma real.continuous_mul : continuous (λp : ℝ × ℝ, p.1 * p.2) :=
continuous_iff_continuous_at.2 $ λ ⟨a₁, a₂⟩,
tendsto_of_uniform_continuous_subtype
  (real.uniform_continuous_mul
    ({x | |x| < |a₁| + 1} ×ˢ {x | |x| < |a₂| + 1})
    (λ x, id))
  (is_open.mem_nhds
    (((is_open_gt' (|a₁| + 1)).preimage continuous_abs).prod
      ((is_open_gt' (|a₂| + 1)).preimage continuous_abs ))
    ⟨lt_add_one (|a₁|), lt_add_one (|a₂|)⟩)

instance : topological_ring ℝ :=
{ continuous_mul := real.continuous_mul, ..real.topological_add_group }

instance : complete_space ℝ :=
begin
  apply complete_of_cauchy_seq_tendsto,
  intros u hu,
  let c : cau_seq ℝ abs := ⟨u, metric.cauchy_seq_iff'.1 hu⟩,
  refine ⟨c.lim, λ s h, _⟩,
  rcases metric.mem_nhds_iff.1 h with ⟨ε, ε0, hε⟩,
  have := c.equiv_lim ε ε0,
  simp only [mem_map, mem_at_top_sets, mem_set_of_eq],
  refine this.imp (λ N hN n hn, hε (hN n hn))
end

lemma real.totally_bounded_ball (x ε : ℝ) : totally_bounded (ball x ε) :=
by rw real.ball_eq_Ioo; apply totally_bounded_Ioo

section

lemma closure_of_rat_image_lt {q : ℚ} : closure ((coe:ℚ → ℝ) '' {x | q < x}) = {r | ↑q ≤ r} :=
subset.antisymm
  ((is_closed_ge' _).closure_subset_iff.2
    (image_subset_iff.2 $ λ p h, le_of_lt $ (@rat.cast_lt ℝ _ _ _).2 h)) $
λ x hx, mem_closure_iff_nhds.2 $ λ t ht,
let ⟨ε, ε0, hε⟩ := metric.mem_nhds_iff.1 ht in
let ⟨p, h₁, h₂⟩ := exists_rat_btwn ((lt_add_iff_pos_right x).2 ε0) in
⟨_, hε (show abs _ < _,
    by rwa [abs_of_nonneg (le_of_lt $ sub_pos.2 h₁), sub_lt_iff_lt_add']),
  p, rat.cast_lt.1 (@lt_of_le_of_lt ℝ _ _ _ _ hx h₁), rfl⟩

/- TODO(Mario): Put these back only if needed later
lemma closure_of_rat_image_le_eq {q : ℚ} : closure ((coe:ℚ → ℝ) '' {x | q ≤ x}) = {r | ↑q ≤ r} :=
_

lemma closure_of_rat_image_le_le_eq {a b : ℚ} (hab : a ≤ b) :
  closure (of_rat '' {q:ℚ | a ≤ q ∧ q ≤ b}) = {r:ℝ | of_rat a ≤ r ∧ r ≤ of_rat b} :=
_-/

lemma real.bounded_iff_bdd_below_bdd_above {s : set ℝ} : bounded s ↔ bdd_below s ∧ bdd_above s :=
⟨begin
  assume bdd,
  rcases (bounded_iff_subset_ball 0).1 bdd with ⟨r, hr⟩, -- hr : s ⊆ closed_ball 0 r
  rw real.closed_ball_eq_Icc at hr, -- hr : s ⊆ Icc (0 - r) (0 + r)
  exact ⟨bdd_below_Icc.mono hr, bdd_above_Icc.mono hr⟩
end,
λ h, bounded_of_bdd_above_of_bdd_below h.2 h.1⟩

lemma real.subset_Icc_Inf_Sup_of_bounded {s : set ℝ} (h : bounded s) :
  s ⊆ Icc (Inf s) (Sup s) :=
subset_Icc_cInf_cSup (real.bounded_iff_bdd_below_bdd_above.1 h).1
  (real.bounded_iff_bdd_below_bdd_above.1 h).2

end

section periodic

namespace function

lemma periodic.compact_of_continuous' [topological_space α] {f : ℝ → α} {c : ℝ}
  (hp : periodic f c) (hc : 0 < c) (hf : continuous f) :
  is_compact (range f) :=
begin
  convert is_compact_Icc.image hf,
  ext x,
  refine ⟨_, mem_range_of_mem_image f (Icc 0 c)⟩,
  rintros ⟨y, h1⟩,
  obtain ⟨z, hz, h2⟩ := hp.exists_mem_Ico₀ hc y,
  exact ⟨z, mem_Icc_of_Ico hz, h2.symm.trans h1⟩,
end

/-- A continuous, periodic function has compact range. -/
lemma periodic.compact_of_continuous [topological_space α] {f : ℝ → α} {c : ℝ}
  (hp : periodic f c) (hc : c ≠ 0) (hf : continuous f) :
  is_compact (range f) :=
begin
  cases lt_or_gt_of_ne hc with hneg hpos,
  exacts [hp.neg.compact_of_continuous' (neg_pos.mpr hneg) hf, hp.compact_of_continuous' hpos hf],
end

/-- A continuous, periodic function is bounded. -/
lemma periodic.bounded_of_continuous [pseudo_metric_space α] {f : ℝ → α} {c : ℝ}
  (hp : periodic f c) (hc : c ≠ 0) (hf : continuous f) :
  bounded (range f) :=
(hp.compact_of_continuous hc hf).bounded

end function

end periodic

section subgroups

/-- Given a nontrivial subgroup `G ⊆ ℝ`, if `G ∩ ℝ_{>0}` has no minimum then `G` is dense. -/
lemma real.subgroup_dense_of_no_min {G : add_subgroup ℝ} {g₀ : ℝ} (g₀_in : g₀ ∈ G) (g₀_ne : g₀ ≠ 0)
  (H' : ¬ ∃ a : ℝ, is_least {g : ℝ | g ∈ G ∧ 0 < g} a) :
  dense (G : set ℝ) :=
begin
  let G_pos := {g : ℝ | g ∈ G ∧ 0 < g},
  push_neg at H',
  intros x,
  suffices : ∀ ε > (0 : ℝ), ∃ g ∈ G, |x - g| < ε,
    by simpa only [real.mem_closure_iff, abs_sub_comm],
  intros ε ε_pos,
  obtain ⟨g₁, g₁_in, g₁_pos⟩ : ∃ g₁ : ℝ, g₁ ∈ G ∧ 0 < g₁,
  { cases lt_or_gt_of_ne g₀_ne with Hg₀ Hg₀,
    { exact ⟨-g₀, G.neg_mem g₀_in, neg_pos.mpr Hg₀⟩ },
    { exact ⟨g₀, g₀_in, Hg₀⟩ } },
  obtain ⟨a, ha⟩ : ∃ a, is_glb G_pos a :=
    ⟨Inf G_pos, is_glb_cInf ⟨g₁, g₁_in, g₁_pos⟩ ⟨0, λ _ hx, le_of_lt hx.2⟩⟩,
  have a_notin : a ∉ G_pos,
  { intros H,
    exact H' a ⟨H, ha.1⟩ },
  obtain ⟨g₂, g₂_in, g₂_pos, g₂_lt⟩ : ∃ g₂ : ℝ, g₂ ∈ G ∧ 0 < g₂ ∧ g₂ < ε,
  { obtain ⟨b, hb, hb', hb''⟩ := ha.exists_between_self_add' a_notin ε_pos,
    obtain ⟨c, hc, hc', hc''⟩ := ha.exists_between_self_add' a_notin (sub_pos.2 hb'),
    refine ⟨b - c, G.sub_mem hb.1 hc.1, _, _⟩ ;
    linarith },
  refine ⟨floor (x/g₂) * g₂, _, _⟩,
  { exact add_subgroup.int_mul_mem _ g₂_in },
  { rw abs_of_nonneg (sub_floor_div_mul_nonneg x g₂_pos),
    linarith [sub_floor_div_mul_lt x g₂_pos] }
end

/-- Subgroups of `ℝ` are either dense or cyclic. See `real.subgroup_dense_of_no_min` and
`subgroup_cyclic_of_min` for more precise statements. -/
lemma real.subgroup_dense_or_cyclic (G : add_subgroup ℝ) :
  dense (G : set ℝ) ∨ ∃ a : ℝ, G = add_subgroup.closure {a} :=
begin
  cases add_subgroup.bot_or_exists_ne_zero G with H H,
  { right,
    use 0,
    rw [H, add_subgroup.closure_singleton_zero] },
  { let G_pos := {g : ℝ | g ∈ G ∧ 0 < g},
    by_cases H' : ∃ a, is_least G_pos a,
    { right,
      rcases H' with ⟨a, ha⟩,
      exact ⟨a, add_subgroup.cyclic_of_min ha⟩ },
    { left,
      rcases H with ⟨g₀, g₀_in, g₀_ne⟩,
      exact real.subgroup_dense_of_no_min g₀_in g₀_ne H' } }
end

end subgroups
