/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import topology.metric_space.basic
import topology.algebra.uniform_group
import topology.algebra.ring
import topology.algebra.continuous_functions
import ring_theory.subring
import group_theory.archimedean
/-!
# Topological properties of ℝ
-/

noncomputable theory
open classical set filter topological_space metric
open_locale classical
open_locale topological_space

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

instance : metric_space ℚ :=
metric_space.induced coe rat.cast_injective real.metric_space

theorem rat.dist_eq (x y : ℚ) : dist x y = abs (x - y) := rfl

@[norm_cast, simp] lemma rat.dist_cast (x y : ℚ) : dist (x : ℝ) y = dist x y := rfl

section low_prio
-- we want to ignore this instance for the next declaration
local attribute [instance, priority 10] int.uniform_space
instance : metric_space ℤ :=
begin
  letI M := metric_space.induced coe int.cast_injective real.metric_space,
  refine @metric_space.replace_uniformity _ int.uniform_space M
    (le_antisymm refl_le_uniformity $ λ r ru,
      mem_uniformity_dist.2 ⟨1, zero_lt_one, λ a b h,
      mem_principal_sets.1 ru $ dist_le_zero.1 (_ : (abs (a - b) : ℝ) ≤ 0)⟩),
  have : (abs (↑a - ↑b) : ℝ) < 1 := h,
  have : abs (a - b) < 1, by norm_cast at this; assumption,
  have : abs (a - b) ≤ 0 := (@int.lt_add_one_iff _ 0).mp this,
  norm_cast, assumption
end
end low_prio

theorem int.dist_eq (x y : ℤ) : dist x y = abs (x - y) := rfl

@[norm_cast, simp] theorem int.dist_cast_real (x y : ℤ) : dist (x : ℝ) y = dist x y := rfl

@[norm_cast, simp] theorem int.dist_cast_rat (x y : ℤ) : dist (x : ℚ) y = dist x y :=
by rw [← int.dist_cast_real, ← rat.dist_cast]; congr' 1; norm_cast

theorem uniform_continuous_of_rat : uniform_continuous (coe : ℚ → ℝ) :=
uniform_continuous_comap

theorem uniform_embedding_of_rat : uniform_embedding (coe : ℚ → ℝ) :=
uniform_embedding_comap rat.cast_injective

theorem dense_embedding_of_rat : dense_embedding (coe : ℚ → ℝ) :=
uniform_embedding_of_rat.dense_embedding $
λ x, mem_closure_iff_nhds.2 $ λ t ht,
let ⟨ε,ε0, hε⟩ := mem_nhds_iff.1 ht in
let ⟨q, h⟩ := exists_rat_near x ε0 in
⟨_, hε (mem_ball'.2 h), q, rfl⟩

theorem embedding_of_rat : embedding (coe : ℚ → ℝ) := dense_embedding_of_rat.to_embedding

theorem continuous_of_rat : continuous (coe : ℚ → ℝ) := uniform_continuous_of_rat.continuous

theorem real.uniform_continuous_add : uniform_continuous (λp : ℝ × ℝ, p.1 + p.2) :=
metric.uniform_continuous_iff.2 $ λ ε ε0,
let ⟨δ, δ0, Hδ⟩ := rat_add_continuous_lemma abs ε0 in
⟨δ, δ0, λ a b h, let ⟨h₁, h₂⟩ := max_lt_iff.1 h in Hδ h₁ h₂⟩

-- TODO(Mario): Find a way to use rat_add_continuous_lemma
theorem rat.uniform_continuous_add : uniform_continuous (λp : ℚ × ℚ, p.1 + p.2) :=
uniform_embedding_of_rat.to_uniform_inducing.uniform_continuous_iff.2 $ by simp [(∘)]; exact
real.uniform_continuous_add.comp ((uniform_continuous_of_rat.comp uniform_continuous_fst).prod_mk
  (uniform_continuous_of_rat.comp uniform_continuous_snd))

theorem real.uniform_continuous_neg : uniform_continuous (@has_neg.neg ℝ _) :=
metric.uniform_continuous_iff.2 $ λ ε ε0, ⟨_, ε0, λ a b h,
  by rw dist_comm at h; simpa [real.dist_eq] using h⟩

theorem rat.uniform_continuous_neg : uniform_continuous (@has_neg.neg ℚ _) :=
metric.uniform_continuous_iff.2 $ λ ε ε0, ⟨_, ε0, λ a b h,
  by rw dist_comm at h; simpa [rat.dist_eq] using h⟩

instance : uniform_add_group ℝ :=
uniform_add_group.mk' real.uniform_continuous_add real.uniform_continuous_neg

instance : uniform_add_group ℚ :=
uniform_add_group.mk' rat.uniform_continuous_add rat.uniform_continuous_neg

 -- short-circuit type class inference
instance : topological_add_group ℝ := by apply_instance
instance : topological_add_group ℚ := by apply_instance

instance : order_topology ℚ :=
induced_order_topology _ (λ x y, rat.cast_lt) (@exists_rat_btwn _ _ _)

lemma real.is_topological_basis_Ioo_rat :
  @is_topological_basis ℝ _ (⋃(a b : ℚ) (h : a < b), {Ioo a b}) :=
is_topological_basis_of_open_of_nhds
  (by simp [is_open_Ioo] {contextual:=tt})
  (assume a v hav hv,
    let ⟨l, u, hl, hu, h⟩ := (mem_nhds_unbounded (no_top _) (no_bot _)).mp (mem_nhds_sets hv hav),
        ⟨q, hlq, hqa⟩ := exists_rat_btwn hl,
        ⟨p, hap, hpu⟩ := exists_rat_btwn hu in
    ⟨Ioo q p,
      by simp; exact ⟨q, p, rat.cast_lt.1 $ lt_trans hqa hap, rfl⟩,
      ⟨hqa, hap⟩, assume a' ⟨hqa', ha'p⟩, h _ (lt_trans hlq hqa') (lt_trans ha'p hpu)⟩)

instance : second_countable_topology ℝ :=
⟨⟨(⋃(a b : ℚ) (h : a < b), {Ioo a b}),
  by simp [countable_Union, countable_Union_Prop],
  real.is_topological_basis_Ioo_rat.2.2⟩⟩

/- TODO(Mario): Prove that these are uniform isomorphisms instead of uniform embeddings
lemma uniform_embedding_add_rat {r : ℚ} : uniform_embedding (λp:ℚ, p + r) :=
_

lemma uniform_embedding_mul_rat {q : ℚ} (hq : q ≠ 0) : uniform_embedding ((*) q) :=
_ -/

lemma real.mem_closure_iff {s : set ℝ} {x : ℝ} : x ∈ closure s ↔ ∀ ε > 0, ∃ y ∈ s, abs (y - x) < ε :=
by simp [mem_closure_iff_nhds_basis nhds_basis_ball, real.dist_eq]

lemma real.uniform_continuous_inv (s : set ℝ) {r : ℝ} (r0 : 0 < r) (H : ∀ x ∈ s, r ≤ abs x) :
  uniform_continuous (λp:s, p.1⁻¹) :=
metric.uniform_continuous_iff.2 $ λ ε ε0,
let ⟨δ, δ0, Hδ⟩ := rat_inv_continuous_lemma abs ε0 r0 in
⟨δ, δ0, λ a b h, Hδ (H _ a.2) (H _ b.2) h⟩

lemma real.uniform_continuous_abs : uniform_continuous (abs : ℝ → ℝ) :=
metric.uniform_continuous_iff.2 $ λ ε ε0,
  ⟨ε, ε0, λ a b, lt_of_le_of_lt (abs_abs_sub_abs_le_abs_sub _ _)⟩

lemma rat.uniform_continuous_abs : uniform_continuous (abs : ℚ → ℚ) :=
metric.uniform_continuous_iff.2 $ λ ε ε0,
  ⟨ε, ε0, λ a b h, lt_of_le_of_lt
    (by simpa [rat.dist_eq] using abs_abs_sub_abs_le_abs_sub _ _) h⟩

lemma real.tendsto_inv {r : ℝ} (r0 : r ≠ 0) : tendsto (λq, q⁻¹) (𝓝 r) (𝓝 r⁻¹) :=
by rw ← abs_pos at r0; exact
tendsto_of_uniform_continuous_subtype
  (real.uniform_continuous_inv {x | abs r / 2 < abs x} (half_pos r0) (λ x h, le_of_lt h))
  (mem_nhds_sets ((is_open_lt' (abs r / 2)).preimage continuous_abs) (half_lt_self r0))

lemma real.continuous_inv : continuous (λa:{r:ℝ // r ≠ 0}, a.val⁻¹) :=
continuous_iff_continuous_at.mpr $ assume ⟨r, hr⟩,
  tendsto.comp (real.tendsto_inv hr) (continuous_iff_continuous_at.mp continuous_subtype_val _)

lemma real.continuous.inv [topological_space α] {f : α → ℝ} (h : ∀a, f a ≠ 0) (hf : continuous f) :
  continuous (λa, (f a)⁻¹) :=
show continuous ((has_inv.inv ∘ @subtype.val ℝ (λr, r ≠ 0)) ∘ λa, ⟨f a, h a⟩),
  from real.continuous_inv.comp (continuous_subtype_mk _ hf)

lemma real.uniform_continuous_mul_const {x : ℝ} : uniform_continuous ((*) x) :=
metric.uniform_continuous_iff.2 $ λ ε ε0, begin
  cases no_top (abs x) with y xy,
  have y0 := lt_of_le_of_lt (abs_nonneg _) xy,
  refine ⟨_, div_pos ε0 y0, λ a b h, _⟩,
  rw [real.dist_eq, ← mul_sub, abs_mul, ← mul_div_cancel' ε (ne_of_gt y0)],
  exact mul_lt_mul' (le_of_lt xy) h (abs_nonneg _) y0
end

lemma real.uniform_continuous_mul (s : set (ℝ × ℝ))
  {r₁ r₂ : ℝ} (H : ∀ x ∈ s, abs (x : ℝ × ℝ).1 < r₁ ∧ abs x.2 < r₂) :
  uniform_continuous (λp:s, p.1.1 * p.1.2) :=
metric.uniform_continuous_iff.2 $ λ ε ε0,
let ⟨δ, δ0, Hδ⟩ := rat_mul_continuous_lemma abs ε0 in
⟨δ, δ0, λ a b h,
  let ⟨h₁, h₂⟩ := max_lt_iff.1 h in Hδ (H _ a.2).1 (H _ b.2).2 h₁ h₂⟩

protected lemma real.continuous_mul : continuous (λp : ℝ × ℝ, p.1 * p.2) :=
continuous_iff_continuous_at.2 $ λ ⟨a₁, a₂⟩,
tendsto_of_uniform_continuous_subtype
  (real.uniform_continuous_mul
    ({x | abs x < abs a₁ + 1}.prod {x | abs x < abs a₂ + 1})
    (λ x, id))
  (mem_nhds_sets
    (((is_open_gt' (abs a₁ + 1)).preimage real.continuous_abs).prod
      ((is_open_gt' (abs a₂ + 1)).preimage real.continuous_abs ))
    ⟨lt_add_one (abs a₁), lt_add_one (abs a₂)⟩)

instance : topological_ring ℝ :=
{ continuous_mul := real.continuous_mul, ..real.topological_add_group }

instance : topological_semiring ℝ := by apply_instance  -- short-circuit type class inference

lemma rat.continuous_mul : continuous (λp : ℚ × ℚ, p.1 * p.2) :=
embedding_of_rat.continuous_iff.2 $ by simp [(∘)]; exact
real.continuous_mul.comp ((continuous_of_rat.comp continuous_fst).prod_mk
  (continuous_of_rat.comp continuous_snd))

instance : topological_ring ℚ :=
{ continuous_mul := rat.continuous_mul, ..rat.topological_add_group }

theorem real.ball_eq_Ioo (x ε : ℝ) : ball x ε = Ioo (x - ε) (x + ε) :=
set.ext $ λ y, by rw [mem_ball, real.dist_eq,
  abs_sub_lt_iff, sub_lt_iff_lt_add', and_comm, sub_lt]; refl

theorem real.Ioo_eq_ball (x y : ℝ) : Ioo x y = ball ((x + y) / 2) ((y - x) / 2) :=
by rw [real.ball_eq_Ioo, ← sub_div, add_comm, ← sub_add,
  add_sub_cancel', add_self_div_two, ← add_div,
  add_assoc, add_sub_cancel'_right, add_self_div_two]

lemma real.totally_bounded_Ioo (a b : ℝ) : totally_bounded (Ioo a b) :=
metric.totally_bounded_iff.2 $ λ ε ε0, begin
  rcases exists_nat_gt ((b - a) / ε) with ⟨n, ba⟩,
  rw [div_lt_iff' ε0, sub_lt_iff_lt_add'] at ba,
  let s := (λ i:ℕ, a + ε * i) '' {i:ℕ | i < n},
  refine ⟨s, (set.finite_lt_nat _).image _, _⟩,
  rintro x ⟨ax, xb⟩,
  let i : ℕ := ⌊(x - a) / ε⌋.to_nat,
  have : (i : ℤ) = ⌊(x - a) / ε⌋ :=
    int.to_nat_of_nonneg (floor_nonneg.2 $ le_of_lt (div_pos (sub_pos.2 ax) ε0)),
  simp, use i, split,
  { rw [← int.coe_nat_lt, this],
    refine int.cast_lt.1 (lt_of_le_of_lt (floor_le _) _),
    rw [int.cast_coe_nat, div_lt_iff' ε0, sub_lt_iff_lt_add'],
    exact lt_trans xb ba },
  { rw [real.dist_eq, ← int.cast_coe_nat, this, abs_of_nonneg,
        ← sub_sub, sub_lt_iff_lt_add'],
    { have := lt_floor_add_one ((x - a) / ε),
      rwa [div_lt_iff' ε0, mul_add, mul_one] at this },
    { have := floor_le ((x - a) / ε),
      rwa [sub_nonneg, ← le_sub_iff_add_le', ← le_div_iff' ε0] } }
end

lemma real.totally_bounded_ball (x ε : ℝ) : totally_bounded (ball x ε) :=
by rw real.ball_eq_Ioo; apply real.totally_bounded_Ioo

lemma real.totally_bounded_Ico (a b : ℝ) : totally_bounded (Ico a b) :=
let ⟨c, ac⟩ := no_bot a in totally_bounded_subset
  (by exact λ x ⟨h₁, h₂⟩, ⟨lt_of_lt_of_le ac h₁, h₂⟩)
  (real.totally_bounded_Ioo c b)

lemma real.totally_bounded_Icc (a b : ℝ) : totally_bounded (Icc a b) :=
let ⟨c, bc⟩ := no_top b in totally_bounded_subset
  (by exact λ x ⟨h₁, h₂⟩, ⟨h₁, lt_of_le_of_lt h₂ bc⟩)
  (real.totally_bounded_Ico a c)

lemma rat.totally_bounded_Icc (a b : ℚ) : totally_bounded (Icc a b) :=
begin
  have := totally_bounded_preimage uniform_embedding_of_rat (real.totally_bounded_Icc a b),
  rwa (set.ext (λ q, _) : Icc _ _ = _), simp
end

instance : complete_space ℝ :=
begin
  apply complete_of_cauchy_seq_tendsto,
  intros u hu,
  let c : cau_seq ℝ abs := ⟨u, cauchy_seq_iff'.1 hu⟩,
  refine ⟨c.lim, λ s h, _⟩,
  rcases metric.mem_nhds_iff.1 h with ⟨ε, ε0, hε⟩,
  have := c.equiv_lim ε ε0,
  simp only [mem_map, mem_at_top_sets, mem_set_of_eq],
  refine this.imp (λ N hN n hn, hε (hN n hn))
end

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

lemma compact_Icc {a b : ℝ} : is_compact (Icc a b) :=
compact_of_totally_bounded_is_closed
  (real.totally_bounded_Icc a b)
  (is_closed_inter (is_closed_ge' a) (is_closed_le' b))

lemma compact_pi_Icc {ι : Type*} {a b : ι → ℝ} : is_compact (Icc a b) :=
pi_univ_Icc a b ▸ compact_univ_pi $ λ i, compact_Icc

instance : proper_space ℝ :=
{ compact_ball := λx r, by rw closed_ball_Icc; apply compact_Icc }

lemma real.bounded_iff_bdd_below_bdd_above {s : set ℝ} : bounded s ↔ bdd_below s ∧ bdd_above s :=
⟨begin
  assume bdd,
  rcases (bounded_iff_subset_ball 0).1 bdd with ⟨r, hr⟩, -- hr : s ⊆ closed_ball 0 r
  rw closed_ball_Icc at hr, -- hr : s ⊆ Icc (0 - r) (0 + r)
  exact ⟨⟨-r, λy hy, by simpa using (hr hy).1⟩, ⟨r, λy hy, by simpa using (hr hy).2⟩⟩
end,
begin
  rintros ⟨⟨m, hm⟩, ⟨M, hM⟩⟩,
  have I : s ⊆ Icc m M := λx hx, ⟨hm hx, hM hx⟩,
  have : Icc m M = closed_ball ((m+M)/2) ((M-m)/2) :=
    by rw closed_ball_Icc; congr; ring,
  rw this at I,
  exact bounded.subset I bounded_closed_ball
end⟩

lemma real.image_Icc {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (h : continuous_on f $ Icc a b) :
  f '' Icc a b = Icc (Inf $ f '' Icc a b) (Sup $ f '' Icc a b) :=
eq_Icc_of_connected_compact ⟨(nonempty_Icc.2 hab).image f, is_preconnected_Icc.image f h⟩
  (compact_Icc.image_of_continuous_on h)

end

instance reals_semimodule : topological_semimodule ℝ ℝ := ⟨continuous_mul⟩

instance real_maps_algebra {α : Type*} [topological_space α] :
  algebra ℝ C(α, ℝ) := continuous_map_algebra

section subgroups

/-- Given a nontrivial subgroup `G ⊆ ℝ`, if `G ∩ ℝ_{>0}` has no minimum then `G` is dense. -/
lemma real.subgroup_dense_of_no_min {G : add_subgroup ℝ} {g₀ : ℝ} (g₀_in : g₀ ∈ G) (g₀_ne : g₀ ≠ 0)
  (H' : ¬ ∃ a : ℝ, is_least {g : ℝ | g ∈ G ∧ 0 < g} a) :
  dense (G : set ℝ) :=
begin
  let G_pos := {g : ℝ | g ∈ G ∧ 0 < g},
  push_neg at H',
  intros x,
  suffices : ∀ ε > (0 : ℝ), ∃ g ∈ G, abs (x - g) < ε,
    by simpa only [real.mem_closure_iff, abs_sub],
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
  { obtain ⟨b, hb, hb', hb''⟩ := ha.exists_between_self_add' ε_pos a_notin,
    obtain ⟨c, hc, hc', hc''⟩ := ha.exists_between_self_add' (by linarith : 0 < b - a) a_notin,
    refine ⟨b - c, add_subgroup.sub_mem G hb.1 hc.1, _, _⟩ ;
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
