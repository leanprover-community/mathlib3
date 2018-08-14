/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

The real numbers ℝ.

They are constructed as the topological completion of ℚ. With the following steps:
(1) prove that ℚ forms a uniform space.
(2) subtraction and addition are uniform continuous functions in this space
(3) for multiplication and inverse this only holds on bounded subsets
(4) ℝ is defined as separated Cauchy filters over ℚ (the separation requires a quotient construction)
(5) extend the uniform continuous functions along the completion
(6) proof field properties using the principle of extension of identities

TODO

generalizations:
* topological groups & rings
* order topologies
* Archimedean fields

-/
import logic.function analysis.metric_space

noncomputable theory
open classical set lattice filter topological_space
local attribute [instance] prop_decidable

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

instance : metric_space ℚ :=
metric_space.induced coe rat.cast_injective real.metric_space

theorem rat.dist_eq (x y : ℚ) : dist x y = abs (x - y) := rfl

instance : metric_space ℤ :=
begin
  letI M := metric_space.induced coe int.cast_injective real.metric_space,
  refine @metric_space.replace_uniformity _ int.uniform_space M
    (le_antisymm refl_le_uniformity $ λ r ru,
      mem_uniformity_dist.2 ⟨1, zero_lt_one, λ a b h,
      mem_principal_sets.1 ru $ dist_le_zero.1 (_ : (abs (a - b) : ℝ) ≤ 0)⟩),
  simpa using (@int.cast_le ℝ _ _ 0).2 (int.lt_add_one_iff.1 $
    (@int.cast_lt ℝ _ (abs (a - b)) 1).1 $ by simpa using h)
end

theorem uniform_continuous_of_rat : uniform_continuous (coe : ℚ → ℝ) :=
uniform_continuous_vmap

theorem uniform_embedding_of_rat : uniform_embedding (coe : ℚ → ℝ) :=
metric_space.induced_uniform_embedding _ _ _

theorem dense_embedding_of_rat : dense_embedding (coe : ℚ → ℝ) :=
uniform_embedding_of_rat.dense_embedding $
λ x, mem_closure_iff_nhds.2 $ λ t ht,
let ⟨ε,ε0, hε⟩ := mem_nhds_iff_metric.1 ht in
let ⟨q, h⟩ := exists_rat_near x ε0 in
ne_empty_iff_exists_mem.2 ⟨_, hε (mem_ball'.2 h), q, rfl⟩

theorem embedding_of_rat : embedding (coe : ℚ → ℝ) := dense_embedding_of_rat.embedding

theorem continuous_of_rat : continuous (coe : ℚ → ℝ) := uniform_continuous_of_rat.continuous

theorem real.uniform_continuous_add : uniform_continuous (λp : ℝ × ℝ, p.1 + p.2) :=
uniform_continuous_of_metric.2 $ λ ε ε0,
let ⟨δ, δ0, Hδ⟩ := rat_add_continuous_lemma abs ε0 in
⟨δ, δ0, λ a b h, let ⟨h₁, h₂⟩ := max_lt_iff.1 h in Hδ h₁ h₂⟩

-- TODO(Mario): Find a way to use rat_add_continuous_lemma
theorem rat.uniform_continuous_add : uniform_continuous (λp : ℚ × ℚ, p.1 + p.2) :=
uniform_embedding_of_rat.uniform_continuous_iff.2 $ by simp [(∘)]; exact
((uniform_continuous_fst.comp uniform_continuous_of_rat).prod_mk
  (uniform_continuous_snd.comp uniform_continuous_of_rat)).comp real.uniform_continuous_add

theorem real.uniform_continuous_neg : uniform_continuous (@has_neg.neg ℝ _) :=
uniform_continuous_of_metric.2 $ λ ε ε0, ⟨_, ε0, λ a b h,
  by rw dist_comm at h; simpa [real.dist_eq] using h⟩

theorem rat.uniform_continuous_neg : uniform_continuous (@has_neg.neg ℚ _) :=
uniform_continuous_of_metric.2 $ λ ε ε0, ⟨_, ε0, λ a b h,
  by rw dist_comm at h; simpa [rat.dist_eq] using h⟩

instance : uniform_add_group ℝ :=
uniform_add_group.mk' real.uniform_continuous_add real.uniform_continuous_neg

instance : uniform_add_group ℚ :=
uniform_add_group.mk' rat.uniform_continuous_add rat.uniform_continuous_neg

instance : topological_add_group ℝ := by apply_instance
instance : topological_add_group ℚ := by apply_instance

instance : orderable_topology ℚ :=
induced_orderable_topology _ (λ x y, rat.cast_lt) (@exists_rat_btwn _ _ _)

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

lemma real.uniform_continuous_inv (s : set ℝ) {r : ℝ} (r0 : 0 < r) (H : ∀ x ∈ s, r ≤ abs x) :
  uniform_continuous (λp:s, p.1⁻¹) :=
uniform_continuous_of_metric.2 $ λ ε ε0,
let ⟨δ, δ0, Hδ⟩ := rat_inv_continuous_lemma abs ε0 r0 in
⟨δ, δ0, λ a b h, Hδ (H _ a.2) (H _ b.2) h⟩

lemma real.uniform_continuous_abs : uniform_continuous (abs : ℝ → ℝ) :=
uniform_continuous_of_metric.2 $ λ ε ε0,
  ⟨ε, ε0, λ a b, lt_of_le_of_lt (abs_abs_sub_abs_le_abs_sub _ _)⟩

lemma real.continuous_abs : continuous (abs : ℝ → ℝ) :=
real.uniform_continuous_abs.continuous

lemma rat.uniform_continuous_abs : uniform_continuous (abs : ℚ → ℚ) :=
uniform_continuous_of_metric.2 $ λ ε ε0,
  ⟨ε, ε0, λ a b h, lt_of_le_of_lt
    (by simpa [rat.dist_eq] using abs_abs_sub_abs_le_abs_sub _ _) h⟩

lemma rat.continuous_abs : continuous (abs : ℚ → ℚ) :=
rat.uniform_continuous_abs.continuous

lemma real.tendsto_inv {r : ℝ} (r0 : r ≠ 0) : tendsto (λq, q⁻¹) (nhds r) (nhds r⁻¹) :=
by rw ← abs_pos_iff at r0; exact
tendsto_of_uniform_continuous_subtype
  (real.uniform_continuous_inv {x | abs r / 2 < abs x} (half_pos r0) (λ x h, le_of_lt h))
  (mem_nhds_sets (real.continuous_abs _ $ is_open_lt' (abs r / 2)) (half_lt_self r0))

lemma real.continuous_inv' : continuous (λa:{r:ℝ // r ≠ 0}, a.val⁻¹) :=
continuous_iff_tendsto.mpr $ assume ⟨r, hr⟩,
  (continuous_iff_tendsto.mp continuous_subtype_val _).comp (real.tendsto_inv hr)

lemma real.continuous_inv [topological_space α] {f : α → ℝ} (h : ∀a, f a ≠ 0) (hf : continuous f) :
  continuous (λa, (f a)⁻¹) :=
show continuous ((has_inv.inv ∘ @subtype.val ℝ (λr, r ≠ 0)) ∘ λa, ⟨f a, h a⟩),
  from (continuous_subtype_mk _ hf).comp real.continuous_inv'

lemma real.uniform_continuous_mul_const {x : ℝ} : uniform_continuous ((*) x) :=
uniform_continuous_of_metric.2 $ λ ε ε0, begin
  cases no_top (abs x) with y xy,
  have y0 := lt_of_le_of_lt (abs_nonneg _) xy,
  refine ⟨_, div_pos ε0 y0, λ a b h, _⟩,
  rw [real.dist_eq, ← mul_sub, abs_mul, ← mul_div_cancel' ε (ne_of_gt y0)],
  exact mul_lt_mul' (le_of_lt xy) h (abs_nonneg _) y0
end

lemma real.uniform_continuous_mul (s : set (ℝ × ℝ))
  {r₁ r₂ : ℝ} (r₁0 : 0 < r₁) (r₂0 : 0 < r₂)
  (H : ∀ x ∈ s, abs (x : ℝ × ℝ).1 < r₁ ∧ abs x.2 < r₂) :
  uniform_continuous (λp:s, p.1.1 * p.1.2) :=
uniform_continuous_of_metric.2 $ λ ε ε0,
let ⟨δ, δ0, Hδ⟩ := rat_mul_continuous_lemma abs ε0 r₁0 r₂0 in
⟨δ, δ0, λ a b h,
  let ⟨h₁, h₂⟩ := max_lt_iff.1 h in Hδ (H _ a.2).1 (H _ b.2).2 h₁ h₂⟩

lemma real.continuous_mul : continuous (λp : ℝ × ℝ, p.1 * p.2) :=
continuous_iff_tendsto.2 $ λ ⟨a₁, a₂⟩,
tendsto_of_uniform_continuous_subtype
  (real.uniform_continuous_mul
    ({x | abs x < abs a₁ + 1}.prod {x | abs x < abs a₂ + 1})
    (lt_of_le_of_lt (abs_nonneg _) (lt_add_one _))
    (lt_of_le_of_lt (abs_nonneg _) (lt_add_one _))
    (λ x, id))
  (mem_nhds_sets
    (is_open_prod
      (real.continuous_abs _ $ is_open_gt' _)
      (real.continuous_abs _ $ is_open_gt' _))
    ⟨lt_add_one (abs a₁), lt_add_one (abs a₂)⟩)

instance : topological_ring ℝ :=
{ continuous_mul := real.continuous_mul, ..real.topological_add_group }

instance : topological_semiring ℝ := by apply_instance

lemma rat.continuous_mul : continuous (λp : ℚ × ℚ, p.1 * p.2) :=
embedding_of_rat.continuous_iff.2 $ by simp [(∘)]; exact
((continuous_fst.comp continuous_of_rat).prod_mk
  (continuous_snd.comp continuous_of_rat)).comp real.continuous_mul

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
totally_bounded_of_metric.2 $ λ ε ε0, begin
  rcases exists_nat_gt ((b - a) / ε) with ⟨n, ba⟩,
  rw [div_lt_iff' ε0, sub_lt_iff_lt_add'] at ba,
  let s := (λ i:ℕ, a + ε * i) '' {i:ℕ | i < n},
  refine ⟨s, finite_image _ ⟨set.fintype_lt_nat _⟩, λ x h, _⟩,
  rcases h with ⟨ax, xb⟩,
  let i : ℕ := ⌊(x - a) / ε⌋.to_nat,
  have : (i : ℤ) = ⌊(x - a) / ε⌋ :=
    int.to_nat_of_nonneg (floor_nonneg.2 $ le_of_lt (div_pos (sub_pos.2 ax) ε0)),
  simp, refine ⟨_, ⟨i, _, rfl⟩, _⟩,
  { rw [← int.coe_nat_lt, this],
    refine int.cast_lt.1 (lt_of_le_of_lt (floor_le _) _),
    rw [int.cast_coe_nat, div_lt_iff' ε0, sub_lt_iff_lt_add'],
    exact lt_trans xb ba },
  { rw [real.dist_eq, ← int.cast_coe_nat, this, abs_of_nonneg,
        ← sub_sub, sub_lt_iff_lt_add'],
    { have := lt_floor_add_one ((x - a) / ε),
      rwa [div_lt_iff' ε0, mul_add, mul_one] at this },
    { have := floor_le ((x - a) / ε),
      rwa [ge, sub_nonneg, ← le_sub_iff_add_le', ← le_div_iff' ε0] } }
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

-- TODO(Mario): Generalize to first-countable uniform spaces?
instance : complete_space ℝ :=
⟨λ f cf, begin
  have := (cauchy_of_metric.1 cf).2,
  let S : ∀ ε:{ε:ℝ//ε>0}, {t : f.sets // ∀ x y ∈ t.1, dist x y < ε} :=
    λ ε, classical.choice
      (let ⟨t, tf, h⟩ := (cauchy_of_metric.1 cf).2 ε ε.2 in ⟨⟨⟨t, tf⟩, h⟩⟩),
  let g : ℕ → {ε:ℝ//ε>0} := λ n,
    ⟨n.to_pnat'⁻¹, inv_pos (nat.cast_pos.2 n.to_pnat'.pos)⟩,
  have hg : ∀ ε > 0, ∃ n, ∀ j ≥ n, (g j : ℝ) < ε,
  { intros ε ε0,
    cases exists_nat_gt ε⁻¹ with n hn,
    refine ⟨n, λ j nj, _⟩,
    have hj := lt_of_lt_of_le hn (nat.cast_le.2 nj),
    have j0 := lt_trans (inv_pos ε0) hj,
    have jε := (inv_lt j0 ε0).2 hj,
    rwa ← pnat.to_pnat'_coe (nat.cast_pos.1 j0) at jε },
  let F : ∀ n : ℕ, {t : f.sets // ∀ x y ∈ t.1, dist x y < g n},
  { refine λ n, ⟨⟨_, Inter_mem_sets (finite_le_nat n) (λ i _, (S (g i)).1.2)⟩, _⟩,
    have : (⋂ i ∈ {i : ℕ | i ≤ n}, (S (g i)).1.1) ⊆ S (g n) :=
      bInter_subset_of_mem (le_refl n),
    exact λ x y xs ys, (S (g n)).2 _ _ (this xs) (this ys) },
  let G : ∀ n : ℕ, F n,
  { refine λ n, classical.choice _,
    cases inhabited_of_mem_sets cf.1 (F n).1.2 with x xS,
    exact ⟨⟨x, xS⟩⟩ },
  let c : cau_seq ℝ abs,
  { refine ⟨λ n, G n, λ ε ε0, _⟩,
    cases hg _ ε0 with n hn,
    refine ⟨n, λ j jn, _⟩,
    have : (F j).1.1 ⊆ (F n) :=
      bInter_subset_bInter_left (λ i h, @le_trans _ _ i n j h jn),
    exact lt_trans ((F n).2 _ _ (this (G j).2) (G n).2) (hn _ $ le_refl _) },
  refine ⟨real.lim c, λ s h, _⟩,
  rcases mem_nhds_iff_metric.1 h with ⟨ε, ε0, hε⟩,
  cases exists_forall_ge_and (hg _ $ half_pos ε0)
    (real.equiv_lim c _ $ half_pos ε0) with n hn,
  cases hn _ (le_refl _) with h₁ h₂,
  refine sets_of_superset _ (F n).1.2 (subset.trans _ $
    subset.trans (ball_half_subset (G n) h₂) hε),
  exact λ x h, lt_trans ((F n).2 x (G n) h (G n).2) h₁
end⟩

-- TODO(Mario): This proof has nothing to do with reals
theorem real.Cauchy_eq {f g : Cauchy ℝ} :
  lim f.1 = lim g.1 ↔ (f, g) ∈ separation_rel (Cauchy ℝ) :=
begin
  split,
  { intros e s hs,
    rcases Cauchy.mem_uniformity'.1 hs with ⟨t, tu, ts⟩,
    apply ts,
    rcases comp_mem_uniformity_sets tu with ⟨d, du, dt⟩,
    refine mem_prod_iff.2
      ⟨_, le_nhds_lim_of_cauchy f.2 (mem_nhds_right (lim f.1) du),
       _, le_nhds_lim_of_cauchy g.2 (mem_nhds_left (lim g.1) du), λ x h, _⟩,
    cases x with a b, cases h with h₁ h₂,
    rw ← e at h₂,
    exact dt ⟨_, h₁, h₂⟩ },
  { intros H,
    refine separated_def.1 (by apply_instance) _ _ (λ t tu, _),
    rcases mem_uniformity_is_closed tu with ⟨d, du, dc, dt⟩,
    refine H {p | (lim p.1.1, lim p.2.1) ∈ t}
      (Cauchy.mem_uniformity'.2 ⟨d, du, λ f g h, _⟩),
    rcases mem_prod_iff.1 h with ⟨x, xf, y, yg, h⟩,
    have limc : ∀ (f : Cauchy ℝ) (x ∈ f.1.sets), lim f.1 ∈ closure x,
    { intros f x xf,
      rw closure_eq_nhds,
      exact neq_bot_of_le_neq_bot f.2.1
        (le_inf (le_nhds_lim_of_cauchy f.2) (le_principal_iff.2 xf)) },
    have := (closure_subset_iff_subset_of_is_closed dc).2 h,
    rw closure_prod_eq at this,
    refine dt (this ⟨_, _⟩); dsimp; apply limc; assumption }
end

lemma tendsto_of_nat_at_top_at_top : tendsto (coe : ℕ → ℝ) at_top at_top :=
tendsto_infi.2 $ assume r, tendsto_principal.2 $
let ⟨n, hn⟩ := exists_nat_gt r in
mem_at_top_sets.2 ⟨n, λ m h, le_trans (le_of_lt hn) (nat.cast_le.2 h)⟩

section

lemma closure_of_rat_image_lt {q : ℚ} : closure ((coe:ℚ → ℝ) '' {x | q < x}) = {r | ↑q ≤ r} :=
subset.antisymm
  ((closure_subset_iff_subset_of_is_closed (is_closed_ge' _)).2
    (image_subset_iff.2 $ λ p h, le_of_lt $ (@rat.cast_lt ℝ _ _ _).2 h)) $
λ x hx, mem_closure_iff_nhds.2 $ λ t ht,
let ⟨ε, ε0, hε⟩ := mem_nhds_iff_metric.1 ht in
let ⟨p, h₁, h₂⟩ := exists_rat_btwn ((lt_add_iff_pos_right x).2 ε0) in
ne_empty_iff_exists_mem.2 ⟨_, hε (show abs _ < _,
    by rwa [abs_of_nonneg (le_of_lt $ sub_pos.2 h₁), sub_lt_iff_lt_add']),
  p, rat.cast_lt.1 (@lt_of_le_of_lt ℝ _ _ _ _ hx h₁), rfl⟩

/- TODO(Mario): Put these back only if needed later
lemma closure_of_rat_image_le_eq {q : ℚ} : closure ((coe:ℚ → ℝ) '' {x | q ≤ x}) = {r | ↑q ≤ r} :=
_

lemma closure_of_rat_image_le_le_eq {a b : ℚ} (hab : a ≤ b) :
  closure (of_rat '' {q:ℚ | a ≤ q ∧ q ≤ b}) = {r:ℝ | of_rat a ≤ r ∧ r ≤ of_rat b} :=
_-/

lemma compact_Icc {a b : ℝ} : compact (Icc a b) :=
compact_of_totally_bounded_is_closed
  (real.totally_bounded_Icc a b)
  (is_closed_inter (is_closed_ge' a) (is_closed_le' b))

end
