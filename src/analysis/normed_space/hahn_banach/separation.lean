/-
Copyright (c) 2022 Bhavik Mehta All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Yaël Dillies
-/
import analysis.convex.cone.basic
import analysis.convex.gauge
import topology.algebra.module.locally_convex

/-!
# Separation Hahn-Banach theorem

In this file we prove the geometric Hahn-Banach theorem. For any two disjoint convex sets, there
exists a continuous linear functional separating them, geometrically meaning that we can intercalate
a plane between them.

We provide many variations to stricten the result under more assumptions on the convex sets:
* `geometric_hahn_banach_open`: One set is open. Weak separation.
* `geometric_hahn_banach_open_point`, `geometric_hahn_banach_point_open`: One set is open, the
  other is a singleton. Weak separation.
* `geometric_hahn_banach_open_open`: Both sets are open. Semistrict separation.
* `geometric_hahn_banach_compact_closed`, `geometric_hahn_banach_closed_compact`: One set is closed,
  the other one is compact. Strict separation.
* `geometric_hahn_banach_point_closed`, `geometric_hahn_banach_closed_point`: One set is closed, the
  other one is a singleton. Strict separation.
* `geometric_hahn_banach_point_point`: Both sets are singletons. Strict separation.

## TODO

* Eidelheit's theorem
* `convex ℝ s → interior (closure s) ⊆ s`
-/

open set
open_locale pointwise

variables {𝕜 E : Type*}

/-- Given a set `s` which is a convex neighbourhood of `0` and a point `x₀` outside of it, there is
a continuous linear functional `f` separating `x₀` and `s`, in the sense that it sends `x₀` to 1 and
all of `s` to values strictly below `1`. -/
lemma separate_convex_open_set [topological_space E] [add_comm_group E] [topological_add_group E]
  [module ℝ E] [has_continuous_smul ℝ E] {s : set E}
  (hs₀ : (0 : E) ∈ s) (hs₁ : convex ℝ s) (hs₂ : is_open s) {x₀ : E} (hx₀ : x₀ ∉ s) :
  ∃ f : E →L[ℝ] ℝ, f x₀ = 1 ∧ ∀ x ∈ s, f x < 1 :=
begin
  let f : E →ₗ.[ℝ] ℝ :=
    linear_pmap.mk_span_singleton x₀ 1 (ne_of_mem_of_not_mem hs₀ hx₀).symm,
  obtain ⟨φ, hφ₁, hφ₂⟩ := exists_extension_of_le_sublinear f (gauge s)
    (λ c hc, gauge_smul_of_nonneg hc.le)
    (gauge_add_le hs₁ $ absorbent_nhds_zero $ hs₂.mem_nhds hs₀) _,
  have hφ₃ : φ x₀ = 1,
  { rw [←submodule.coe_mk x₀ (submodule.mem_span_singleton_self _), hφ₁,
      linear_pmap.mk_span_singleton'_apply_self] },
  have hφ₄ : ∀ x ∈ s, φ x < 1,
  { exact λ x hx, (hφ₂ x).trans_lt (gauge_lt_one_of_mem_of_open hs₁ hs₀ hs₂ hx) },
  { refine ⟨⟨φ, _⟩, hφ₃, hφ₄⟩,
    refine φ.continuous_of_nonzero_on_open _ (hs₂.vadd (-x₀)) (nonempty.vadd_set ⟨0, hs₀⟩)
      (vadd_set_subset_iff.mpr $ λ x hx, _),
    change φ (-x₀ + x) ≠ 0,
    rw [map_add, map_neg],
    specialize hφ₄ x hx,
    linarith },
  rintro ⟨x, hx⟩,
  obtain ⟨y, rfl⟩ := submodule.mem_span_singleton.1 hx,
  rw linear_pmap.mk_span_singleton'_apply,
  simp only [mul_one, algebra.id.smul_eq_mul, submodule.coe_mk],
  obtain h | h := le_or_lt y 0,
  { exact h.trans (gauge_nonneg _) },
  { rw [gauge_smul_of_nonneg h.le, smul_eq_mul, le_mul_iff_one_le_right h],
    exact one_le_gauge_of_not_mem (hs₁.star_convex hs₀)
      (absorbent_nhds_zero $ hs₂.mem_nhds hs₀).absorbs hx₀,
    apply_instance }
end

variables [topological_space E] [add_comm_group E] [topological_add_group E] [module ℝ E]
  [has_continuous_smul ℝ E] {s t : set E} {x y : E}

/-- A version of the **Hahn-Banach theorem**: given disjoint convex sets `s`, `t` where `s` is open,
there is a continuous linear functional which separates them. -/
theorem geometric_hahn_banach_open (hs₁ : convex ℝ s) (hs₂ : is_open s) (ht : convex ℝ t)
  (disj : disjoint s t) :
  ∃ (f : E →L[ℝ] ℝ) (u : ℝ), (∀ a ∈ s, f a < u) ∧ ∀ b ∈ t, u ≤ f b :=
begin
  obtain rfl | ⟨a₀, ha₀⟩ := s.eq_empty_or_nonempty,
  { exact ⟨0, 0, by simp, λ b hb, le_rfl⟩ },
  obtain rfl | ⟨b₀, hb₀⟩ := t.eq_empty_or_nonempty,
  { exact ⟨0, 1, λ a ha, zero_lt_one, by simp⟩ },
  let x₀ := b₀ - a₀,
  let C := x₀ +ᵥ (s - t),
  have : (0:E) ∈ C := ⟨a₀ - b₀, sub_mem_sub ha₀ hb₀,
    by rw [vadd_eq_add, sub_add_sub_cancel', sub_self]⟩,
  have : convex ℝ C := (hs₁.sub ht).vadd _,
  have : x₀ ∉ C,
  { intro hx₀,
    rw ←add_zero x₀ at hx₀,
    exact disj.zero_not_mem_sub_set (vadd_mem_vadd_set_iff.1 hx₀) },
  obtain ⟨f, hf₁, hf₂⟩ := separate_convex_open_set ‹0 ∈ C› ‹_› (hs₂.sub_right.vadd _) ‹x₀ ∉ C›,
  have : f b₀ = f a₀ + 1 := by simp [←hf₁],
  have forall_le : ∀ (a ∈ s) (b ∈ t), f a ≤ f b,
  { intros a ha b hb,
    have := hf₂ (x₀ + (a - b)) (vadd_mem_vadd_set $ sub_mem_sub ha hb),
    simp only [f.map_add, f.map_sub, hf₁] at this,
    linarith },
  refine ⟨f, Inf (f '' t), image_subset_iff.1 (_ : f '' s ⊆ Iio (Inf (f '' t))), λ b hb, _⟩,
  { rw ←interior_Iic,
    refine interior_maximal (image_subset_iff.2 $ λ a ha, _) (f.is_open_map_of_ne_zero _ _ hs₂),
    { exact le_cInf (nonempty.image _ ⟨_, hb₀⟩) (ball_image_of_ball $ forall_le _ ha) },
    { rintro rfl,
      simpa using hf₁ } },
  { exact cInf_le ⟨f a₀, ball_image_of_ball $ forall_le _ ha₀⟩ (mem_image_of_mem _ hb) }
end

theorem geometric_hahn_banach_open_point (hs₁ : convex ℝ s) (hs₂ : is_open s) (disj : x ∉ s) :
  ∃ f : E →L[ℝ] ℝ, ∀ a ∈ s, f a < f x :=
let ⟨f, s, hs, hx⟩ := geometric_hahn_banach_open hs₁ hs₂ (convex_singleton x)
  (disjoint_singleton_right.2 disj)
  in ⟨f, λ a ha, lt_of_lt_of_le (hs a ha) (hx x (mem_singleton _))⟩

theorem geometric_hahn_banach_point_open (ht₁ : convex ℝ t) (ht₂ : is_open t) (disj : x ∉ t) :
  ∃ f : E →L[ℝ] ℝ, ∀ b ∈ t, f x < f b :=
let ⟨f, hf⟩ := geometric_hahn_banach_open_point ht₁ ht₂ disj in ⟨-f, by simpa⟩

theorem geometric_hahn_banach_open_open (hs₁ : convex ℝ s) (hs₂ : is_open s) (ht₁ : convex ℝ t)
  (ht₃ : is_open t) (disj : disjoint s t) :
  ∃ (f : E →L[ℝ] ℝ) (u : ℝ), (∀ a ∈ s, f a < u) ∧ ∀ b ∈ t, u < f b :=
begin
  obtain (rfl | ⟨a₀, ha₀⟩) := s.eq_empty_or_nonempty,
  { exact ⟨0, -1, by simp, λ b hb, by norm_num⟩ },
  obtain (rfl | ⟨b₀, hb₀⟩) := t.eq_empty_or_nonempty,
  { exact ⟨0, 1, λ a ha, by norm_num, by simp⟩ },
  obtain ⟨f, s, hf₁, hf₂⟩ := geometric_hahn_banach_open hs₁ hs₂ ht₁ disj,
  have hf : is_open_map f,
  { refine f.is_open_map_of_ne_zero _,
    rintro rfl,
    exact (hf₁ _ ha₀).not_le (hf₂ _ hb₀) },
  refine ⟨f, s, hf₁, image_subset_iff.1 (_ : f '' t ⊆ Ioi s)⟩,
  rw ←interior_Ici,
  refine interior_maximal (image_subset_iff.2 hf₂) (f.is_open_map_of_ne_zero _ _ ht₃),
  rintro rfl,
  exact (hf₁ _ ha₀).not_le (hf₂ _ hb₀),
end

variables [locally_convex_space ℝ E]

/-- A version of the **Hahn-Banach theorem**: given disjoint convex sets `s`, `t` where `s` is
compact and `t` is closed, there is a continuous linear functional which strongly separates them. -/
theorem geometric_hahn_banach_compact_closed (hs₁ : convex ℝ s) (hs₂ : is_compact s)
  (ht₁ : convex ℝ t) (ht₂ : is_closed t) (disj : disjoint s t) :
  ∃ (f : E →L[ℝ] ℝ) (u v : ℝ), (∀ a ∈ s, f a < u) ∧ u < v ∧ ∀ b ∈ t, v < f b :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { exact ⟨0, -2, -1, by simp, by norm_num, λ b hb, by norm_num⟩ },
  unfreezingI { obtain rfl | ht := t.eq_empty_or_nonempty },
  { exact ⟨0, 1, 2, λ a ha, by norm_num, by norm_num, by simp⟩ },
  obtain ⟨U, V, hU, hV, hU₁, hV₁, sU, tV, disj'⟩ := disj.exists_open_convexes hs₁ hs₂ ht₁ ht₂,
  obtain ⟨f, u, hf₁, hf₂⟩ := geometric_hahn_banach_open_open hU₁ hU hV₁ hV disj',
  obtain ⟨x, hx₁, hx₂⟩ := hs₂.exists_forall_ge hs f.continuous.continuous_on,
  have : f x < u := hf₁ x (sU hx₁),
  exact ⟨f, (f x + u)/2, u, λ a ha, by linarith [hx₂ a ha], by linarith, λ b hb, hf₂ b (tV hb)⟩,
end

/-- A version of the **Hahn-Banach theorem**: given disjoint convex sets `s`, `t` where `s` is
closed, and `t` is compact, there is a continuous linear functional which strongly separates them.
-/
theorem geometric_hahn_banach_closed_compact (hs₁ : convex ℝ s) (hs₂ : is_closed s)
  (ht₁ : convex ℝ t) (ht₂ : is_compact t) (disj : disjoint s t) :
  ∃ (f : E →L[ℝ] ℝ) (u v : ℝ), (∀ a ∈ s, f a < u) ∧ u < v ∧ ∀ b ∈ t, v < f b :=
let ⟨f, s, t, hs, st, ht⟩ := geometric_hahn_banach_compact_closed ht₁ ht₂ hs₁ hs₂ disj.symm in
⟨-f, -t, -s, by simpa using ht, by simpa using st, by simpa using hs⟩

theorem geometric_hahn_banach_point_closed (ht₁ : convex ℝ t) (ht₂ : is_closed t) (disj : x ∉ t) :
  ∃ (f : E →L[ℝ] ℝ) (u : ℝ), f x < u ∧ ∀ b ∈ t, u < f b :=
let ⟨f, u, v, ha, hst, hb⟩ := geometric_hahn_banach_compact_closed (convex_singleton x)
  is_compact_singleton ht₁ ht₂ (disjoint_singleton_left.2 disj)
  in ⟨f, v, hst.trans' $ ha x $ mem_singleton _, hb⟩

theorem geometric_hahn_banach_closed_point (hs₁ : convex ℝ s) (hs₂ : is_closed s) (disj : x ∉ s) :
  ∃ (f : E →L[ℝ] ℝ) (u : ℝ), (∀ a ∈ s, f a < u) ∧ u < f x :=
let ⟨f, s, t, ha, hst, hb⟩ := geometric_hahn_banach_closed_compact hs₁ hs₂ (convex_singleton x)
  is_compact_singleton (disjoint_singleton_right.2 disj)
  in ⟨f, s, ha, hst.trans $ hb x $ mem_singleton _⟩

/-- See also `normed_space.eq_iff_forall_dual_eq`. -/
theorem geometric_hahn_banach_point_point [t1_space E] (hxy : x ≠ y) :
  ∃ (f : E →L[ℝ] ℝ), f x < f y :=
begin
  obtain ⟨f, s, t, hs, st, ht⟩ :=
    geometric_hahn_banach_compact_closed (convex_singleton x) is_compact_singleton
      (convex_singleton y) is_closed_singleton (disjoint_singleton.2 hxy),
  exact ⟨f, by linarith [hs x rfl, ht y rfl]⟩,
end

/-- A closed convex set is the intersection of the halfspaces containing it. -/
lemma Inter_halfspaces_eq (hs₁ : convex ℝ s) (hs₂ : is_closed s) :
  (⋂ (l : E →L[ℝ] ℝ), {x | ∃ y ∈ s, l x ≤ l y}) = s :=
begin
  rw set.Inter_set_of,
  refine set.subset.antisymm (λ x hx, _) (λ x hx l, ⟨x, hx, le_rfl⟩),
  by_contra,
  obtain ⟨l, s, hlA, hl⟩ := geometric_hahn_banach_closed_point hs₁ hs₂ h,
  obtain ⟨y, hy, hxy⟩ := hx l,
  exact ((hxy.trans_lt (hlA y hy)).trans hl).not_le le_rfl,
end
