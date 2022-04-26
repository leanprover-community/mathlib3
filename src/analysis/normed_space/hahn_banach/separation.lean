/-
Copyright (c) 2022 Bhavik Mehta All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Yaël Dillies
-/
import analysis.convex.cone
import analysis.convex.topology
import analysis.normed.group.pointwise
import analysis.seminorm
import tactic.by_contra

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
* `0 < δ → convex ℝ s → interior (cthickening δ s) = thickening δ s`
-/

open function metric set
open_locale pointwise

variables {𝕜 E : Type*}

section
open filter
open_locale topological_space

lemma linear_map.exists_ne_zero {R₁ R₂ : Type*} [semiring R₁] [semiring R₂] {σ₁₂ : R₁ →+* R₂}
  {M₁ : Type*} [add_comm_monoid M₁] {M₂ : Type*} [add_comm_monoid M₂] [module R₁ M₁] [module R₂ M₂]
  {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : f ≠ 0) :
  ∃ x, f x ≠ 0 :=
by { by_contra' h, exact hf (linear_map.ext h) }

lemma continuous_linear_map.exists_ne_zero {R₁ R₂ : Type*} [semiring R₁]
  [semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type*} [topological_space M₁] [add_comm_monoid M₁]
  {M₂ : Type*} [topological_space M₂] [add_comm_monoid M₂] [module R₁ M₁] [module R₂ M₂]
  {f : M₁ →SL[σ₁₂] M₂} (hf : f ≠ 0) :
  ∃ x, f x ≠ 0 :=
by { by_contra' h, exact hf (continuous_linear_map.ext h) }

lemma nhds_le_map_nhds [topological_space 𝕜] [topological_space E] {f : E → 𝕜} {g : 𝕜 → E} {a : E}
  (hg : continuous_at g (f a)) (hcomp : f ∘ g = id) (hgfa : g (f a) = a) :
  𝓝 (f a) ≤ map f (𝓝 a) :=
calc 𝓝 (f a) = ((𝓝 (f a)).map g).map f : by rw [map_map, hcomp, map_id]
  ... ≤ (𝓝 $ g (f a)).map f             : map_mono hg
  ... = (𝓝 a).map f                     : by rw hgfa

lemma linear_map.nhds_le_map_nhds [topological_space 𝕜] [division_ring 𝕜] [topological_ring 𝕜]
  [add_comm_group E] [topological_space E] [topological_add_group E] [module 𝕜 E]
  [has_continuous_smul 𝕜 E] {f : E →ₗ[𝕜] 𝕜} (hf : f ≠ 0) (a : E) :
  𝓝 (f a) ≤ map f (𝓝 a) :=
begin
  obtain ⟨x₀, hx₀⟩ := linear_map.exists_ne_zero hf,
  let g : 𝕜 → E := λ x, a + (x - f a) • (f x₀)⁻¹ • x₀,
  have hg : continuous g, by continuity,
  have hcomp : f ∘ g = id, by { ext, simp [hx₀] },
  have hgfa : g (f a) = a, by simp [hx₀],
  exact nhds_le_map_nhds hg.continuous_at hcomp hgfa,
end

/-- A nonzero continuous linear functional is open. -/
lemma continuous_linear_map.is_open_map [topological_space 𝕜] [division_ring 𝕜]
  [topological_ring 𝕜] [add_comm_group E] [topological_space E] [topological_add_group E]
  [module 𝕜 E] [has_continuous_smul 𝕜 E] (f : E →L[𝕜] 𝕜) (hf : f ≠ 0) :
  is_open_map f :=
begin
  refine is_open_map.of_nhds_le (λ a, _),
  obtain ⟨x₀, hx₀⟩ := continuous_linear_map.exists_ne_zero hf,
  let g : 𝕜 → E := λ x, a + (x - f a) • (f x₀)⁻¹ • x₀,
  have hg : continuous g, by continuity,
  have hcomp : f ∘ g = id, by { ext, simp [hx₀] },
  have hgfa : g (f a) = a, by simp [hx₀],
  exact nhds_le_map_nhds hg.continuous_at hcomp hgfa,
end

variables [normed_group E] [normed_space ℝ E]

lemma seminorm.exists_extension (f : linear_pmap ℝ E ℝ) (p : seminorm ℝ E)
  (hf : ∀ x : f.domain, f x ≤ p x) :
  ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ p x :=
exists_extension_of_le_sublinear f p (λ c hc x, by rw [p.smul, real.norm_of_nonneg hc.le])
  p.triangle hf

/-- Given a set `s` which is a convex neighbourhood of `0` and a point `x₀` outside of it, there is
a continuous linear functional `f` separating `x₀` and `s`, in the sense that it sends `x₀` to 1 and
all of `s` to values strictly below `1`. -/
lemma separate_convex_open_set {s : set E} (hs₀ : (0 : E) ∈ s) (hs₁ : convex ℝ s)
  (hs₂ : is_open s) {x₀ : E} (hx₀ : x₀ ∉ s) :
  ∃ f : E →L[ℝ] ℝ, f x₀ = 1 ∧ ∀ x ∈ s, f x < 1 :=
begin
  let f : linear_pmap ℝ E ℝ :=
    linear_pmap.mk_span_singleton x₀ 1 (ne_of_mem_of_not_mem hs₀ hx₀).symm,
  obtain ⟨r, hr, hrs⟩ := metric.mem_nhds_iff.1
    (inter_mem (hs₂.mem_nhds hs₀) $ hs₂.neg.mem_nhds $ by rwa [mem_neg, neg_zero]),
  obtain ⟨φ, hφ₁, hφ₂⟩ := exists_extension_of_le_sublinear f (gauge s)
    (λ c hc, gauge_smul_of_nonneg hc.le)
    (gauge_add_le hs₁ $ absorbent_nhds_zero $ hs₂.mem_nhds hs₀) _,
  { refine ⟨φ.mk_continuous (r⁻¹) $ λ x, _, _, _⟩,
    { rw [real.norm_eq_abs, abs_le, neg_le, ←linear_map.map_neg],
      nth_rewrite 0 ←norm_neg x,
      suffices : ∀ x, φ x ≤ r⁻¹ * ∥x∥,
      { exact ⟨this _, this _⟩ },
      refine λ x, (hφ₂ _).trans _,
      rw [←div_eq_inv_mul, ←gauge_ball hr],
      exact gauge_mono (absorbent_ball_zero hr) (hrs.trans $ inter_subset_left _ _) x },
    { dsimp,
      rw [←submodule.coe_mk x₀ (submodule.mem_span_singleton_self _), hφ₁,
        linear_pmap.mk_span_singleton_apply_self] },
    { exact λ x hx, (hφ₂ x).trans_lt (gauge_lt_one_of_mem_of_open hs₁ hs₀ hs₂ hx) } },
  { rintro ⟨x, hx⟩,
    obtain ⟨y, rfl⟩ := submodule.mem_span_singleton.1 hx,
    rw linear_pmap.mk_span_singleton_apply,
    simp only [mul_one, algebra.id.smul_eq_mul, submodule.coe_mk],
    obtain h | h := le_or_lt y 0,
    { exact h.trans (gauge_nonneg _) },
    { rw [gauge_smul_of_nonneg h.le, smul_eq_mul, le_mul_iff_one_le_right h],
      exact one_le_gauge_of_not_mem (hs₁.star_convex hs₀)
        ((absorbent_ball_zero hr).subset $ hrs.trans $ inter_subset_left _ _).absorbs hx₀,
      apply_instance } }
end

end

variables [normed_group E] [normed_space ℝ E] {s t : set E} {x : E}

/-- A version of the Hahn-Banach theorem: given disjoint convex sets `s`, `t` where `s` is open,
there is a continuous linear functional which separates them. -/
theorem geometric_hahn_banach_open (hs₁ : convex ℝ s) (hs₂ : is_open s) (ht : convex ℝ t)
  (disj : disjoint s t) :
  ∃ (f : E →L[ℝ] ℝ) (u : ℝ), (∀ a ∈ s, f a < u) ∧ ∀ b ∈ t, u ≤ f b :=
begin
  obtain rfl | ⟨a₀, ha₀⟩ := s.eq_empty_or_nonempty,
  { exact ⟨0, 0, by simp, λ b hb, by simp⟩ },
  obtain rfl | ⟨b₀, hb₀⟩ := t.eq_empty_or_nonempty,
  { exact ⟨0, 1, λ a ha, by norm_num, by simp⟩ },
  let x₀ := b₀ - a₀,
  let C := {x₀} + s + -t,
  have : (0:E) ∈ C := ⟨_ + a₀, -b₀, add_mem_add rfl ha₀, neg_mem_neg.2 hb₀, by simp⟩,
  have : convex ℝ C := ((convex_singleton _).add hs₁).add ht.neg_preimage,
  have : x₀ ∉ C,
  { intro hx₀,
    simp only [mem_add, mem_singleton_iff, mem_neg, exists_eq_left, exists_exists_and_eq_and,
      exists_and_distrib_left, add_assoc x₀, add_right_eq_self] at hx₀,
    obtain ⟨a, ha, b, hb, hab⟩ := hx₀,
    rw ←eq_neg_of_add_eq_zero hab at hb,
    exact disj ⟨ha, hb⟩ },
  obtain ⟨f, hf₁, hf₂⟩ := separate_convex_open_set ‹0 ∈ C› ‹_› hs₂.add_left.add_right ‹x₀ ∉ C›,
  have : f b₀ = f a₀ + 1,
  { simp [←hf₁] },
  have forall_lt : ∀ (a ∈ s) (b ∈ t), f a < f b,
  { intros a ha b hb,
    have := hf₂ (x₀ + a + -b) (add_mem_add (add_mem_add rfl ha) (neg_mem_neg.2 hb)),
    simp only [f.map_neg, f.map_add, f.map_sub, hf₁] at this,
    linarith },
  refine ⟨f, Inf (f '' t), _, _⟩,
  { suffices : f '' s ⊆ Iio (Inf (f '' t)),
    { intros a ha,
      apply this ⟨_, ha, rfl⟩ },
    rw ←interior_Iic,
    apply interior_maximal,
    { rintro _ ⟨a, ha, rfl⟩,
      apply le_cInf ⟨f b₀, _⟩,
      { rintro _ ⟨b', hb, rfl⟩,
        exact (forall_lt _ ha _ hb).le },
      { exact mem_image_of_mem _ hb₀ } },
    refine f.is_open_map _ _ hs₂,
    rintro rfl,
    simpa using hf₁ },
  { intros b hb,
    apply cInf_le ⟨f a₀, _⟩ (mem_image_of_mem _ hb),
    rintro _ ⟨b', hb', rfl⟩,
    exact (forall_lt _ ha₀ _ hb').le },
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
  have : f ≠ 0,
  { rintro rfl,
    exact (hf₁ _ ha₀).not_le (hf₂ _ hb₀) },
  have : is_open_map f := f.is_open_map this,
  refine ⟨f, s, hf₁, _⟩,
  suffices : f '' t ⊆ Ioi s,
  { exact λ b hb, this ⟨b, ‹_›, rfl⟩ },
  rw ←interior_Ici,
  refine interior_maximal _ (this _ ht₃),
  rintro _ ⟨_, _, rfl⟩,
  exact hf₂ _ ‹_›,
end

open filter
open_locale topological_space

/-- A version of the Hahn-Banach theorem: given disjoint convex sets `s`, `t` where `s` is compact
and `t` is closed, there is a continuous linear functional which strongly separates them. -/
theorem geometric_hahn_banach_compact_closed {s t : set E} (hs₁ : convex ℝ s) (hs₂ : is_compact s)
  (ht₁ : convex ℝ t) (ht₂ : is_closed t) (disj : disjoint s t) :
  ∃ (f : E →L[ℝ] ℝ) (u v : ℝ), (∀ a ∈ s, f a < u) ∧ u < v ∧ ∀ b ∈ t, v < f b :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { exact ⟨0, -2, -1, by simp, by norm_num, λ b hb, by norm_num⟩ },
  tactic.unfreeze_local_instances,
  obtain rfl | ht := t.eq_empty_or_nonempty,
  { exact ⟨0, 1, 2, λ a ha, by norm_num, by norm_num, by simp⟩ },
  obtain ⟨U, V, hU, hV, hU₁, hV₁, sU, tV, disj'⟩ :=
    exists_disjoint_open_convexes hs₁ hs₂ ht₁ ht₂ disj,
  obtain ⟨f, u, hf₁, hf₂⟩ := geometric_hahn_banach_open_open hU₁ hU hV₁ hV disj',
  obtain ⟨x, hx₁, hx₂⟩ := hs₂.exists_forall_ge hs f.continuous.continuous_on,
  have : Sup (f '' s) = f x,
  { apply le_antisymm (cSup_le (hs.image f) (by simpa)),
    exact le_cSup ⟨f x, by simpa [upper_bounds]⟩ ⟨_, hx₁, rfl⟩ },
  have : f x < u := hf₁ x (sU hx₁),
  exact ⟨f, (f x + u)/2, u, λ a ha, by linarith [hx₂ a ha], by linarith, λ b hb, hf₂ b (tV hb)⟩,
end

/-- A version of the Hahn-Banach theorem: given disjoint convex sets `s`, `t` where `s` is closed,
and `t` is compact, there is a continuous linear functional which strongly separates them. -/
theorem geometric_hahn_banach_closed_compact (hs₁ : convex ℝ s) (hs₂ : is_closed s)
  (ht₁ : convex ℝ t) (ht₂ : is_compact t) (disj : disjoint s t) :
  ∃ (f : E →L[ℝ] ℝ) (u v : ℝ), (∀ a ∈ s, f a < u) ∧ u < v ∧ ∀ b ∈ t, v < f b :=
let ⟨f, s, t, hs, st, ht⟩ := geometric_hahn_banach_compact_closed ht₁ ht₂ hs₁ hs₂ disj.symm in
⟨-f, -t, -s, by simpa using ht, by simpa using st, by simpa using hs⟩

theorem geometric_hahn_banach_point_closed (ht₁ : convex ℝ t) (ht₂ : is_closed t) (disj : x ∉ t) :
  ∃ (f : E →L[ℝ] ℝ) (u : ℝ), f x < u ∧ ∀ b ∈ t, u < f b :=
let ⟨f, u, v, ha, hst, hb⟩ := geometric_hahn_banach_compact_closed (convex_singleton x)
  is_compact_singleton ht₁ ht₂ (disjoint_singleton_left.2 disj)
  in ⟨f, v, lt_trans (ha x (mem_singleton _)) hst, hb⟩

theorem geometric_hahn_banach_closed_point {s : set E} {x : E} (hs₁ : convex ℝ s)
  (hs₂ : is_closed s) (disj : x ∉ s) :
  ∃ (f : E →L[ℝ] ℝ) (u : ℝ), (∀ a ∈ s, f a < u) ∧ u < f x :=
let ⟨f, s, t, ha, hst, hb⟩ := geometric_hahn_banach_closed_compact hs₁ hs₂ (convex_singleton x)
  is_compact_singleton (disjoint_singleton_right.2 disj)
  in ⟨f, s, ha, lt_trans hst (hb x (mem_singleton _))⟩

theorem geometric_hahn_banach_point_point {x y : E} (hxy : x ≠ y) : ∃ (f : E →L[ℝ] ℝ), f x < f y :=
begin
  obtain ⟨f, s, t, hs, st, ht⟩ :=
    geometric_hahn_banach_compact_closed (convex_singleton x) is_compact_singleton
      (convex_singleton y) is_closed_singleton (disjoint_singleton.2 hxy),
  exact ⟨f, by linarith [hs x rfl, ht y rfl]⟩,
end
