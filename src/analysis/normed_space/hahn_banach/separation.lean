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
-/

open function set
open_locale pointwise

variables {𝕜 E : Type*}

namespace set
variables {α : Type*}

@[to_additive]
lemma bUnion_mul {ι : Sort*} [has_mul α] (f : ι → set α) (s : set ι) (t : set α) :
  (⋃ i ∈ s, f i) * t = ⋃ i ∈ s, (f i * t) :=
by simp_rw [Union_mul]

@[to_additive]
lemma mul_bUnion {ι : Sort*} [has_mul α] (f : ι → set α) (s : set ι) (t : set α) :
  t * (⋃ i ∈ s, f i) = ⋃ i ∈ s, (t * f i) :=
by simp_rw [mul_Union]

end set

open set

namespace metric
section
variables [pseudo_metric_space E]

open filter
open_locale topological_space

lemma exists_disjoint_thickenings {s t : set E} (hs : is_compact s) (ht : is_closed t)
  (hst : disjoint s t) :
  ∃ ε, 0 < ε ∧ disjoint (thickening ε s) (thickening ε t) :=
begin
  obtain ⟨u, -, u_pos, u_lim⟩ := exists_seq_strict_anti_tendsto (0 : ℝ),
  suffices h : ∃ (n : ℕ), disjoint (thickening (u n) s) (thickening (u n) t),
  { obtain ⟨n, hn⟩ := h,
    exact ⟨u n, u_pos n, hn⟩ },
  by_contra' h,
  -- have := hs.exists_forall_le,
  simp only [not_disjoint_iff, mem_thickening_iff,
    ← exists_and_distrib_left, ← exists_and_distrib_right, and_assoc] at h,
  choose x y hy z hz hxy hxz using h,
  obtain ⟨w, hw, φ, hφ, hyφ : tendsto (y ∘ _) _ _⟩ := hs.tendsto_subseq hy,
  have h : ∀ n, dist (y n) (z n) ≤ u n + u n,
    from λ n, (dist_triangle_left _ _ _).trans (add_le_add (hxy n).le (hxz n).le),
  refine hst ⟨hw, mem_of_is_closed_sequential ht (λ n, hz (φ n)) $ (tendsto_iff_of_dist _).1 hyφ⟩,
  refine squeeze_zero (λ _, dist_nonneg) (λ n, h _) _,
  simp_rw ←two_mul,
  rw ←mul_zero (2 : ℝ),
  exact (u_lim.const_mul (2 : ℝ)).comp hφ.tendsto_at_top,
end

end

variables [semi_normed_group E]

@[simp] lemma add_ball (s : set E) (ε : ℝ) : s + ball 0 ε = thickening ε s :=
begin
  rw thickening_eq_bUnion_ball,
  convert bUnion_add _ s (ball (0 : E) ε),
  exact s.bUnion_of_singleton.symm,
  ext x y,
  simp_rw [singleton_add_ball, add_zero],
end

@[simp] lemma ball_add (s : set E) (ε : ℝ) : ball 0 ε + s = thickening ε s :=
by rw [add_comm, add_ball]


variables (𝕜 E) [normed_field 𝕜] [semi_normed_space 𝕜 E] {r : ℝ}

/-- The norm of a seminormed group as a seminorm. -/
def _root_.norm_seminorm : seminorm 𝕜 E :=
{ to_fun := norm,
  smul' := norm_smul,
  triangle' := norm_add_le }

@[simp] lemma _root_.coe_norm_seminorm : ⇑(norm_seminorm 𝕜 E) = norm := rfl

@[simp] lemma _root_.ball_norm_seminorm : (norm_seminorm 𝕜 E).ball = ball :=
by { ext x r y, simp only [seminorm.mem_ball, mem_ball, coe_norm_seminorm, dist_eq_norm] }

variables {𝕜 E}

/-- Balls at the origin are absorbent. -/
lemma absorbent_ball_zero (hr : 0 < r) : absorbent 𝕜 (ball (0 : E) r) :=
by { convert (norm_seminorm _ _).absorbent_ball_zero hr, rw ball_norm_seminorm }

/-- Balls containing the origin are absorbent. -/
lemma absorbent_ball {x : E} (hx : ∥x∥ < r) : absorbent 𝕜 (ball x r) :=
by { convert (norm_seminorm _ _).absorbent_ball hx, rw ball_norm_seminorm }

end metric

open metric

lemma convex.thickening [normed_group E] [normed_space ℝ E] {s : set E} (hs : convex ℝ s) (ε : ℝ) :
  convex ℝ (thickening ε s) :=
by { rw ←add_ball, exact hs.add (convex_ball 0 _) }

lemma convex.cthickening [normed_group E] [normed_space ℝ E] {s : set E} (hs : convex ℝ s) (ε : ℝ) :
  convex ℝ (cthickening ε s) :=
begin
  obtain hε | hε := le_total 0 ε,
  { rw cthickening_eq_Inter_thickening hε,
    exact convex_bInter (λ _ _, hs.thickening _) },
  { rw cthickening_of_nonpos hε,
    exact hs.closure }
end

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

/-- Given a set `C` which is a convex neighbourhood of `0` and a point `x₀` outside of it, there is
a continuous linear functional `f` separating `x₀` and `C`, in the sense that it sends `x₀` to 1 and
all of `C` to values strictly below `1`. -/
lemma separate_convex_open_set {C : set E} (hC₀ : (0:E) ∈ C) (hC₁ : convex ℝ C)
  (hC₂ : is_open C) {x₀ : E} (hx₀ : x₀ ∉ C) :
  ∃ (f : E →L[ℝ] ℝ), f x₀ = 1 ∧ ∀ x ∈ C, f x < 1 :=
begin
  let f : linear_pmap ℝ E ℝ :=
    linear_pmap.mk_span_singleton x₀ 1 (ne_of_mem_of_not_mem hC₀ hx₀).symm,
  have hfx₀ : f ⟨(1:ℝ) • x₀, by { dsimp, rw submodule.mem_span_singleton, exact ⟨1, rfl⟩ }⟩ = 1,
  { simp_rw [linear_pmap.mk_span_singleton_apply, one_smul] },
  have : C ∩ (-C) ∈ 𝓝 (0:E),
    from inter_mem (hC₂.mem_nhds hC₀) (hC₂.neg.mem_nhds $ by rwa [mem_neg, neg_zero]),
  obtain ⟨r, hr, hrC⟩ := metric.mem_nhds_iff.1 this,
  have hC₀' : ∀ x, x ∈ C ∩ -C → -x ∈ C ∩ -C := λ x h,
    by rwa [←mem_neg, inter_neg, set.neg_neg, inter_comm],
  have hC₁' : convex ℝ (C ∩ -C) := hC₁.inter hC₁.neg,
  obtain ⟨φ, hφ₁, hφ₂⟩ := (gauge_seminorm hC₀' hC₁' $
    (absorbent_ball_zero hr).subset hrC).exists_extension f _,
  { refine ⟨φ.mk_continuous (r⁻¹) _, _, _⟩,
    { intros x,
      rw [real.norm_eq_abs, abs_le, neg_le, ←linear_map.map_neg],
      split; apply (hφ₂ _).trans _,
      { sorry },
      { sorry } },
    { dsimp,
      have : x₀ ∈ f.domain := submodule.mem_span_singleton_self _,
      rw [←submodule.coe_mk x₀ this, hφ₁, ←hfx₀],
      congr,
      rw one_smul },
    { exact λ x hx, (hφ₂ x).trans_lt (gauge_lt_one_of_mem_of_open hC zero_mem hC₂ _ hx) } },
  { rintro ⟨x, hx⟩,
    obtain ⟨y, rfl⟩ := submodule.mem_span_singleton.1 hx,
    rw linear_pmap.mk_span_singleton_apply,
    simp only [mul_one, algebra.id.smul_eq_mul, submodule.coe_mk],
    obtain h | h := le_or_lt y 0,
    { exact h.trans (gauge_nonneg _) },
    { rw [seminorm.smul, real.norm_of_nonneg h.le, le_mul_iff_one_le_right h],
      exact one_le_gauge_of_not_mem hC₁' hC₀' hC₂ hx₀,
      apply_instance } }
end

/-- Given a set `C` which is a convex neighbourhood of `0` and a point `x₀` outside of it, there is
a continuous linear functional `f` separating `x₀` and `C`, in the sense that it sends `x₀` to 1 and
all of `C` to values strictly below `1`. -/
lemma separate_convex_open_set' {C : set E} (zero_mem : (0:E) ∈ C) (hC : convex ℝ C)
  (hC₂ : is_open C) {x₀ : E} (hx₀ : x₀ ∉ C) :
  ∃ (f : E →L[ℝ] ℝ), f x₀ = 1 ∧ ∀ x ∈ C, f x < 1 :=
begin
  let f : linear_pmap ℝ E ℝ :=
    linear_pmap.mk_span_singleton x₀ 1 (ne_of_mem_of_not_mem zero_mem hx₀).symm,
  have hfx₀ : f ⟨(1:ℝ) • x₀, by { dsimp, rw submodule.mem_span_singleton, exact ⟨1, rfl⟩ }⟩ = 1,
  { simp_rw [linear_pmap.mk_span_singleton_apply, one_smul] },
  obtain ⟨φ, hφ₁, hφ₂⟩ := exists_extension_of_le_sublinear f (gauge C) _ _ _,
  { refine ⟨⟨φ, (φ.to_add_monoid_hom.uniform_continuous_of_continuous_at_zero _).continuous⟩, _, _⟩,
    { change tendsto _ _ _,
      rw (nhds_basis_opens (0:E)).tendsto_iff nhds_basis_ball,
      refine λ ε hε, ⟨(ε • C) ∩ (-ε • C), ⟨⟨_, _⟩, _⟩, _⟩,
      { exact mem_smul_set.mpr ⟨0, zero_mem, smul_zero _⟩ },
      { exact mem_smul_set.mpr ⟨0, zero_mem, smul_zero _⟩ },
      { exact (is_open_map_smul₀ hε.ne' _ hC₂).inter
          (is_open_map_smul₀ (neg_ne_zero.mpr hε.ne.symm) _ hC₂) },
      rintro x ⟨hx₁, hx₂⟩,
      have : ∥φ x∥ < ε,
      { rw [real.norm_eq_abs, abs_lt, neg_lt, ←linear_map.map_neg],
        split; apply (hφ₂ _).trans_lt,
        { refine gauge_lt_of_mem_smul (-x) ε hε zero_mem hC hC₂ _,
          rw [mem_smul_set_iff_inv_smul_mem₀ hε.ne', smul_neg],
          rwa [mem_smul_set_iff_inv_smul_mem₀ (neg_ne_zero.mpr hε.ne'), inv_neg, neg_smul] at hx₂ },
        { exact gauge_lt_of_mem_smul x ε hε zero_mem hC hC₂ hx₁ } },
      simp [this] },
    { dsimp,
      have : x₀ ∈ f.domain := submodule.mem_span_singleton_self _,
      rw [←submodule.coe_mk x₀ this, hφ₁, ← hfx₀],
      congr,
      rw one_smul },
    { exact λ x hx, (hφ₂ x).trans_lt (gauge_lt_one_of_mem_of_open hC zero_mem hC₂ _ hx) } },
  { simp_rw ← smul_eq_mul,
    exact λ c hc x, gauge_smul_of_nonneg hc.le x },
  { exact gauge_add_le hC (absorbent_nhds_zero (hC₂.mem_nhds zero_mem)) },
  { rintro ⟨x, hx⟩,
    obtain ⟨y, rfl⟩ := submodule.mem_span_singleton.1 hx,
    rw linear_pmap.mk_span_singleton_apply,
    simp only [mul_one, algebra.id.smul_eq_mul, submodule.coe_mk],
    obtain h | h := le_or_lt y 0,
    { exact h.trans (gauge_nonneg _) },
    { rw [gauge_smul_of_nonneg h.le, smul_eq_mul, le_mul_iff_one_le_right h],
      exact one_le_gauge_of_not_mem hC zero_mem hC₂ hx₀,
      apply_instance } }
end

end

variables [normed_group E] [normed_space ℝ E]

/-- A version of the Hahn-Banach theorem: given disjoint convex sets `A`, `B` where `A` is open,
there is a continuous linear functional which separates them. -/
theorem geometric_hahn_banach_open {A B : set E}
  (hA₁ : convex ℝ A) (hA₂ : is_open A) (hB : convex ℝ B) (disj : disjoint A B) :
  ∃ (f : E →L[ℝ] ℝ) (s : ℝ), (∀ a ∈ A, f a < s) ∧ (∀ b ∈ B, s ≤ f b) :=
begin
  rcases A.eq_empty_or_nonempty with (rfl | ⟨a₀, ha₀⟩),
  { exact ⟨0, 0, by simp, λ b hb, by simp⟩ },
  rcases B.eq_empty_or_nonempty with (rfl | ⟨b₀, hb₀⟩),
  { exact ⟨0, 1, λ a ha, by norm_num, by simp⟩ },
  let x₀ := b₀ - a₀,
  let C := {x₀} + A + -B,
  have : (0:E) ∈ C := ⟨_ + a₀, -b₀, add_mem_add rfl ha₀, neg_mem_neg.2 hb₀, by simp⟩,
  have : convex ℝ C := ((convex_singleton _).add hA₁).add hB.neg_preimage,
  have : x₀ ∉ C,
  { intro hx₀,
    simp only [mem_add, mem_singleton_iff, mem_neg, exists_eq_left, exists_exists_and_eq_and,
      exists_and_distrib_left, add_assoc x₀, add_right_eq_self] at hx₀,
    obtain ⟨a, ha, b, hb, hab⟩ := hx₀,
    rw ←eq_neg_of_add_eq_zero hab at hb,
    exact disj ⟨ha, hb⟩ },
  obtain ⟨f, hf₁, hf₂⟩ := separate_convex_open_set ‹0 ∈ C› ‹_› hA₂.add_left.add_right ‹x₀ ∉ C›,
  have : f b₀ = f a₀ + 1,
  { simp [←hf₁] },
  have forall_lt : ∀ (a ∈ A) (b ∈ B), f a < f b,
  { intros a ha b hb,
    have := hf₂ (x₀ + a + -b) (add_mem_add (add_mem_add rfl ha) (neg_mem_neg.2 hb)),
    simp only [f.map_neg, f.map_add, f.map_sub, hf₁] at this,
    linarith },
  refine ⟨f, Inf (f '' B), _, _⟩,
  { suffices : f '' A ⊆ Iio (Inf (f '' B)),
    { intros a ha,
      apply this ⟨_, ha, rfl⟩ },
    rw ←interior_Iic,
    apply interior_maximal,
    { rintro _ ⟨a, ha, rfl⟩,
      apply le_cInf ⟨f b₀, _⟩,
      { rintro _ ⟨b', hb, rfl⟩,
        exact (forall_lt _ ha _ hb).le },
      { exact mem_image_of_mem _ hb₀ } },
    refine f.is_open_map _ _ hA₂,
    rintro rfl,
    simpa using hf₁ },
  { intros b hb,
    apply cInf_le ⟨f a₀, _⟩ (mem_image_of_mem _ hb),
    rintro _ ⟨b', hb', rfl⟩,
    exact (forall_lt _ ha₀ _ hb').le },
end

theorem geometric_hahn_banach_open_point {A : set E} {x : E} (hA₁ : convex ℝ A) (hA₂ : is_open A)
  (disj : x ∉ A) :
  ∃ (f : E →L[ℝ] ℝ), (∀ a ∈ A, f a < f x) :=
let ⟨f, s, hA, hx⟩ := geometric_hahn_banach_open hA₁ hA₂ (convex_singleton x)
  (disjoint_singleton_right.2 disj)
  in ⟨f, λ a ha, lt_of_lt_of_le (hA a ha) (hx x (mem_singleton _))⟩

theorem geometric_hahn_banach_point_open {x : E} {B : set E} (hB₁ : convex ℝ B) (hB₂ : is_open B)
  (disj : x ∉ B) :
  ∃ (f : E →L[ℝ] ℝ), (∀ b ∈ B, f x < f b) :=
let ⟨f, hf⟩ := geometric_hahn_banach_open_point hB₁ hB₂ disj in ⟨-f, by simpa⟩

theorem geometric_hahn_banach_open_open {A B : set E} (hA₁ : convex ℝ A) (hA₂ : is_open A)
  (hB₁ : convex ℝ B) (hB₃ : is_open B) (disj : disjoint A B) :
  ∃ (f : E →L[ℝ] ℝ) (s : ℝ), (∀ a ∈ A, f a < s) ∧ (∀ b ∈ B, s < f b) :=
begin
  obtain (rfl | ⟨a₀, ha₀⟩) := A.eq_empty_or_nonempty,
  { exact ⟨0, -1, by simp, λ b hb, by norm_num⟩ },
  obtain (rfl | ⟨b₀, hb₀⟩) := B.eq_empty_or_nonempty,
  { exact ⟨0, 1, λ a ha, by norm_num, by simp⟩ },
  obtain ⟨f, s, hf₁, hf₂⟩ := geometric_hahn_banach_open hA₁ hA₂ hB₁ disj,
  have : f ≠ 0,
  { rintro rfl,
    exact (hf₁ _ ha₀).not_le (hf₂ _ hb₀) },
  have : is_open_map f := f.is_open_map this,
  refine ⟨f, s, hf₁, _⟩,
  suffices : f '' B ⊆ Ioi s,
  { exact λ b hb, this ⟨b, ‹_›, rfl⟩ },
  rw ←interior_Ici,
  refine interior_maximal _ (this _ hB₃),
  rintro _ ⟨_, _, rfl⟩,
  exact hf₂ _ ‹_›,
end

open filter
open_locale topological_space

/-- If `A`, `B` are disjoint convex sets, `A` is compact and `B` is closed then we can find open
disjoint convex sets containing them. -/
-- TODO: This proof uses the normed space structure of `E`, but it could work for locally convex
-- topological vector spaces: instead of taking the balls around 0 with radius 1/n, we could show
-- there must be some convex neighbourhood `W` of 0 which make `A + W` and `B + W` disjoint?
theorem closed_compact_separate {A B : set E} (hA₁ : convex ℝ A) (hA₂ : is_compact A)
  (hB₁ : convex ℝ B) (hB₂ : is_closed B) (disj : disjoint A B) :
  ∃ U V, is_open U ∧ is_open V ∧ convex ℝ U ∧ convex ℝ V ∧ A ⊆ U ∧ B ⊆ V ∧ disjoint U V :=
let ⟨ε, hε, hAB⟩ := exists_disjoint_thickenings hA₂ hB₂ disj in
  ⟨_, _, is_open_thickening, is_open_thickening, hA₁.thickening _, hB₁.thickening _,
    self_subset_thickening hε _, self_subset_thickening hε _, hAB⟩

/-- A version of the Hahn-Banach theorem: given disjoint convex sets `A`, `B` where `A` is compact
and `B` is closed, there is a continuous linear functional which strongly separates them. -/
theorem geometric_hahn_banach_compact_closed {A B : set E} (hA₁ : convex ℝ A) (hA₂ : is_compact A)
  (hB₁ : convex ℝ B) (hB₂ : is_closed B) (disj : disjoint A B) :
  ∃ (f : E →L[ℝ] ℝ) (s t : ℝ), (∀ a ∈ A, f a < s) ∧ s < t ∧ (∀ b ∈ B, t < f b) :=
begin
  obtain rfl | hA := A.eq_empty_or_nonempty,
  { exact ⟨0, -2, -1, by simp, by norm_num, λ b hb, by norm_num⟩ },
  tactic.unfreeze_local_instances,
  obtain rfl | hB := B.eq_empty_or_nonempty,
  { exact ⟨0, 1, 2, λ a ha, by norm_num, by norm_num, by simp⟩ },
  obtain ⟨U, V, hU, hV, hU₁, hV₁, AU, BV, disj'⟩ := closed_compact_separate hA₁ hA₂ hB₁ hB₂ disj,
  obtain ⟨f, s, hf₁, hf₂⟩ := geometric_hahn_banach_open_open hU₁ hU hV₁ hV disj',
  obtain ⟨x, hx₁, hx₂⟩ := hA₂.exists_forall_ge hA f.continuous.continuous_on,
  have : Sup (f '' A) = f x,
  { apply le_antisymm (cSup_le (hA.image f) (by simpa)),
    exact le_cSup ⟨f x, by simpa [upper_bounds]⟩ ⟨_, hx₁, rfl⟩ },
  have : f x < s := hf₁ x (AU hx₁),
  exact ⟨f, (f x + s)/2, s, λ a ha, by linarith [hx₂ a ha], by linarith, λ b hb, hf₂ b (BV hb)⟩,
end

/-- A version of the Hahn-Banach theorem: given disjoint convex subsets `A,B` where `A` is closed,
and `B` is compact, there is a continuous linear functional which strongly separates them. -/
theorem geometric_hahn_banach_closed_compact {A B : set E} (hA₁ : convex ℝ A) (hA₂ : is_closed A)
  (hB₁ : convex ℝ B) (hB₂ : is_compact B) (disj : disjoint A B) :
  ∃ (f : E →L[ℝ] ℝ) (s t : ℝ), (∀ a ∈ A, f a < s) ∧ s < t ∧ (∀ b ∈ B, t < f b) :=
let ⟨f, s, t, hs, st, ht⟩ := geometric_hahn_banach_compact_closed hB₁ hB₂ hA₁ hA₂ disj.symm in
⟨-f, -t, -s, by simpa using ht, by simpa using st, by simpa using hs⟩

theorem geometric_hahn_banach_point_closed {x : E} {B : set E} (hB₁ : convex ℝ B)
  (hB₂ : is_closed B) (disj : x ∉ B) :
  ∃ (f : E →L[ℝ] ℝ) (s : ℝ), f x < s ∧ (∀ b ∈ B, s < f b) :=
let ⟨f, s, t, ha, hst, hb⟩ := geometric_hahn_banach_compact_closed (convex_singleton x)
  is_compact_singleton hB₁ hB₂ (disjoint_singleton_left.2 disj)
  in ⟨f, t, lt_trans (ha x (mem_singleton _)) hst, hb⟩

theorem geometric_hahn_banach_closed_point {A : set E} {x : E} (hA₁ : convex ℝ A)
  (hA₂ : is_closed A) (disj : x ∉ A) :
  ∃ (f : E →L[ℝ] ℝ) (s : ℝ), (∀ a ∈ A, f a < s) ∧ s < f x :=
let ⟨f, s, t, ha, hst, hb⟩ := geometric_hahn_banach_closed_compact hA₁ hA₂ (convex_singleton x)
  is_compact_singleton (disjoint_singleton_right.2 disj)
  in ⟨f, s, ha, lt_trans hst (hb x (mem_singleton _))⟩

theorem geometric_hahn_banach_point_point {x y : E} (hxy : x ≠ y) : ∃ (f : E →L[ℝ] ℝ), f x < f y :=
begin
  obtain ⟨f, s, t, hs, st, ht⟩ :=
    geometric_hahn_banach_compact_closed (convex_singleton x) is_compact_singleton
      (convex_singleton y) is_closed_singleton (disjoint_singleton.2 hxy),
  exact ⟨f, by linarith [hs x rfl, ht y rfl]⟩,
end
