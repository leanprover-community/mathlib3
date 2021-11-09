/-
Copyright (c) 2021 Bhavik Mehta All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Yaël Dillies
-/
import analysis.convex.cone
import analysis.convex.topology
import analysis.seminorm

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

open set
open_locale pointwise

variables {E : Type*} [normed_group E] [normed_space ℝ E]

lemma continuous_at_of_exists_open (f : E →ₗ[ℝ] ℝ)
  (hf : ∀ ε, 0 < ε → ∃ (U : set E), (0:E) ∈ U ∧ is_open U ∧ ∀ x ∈ U, ∥f x∥ < ε) :
  continuous_at f (0:E) :=
begin
  intros U hU,
  rw metric.nhds_basis_ball.1 at hU,
  rcases hU with ⟨ε, hε₁, hε₂⟩,
  simp only [linear_map.map_zero] at hε₂,
  simp only [filter.mem_map],
  obtain ⟨V, hV₁, hV₂, hV₃⟩ := hf ε hε₁,
  rw mem_nhds_iff,
  refine ⟨V, λ x hx, hε₂ _, hV₂, hV₁⟩,
  simp only [metric.mem_ball, dist_zero_right],
  apply hV₃ _ hx,
end

/-- Given a set `C` which is a convex neighbourhood of `0` and a point `x₀` outside of it, there is
a continuous linear functional `f` separating `x₀` and `C`, in the sense that it sends `x₀` to 1 and
all of `C` to values strictly below `1`. -/
lemma separate_convex_open_set {C : set E} (zero_mem : (0:E) ∈ C) (hC : convex ℝ C)
  (hC₂ : is_open C) {x₀ : E} (hx₀ : x₀ ∉ C) :
  ∃ (f : E →L[ℝ] ℝ), f x₀ = 1 ∧ ∀ x ∈ C, f x < 1 :=
begin
  let f : linear_pmap ℝ E ℝ :=
    linear_pmap.mk_span_singleton x₀ 1 (ne_of_mem_of_not_mem zero_mem hx₀).symm,
  have : f ⟨(1:ℝ) • x₀, by { dsimp, rw submodule.mem_span_singleton, refine ⟨1, rfl⟩ }⟩ = 1,
  { change linear_pmap.mk_span_singleton _ _ _ _ = _,
    rw [linear_pmap.mk_span_singleton_apply, one_smul] },
  rcases exists_extension_of_le_sublinear f (gauge C) _ _ _ with ⟨φ, hφ₁, hφ₂⟩,
  { refine ⟨⟨φ, (φ.to_add_monoid_hom.uniform_continuous_of_continuous_at_zero _).continuous⟩, _, _⟩,
    { refine continuous_at_of_exists_open _ (λ ε hε, ⟨(ε • C) ∩ (-ε • C), ⟨_, _⟩, _, _⟩),
      { rw mem_smul_set,
        exact ⟨0, zero_mem, by rw smul_zero⟩ },
      { rw mem_smul_set,
        exact ⟨0, zero_mem, by rw smul_zero⟩ },
      { apply is_open.inter (is_open_map_smul₀ hε.ne' _ hC₂),
        { exact is_open_map_smul₀ (by linarith) _ hC₂ } },
      rintro x ⟨hx₁, hx₂⟩,
      rw [real.norm_eq_abs, abs_lt],
      split,
      { rw [neg_lt, ←linear_map.map_neg],
        apply (hφ₂ _).trans_lt,
        have : -ε⁻¹ • x ∈ C,
        { obtain ⟨y, _, rfl⟩ := hx₂,
          simpa [smul_smul, hε.ne'] },
        have := gauge_lt_one_of_mem_of_open hC zero_mem hC₂ (-ε⁻¹ • x) ‹_ ∈ C›,
        rwa [neg_smul, ←smul_neg, gauge_smul_of_nonneg (inv_nonneg.2 hε.le), smul_eq_mul,
          inv_mul_lt_iff hε, mul_one] at this,
        apply_instance },
      { have : ε⁻¹ • x ∈ C,
        { rwa ←mem_smul_set_iff_inv_smul_mem₀ hε.ne' },
        have := gauge_lt_one_of_mem_of_open hC zero_mem hC₂ (ε⁻¹ • x) ‹_›,
        rw [gauge_smul_of_nonneg (inv_nonneg.2 hε.le), smul_eq_mul, inv_mul_lt_iff hε, mul_one]
          at this,
        exact (hφ₂ _).trans_lt ‹_›,
        apply_instance } },
    { dsimp,
      have : x₀ ∈ f.domain := submodule.mem_span_singleton_self _,
      rw [←submodule.coe_mk x₀ this, hφ₁],
      convert linear_pmap.mk_span_singleton_apply x₀ (1 : ℝ) _ (1 : ℝ) _; rw one_smul,
      exact this },
    { exact λ x hx, (hφ₂ x).trans_lt (gauge_lt_one_of_mem_of_open hC zero_mem hC₂ _ hx) } },
  { rintro c hc x,
    rw [gauge_smul_of_nonneg (le_of_lt hc), smul_eq_mul],
    apply_instance },
  { exact gauge_add_le hC (absorbent_nhds_zero (hC₂.mem_nhds zero_mem)) },
  { rintro ⟨x, hx⟩,
    obtain ⟨y, rfl⟩ := submodule.mem_span_singleton.1 hx,
    rw linear_pmap.mk_span_singleton_apply,
    simp only [mul_one, algebra.id.smul_eq_mul, submodule.coe_mk],
    cases lt_or_le 0 y with h h,
    { rw [gauge_smul_of_nonneg h.le, smul_eq_mul, le_mul_iff_one_le_right h],
      exact one_le_gauge_of_not_mem hC zero_mem hC₂ hx₀,
      apply_instance },
    exact h.trans (gauge_nonneg _) }
end

/-- A nonzero continuous linear functional is open. -/
lemma nonzero_linear_map_is_open_map {E : Type*} [add_comm_group E] [topological_space E]
  [topological_add_group E] [module ℝ E] [has_continuous_smul ℝ E] (f : E →L[ℝ] ℝ) (hf : f ≠ 0) :
  is_open_map f :=
begin
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, f x₀ ≠ 0,
  { by_contra h,
    push_neg at h,
    exact hf (continuous_linear_map.ext (λ x, by simp [h]) )},
  intros A hA,
  rw is_open_iff_mem_nhds,
  rintro _ ⟨a, ha, rfl⟩,
  let g : ℝ → E := λ x, a + (x - f a) • (f x₀)⁻¹ • x₀,
  have := (show continuous g, by continuity).is_open_preimage _ ‹is_open A›,
  rw is_open_iff_mem_nhds at this,
  exact filter.sets_of_superset _ (this (f a) (by simpa [set.mem_preimage, g]))
    (λ x hx, ⟨_, hx, by simp [hx₀]⟩),
end

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
    apply nonzero_linear_map_is_open_map _ _ _ hA₂,
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
    have := hf₁ _ ha₀,
    simp only [continuous_linear_map.zero_apply] at this,
    have := hf₂ _ hb₀,
    simp only [continuous_linear_map.zero_apply] at this,
    linarith },
  have : is_open_map f := nonzero_linear_map_is_open_map _ this,
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
  (hB₁ : convex ℝ B) (hB₃ : is_closed B) (disj : disjoint A B) :
  ∃ U V, is_open U ∧ is_open V ∧ convex ℝ U ∧ convex ℝ V ∧ A ⊆ U ∧ B ⊆ V ∧ disjoint U V :=
begin
  have : ∃ (n : ℕ), disjoint (A + metric.ball 0 (n+1)⁻¹) (B + metric.ball 0 (n+1)⁻¹),
  { by_contra h,
    push_neg at h,
    simp only [not_disjoint_iff, set.mem_add, metric.mem_ball, dist_zero_right,
      ←exists_and_distrib_left, ←exists_and_distrib_right, and_assoc] at h,
    choose z f f' g g' h₁ h₂ h₃ h₄ h₅ h₆ using h,
    obtain ⟨w, hw, φ, hφ₁, hφ₂ : tendsto (f ∘ _) _ _⟩ := hA₂.tendsto_subseq h₁,
    have : tendsto (g ∘ φ) at_top (𝓝 w),
    { have : tendsto (f - g) at_top (𝓝 0),
      { suffices : ∀ n, ∥(f - g) n∥ ≤ 2 * (n+1)⁻¹,
        { apply squeeze_zero_norm this,
          rw ←mul_zero (2:ℝ),
          apply tendsto.const_mul (2:ℝ),
          simp_rw inv_eq_one_div,
          apply tendsto_one_div_add_at_top_nhds_0_nat },
        intro n,
        simp only [pi.sub_apply],
        have : f n - g n = g' n - f' n,
        { rw [sub_eq_iff_eq_add', ←add_sub_assoc, h₆, ←h₃, add_sub_cancel] },
        rw this,
        apply le_trans (norm_sub_le _ _) _,
        rw two_mul,
        apply add_le_add (h₅ n).le (h₂ n).le },
      have : tendsto (f ∘ φ - g ∘ φ) at_top (𝓝 0),
      { have : f ∘ φ - g ∘ φ = (f - g) ∘ φ,
        { ext,
          simp },
        rw this,
        apply tendsto.comp ‹tendsto (f - g) at_top _› hφ₁.tendsto_at_top },
      simpa using tendsto.sub hφ₂ ‹tendsto (f ∘ φ - g ∘ φ) at_top _› },
    have := mem_of_is_closed_sequential ‹is_closed B› (λ n, h₄ (φ n)) this,
    apply disj ⟨hw, ‹w ∈ B›⟩ },
  obtain ⟨n, hn⟩ := this,
  refine ⟨_, _, _, _, hA₁.add _, hB₁.add _, _, _, hn⟩,
  { exact metric.is_open_ball.add_left },
  { exact metric.is_open_ball.add_left },
  { exact convex_ball 0 _ },
  { exact convex_ball 0 _ },
  { suffices : A + {0} ⊆ A + metric.ball (0:E) (n+1)⁻¹,
    { simpa },
    apply add_subset_add (set.subset.refl _),
    simp only [metric.mem_ball, norm_zero, dist_zero_left, singleton_subset_iff, inv_pos],
    norm_cast,
    simp },
  { suffices : B + {0} ⊆ B + metric.ball (0:E) (n+1)⁻¹,
    { simpa },
    apply add_subset_add (set.subset.refl _),
    simp only [metric.mem_ball, norm_zero, dist_zero_left, singleton_subset_iff, inv_pos],
    norm_cast,
    simp },
end

/-- A version of the Hahn-Banach theorem: given disjoint convex sets `A`, `B` where `A` is compact
and `B` is closed, there is a continuous linear functional which strongly separates them. -/
theorem geometric_hahn_banach_compact_closed {A B : set E} (hA₁ : convex ℝ A) (hA₂ : is_compact A)
  (hB₁ : convex ℝ B) (hB₂ : is_closed B) (disj : disjoint A B) :
  ∃ (f : E →L[ℝ] ℝ) (s t : ℝ), (∀ a ∈ A, f a < s) ∧ s < t ∧ (∀ b ∈ B, t < f b) :=
begin
  rcases A.eq_empty_or_nonempty with (rfl | hA),
  { refine ⟨0, -2, -1, by simp, by norm_num, λ b hb, by norm_num⟩ },
  rcases B.eq_empty_or_nonempty with (h | hB),
  { rw h,
    exact ⟨0, 1, 2, λ a ha, by norm_num, by norm_num, by simp⟩ },
  obtain ⟨U, V, hU, hV, hU₁, hV₁, AU, BV, disj'⟩ := closed_compact_separate hA₁ hA₂ hB₁ hB₂ disj,
  obtain ⟨f, s, hf₁, hf₂⟩ := geometric_hahn_banach_open_open hU₁ hU hV₁ hV disj',
  obtain ⟨x, hx₁, hx₂⟩ := hA₂.exists_forall_ge hA f.continuous.continuous_on,
  have : Sup (f '' A) = f x,
  { apply le_antisymm (cSup_le (hA.image f) (by simpa)),
    refine le_cSup ⟨f x, by simpa [upper_bounds]⟩ ⟨_, hx₁, rfl⟩ },
  have : f x < s := hf₁ x (AU hx₁),
  exact ⟨f, (f x + s)/2, s, λ a ha, by linarith [hx₂ a ha], by linarith, λ b hb, hf₂ b (BV hb)⟩,
end

/--
A version of the Hahn-Banach theorem: given disjoint convex subsets `A,B` where `A` is closed,
and `B` is compact, there is a continuous linear functional which strongly separates them.
-/
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
