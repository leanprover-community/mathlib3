/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.urysohns_lemma
import topology.continuous_function.bounded

/-!
# Metrizability of a normal topological space with second countable topology

In this file we show that a normal topological space with second countable topology `X` is
metrizable: there exists a metric space structure that generates the same topology.

First we prove that `X` can be embedded into `l^∞`, then use this embedding to pull back the metric
space structure.
-/

open set filter metric
open_locale bounded_continuous_function filter topological_space

namespace topological_space

variables (X : Type*) [topological_space X] [normal_space X] [second_countable_topology X]

/-- A normal topological space with second countable topology can be embedded into `l^∞ = ℕ →ᵇ ℝ`.
-/
lemma exists_embedding_l_infty : ∃ f : X → (ℕ →ᵇ ℝ), embedding f :=
begin
  -- Choose a countable basis, and consider the set `s` of pairs of set `(U, V)` such that `U ∈ B`,
  -- `V ∈ B`, and `closure U ⊆ V`.
  rcases exists_countable_basis X with ⟨B, hBc, -, hB⟩,
  set s : set (set X × set X) := {UV ∈ B.prod B| closure UV.1 ⊆ UV.2},
  -- `s` is a countable set.
  haveI : encodable s := ((hBc.prod hBc).mono (inter_subset_left _ _)).to_encodable,
  -- We don't have the space of bounded (possibly discontinuous) functions, so we equip `s`
  -- with the discrete topology and deal with `s →ᵇ ℝ` instead.
  letI : topological_space s := ⊥, haveI : discrete_topology s := ⟨rfl⟩,
  suffices : ∃ f : X → (s →ᵇ ℝ), embedding f,
  { rcases this with ⟨f, hf⟩,
    exact ⟨λ x, (f x).extend (encodable.encode' s) 0, (bounded_continuous_function.isometry_extend
      (encodable.encode' s) (0 : ℕ →ᵇ ℝ)).embedding.comp hf⟩ },
  have hd : ∀ UV : s, disjoint (closure UV.1.1) (UV.1.2ᶜ) :=
    λ UV, disjoint_compl_right.mono_right (compl_subset_compl.2 UV.2.2),
  -- Choose a sequence of `εₙ > 0`, `n : s`, that is bounded above by `1` and tends to zero
  -- along the `cofinite` filter.
  obtain ⟨ε, ε01, hε⟩ : ∃ ε : s → ℝ, (∀ UV, ε UV ∈ Ioc (0 : ℝ) 1) ∧ tendsto ε cofinite (𝓝 0),
  { rcases pos_sum_of_encodable zero_lt_one s with ⟨ε, ε0, c, hεc, hc1⟩,
    refine ⟨ε, λ UV, ⟨ε0 UV, _⟩, hεc.summable.tendsto_cofinite_zero⟩,
    exact (le_has_sum hεc UV $ λ _ _, (ε0 _).le).trans hc1 },
  /- For each `UV = (U, V) ∈ s` we use Urysohn's lemma to choose a function `f UV` that is equal to
  zero on `U` and is equal to `ε UV` on the complement to `V`. -/
  have : ∀ UV : s, ∃ f : C(X, ℝ), eq_on f 0 UV.1.1 ∧ eq_on f (λ _, ε UV) UV.1.2ᶜ ∧
    ∀ x, f x ∈ Icc 0 (ε UV),
  { intro UV,
    rcases exists_continuous_zero_one_of_closed is_closed_closure
      (hB.is_open UV.2.1.2).is_closed_compl (hd UV) with ⟨f, hf₀, hf₁, hf01⟩,
    exact ⟨ε UV • f, λ x hx, by simp [hf₀ (subset_closure hx)], λ x hx, by simp [hf₁ hx],
      λ x, ⟨mul_nonneg (ε01 _).1.le (hf01 _).1, mul_le_of_le_one_right (ε01 _).1.le (hf01 _).2⟩⟩ },
  choose f hf0 hfε hf0ε,
  have hf01 : ∀ UV x, f UV x ∈ Icc (0 : ℝ) 1,
    from λ UV x, Icc_subset_Icc_right (ε01 _).2 (hf0ε _ _),
  /- The embedding is given by `F x UV = f UV x`. -/
  set F : X → s →ᵇ ℝ := λ x, ⟨⟨λ UV, f UV x, continuous_of_discrete_topology⟩, 1, λ UV₁ UV₂,
    real.dist_le_of_mem_Icc_01 (hf01 _ _) (hf01 _ _)⟩,
  have hF : ∀ x UV, F x UV = f UV x := λ _ _, rfl,
  refine ⟨F, embedding.mk' _ (λ x y hxy, _) (λ x, le_antisymm _ _)⟩,
  { /- First we prove that `F` is injective. Indeed, if `F x = F y` and `x ≠ y`, then we can find
    `(U, V) ∈ s` such that `x ∈ U` and `y ∉ V`, hence `F x UV = 0 ≠ ε UV = F y UV`. -/
    refine not_not.1 (λ Hne, _), -- `by_contra Hne` timeouts
    rcases hB.mem_nhds_iff.1 (is_open_ne.mem_nhds Hne) with ⟨V, hVB, hxV, hVy⟩,
    rcases hB.exists_closure_subset (hB.mem_nhds hVB hxV) with ⟨U, hUB, hxU, hUV⟩,
    set UV : ↥s := ⟨(U, V), ⟨hUB, hVB⟩, hUV⟩,
    apply (ε01 UV).1.ne,
    calc (0 : ℝ) = F x UV : (hf0 UV hxU).symm
             ... = F y UV : by rw hxy
             ... = ε UV   : hfε UV (λ h : y ∈ V, hVy h rfl) },
  { /- Now we prove that each neighborhood `V` of `x : X` include a preimage of a neighborhood of
    `F x` under `F`. Without loss of generality, `V` belongs to `B`. Choose `U ∈ B` such that
    `x ∈ V` and `closure V ⊆ U`. Then the preimage of the `(ε (U, V))`-neighborhood of `F x`
    is included by `V`. -/
    refine ((nhds_basis_ball.comap _).le_basis_iff hB.nhds_has_basis).2 _,
    rintro V ⟨hVB, hxV⟩,
    rcases hB.exists_closure_subset (hB.mem_nhds hVB hxV) with ⟨U, hUB, hxU, hUV⟩,
    set UV : ↥s := ⟨(U, V), ⟨hUB, hVB⟩, hUV⟩,
    refine ⟨ε UV, (ε01 UV).1, λ y (hy : dist (F y) (F x) < ε UV), _⟩,
    replace hy : dist (F y UV) (F x UV) < ε UV,
      from (bounded_continuous_function.dist_coe_le_dist _).trans_lt hy,
    contrapose! hy,
    rw [hF, hF, hfε UV hy, hf0 UV hxU, pi.zero_apply, dist_zero_right],
    exact le_abs_self _ },
  { /- Finally, we prove that `F` is continuous. Given `δ > 0`, consider the set `T` of `(U, V) ∈ s`
    such that `ε (U, V) ≥ δ`. Since `ε` tends to zero, `T` is finite. Since each `f` is continuous,
    we can choose a neighborhood such that `dist (F y (U, V)) (F x (U, V)) ≤ δ` for any
    `(U, V) ∈ T`. For `(U, V) ∉ T`, the same inequality is true because both `F y (U, V)` and
    `F x (U, V)` belong to the interval `[0, ε (U, V)]`. -/
    refine (nhds_basis_closed_ball.comap _).ge_iff.2 (λ δ δ0, _),
    have h_fin : finite {UV : s | δ ≤ ε UV}, by simpa only [← not_lt] using hε (gt_mem_nhds δ0),
    have : ∀ᶠ y in 𝓝 x, ∀ UV, δ ≤ ε UV → dist (F y UV) (F x UV) ≤ δ,
    { refine (eventually_all_finite h_fin).2 (λ UV hUV, _),
      exact (f UV).continuous.tendsto x (closed_ball_mem_nhds _ δ0) },
    refine this.mono (λ y hy, (bounded_continuous_function.dist_le δ0.le).2 $ λ UV, _),
    cases le_total δ (ε UV) with hle hle,
    exacts [hy _ hle, (real.dist_le_of_mem_Icc (hf0ε _ _) (hf0ε _ _)).trans (by rwa sub_zero)] }
end

/-- A normal topological space with second countable topology `X` is metrizable: there exists a
metric space structure that generates the same topology. This definition provides a `metric_space`
instance such that the corresponding `topological_space X` instance is definitionally equal
to the original one. -/
@[reducible] noncomputable def to_metric_space : metric_space X :=
@metric_space.replace_uniformity X
  ((uniform_space.comap (exists_embedding_l_infty X).some infer_instance).replace_topology
    (exists_embedding_l_infty X).some_spec.induced)
  (metric_space.induced (exists_embedding_l_infty X).some
    (exists_embedding_l_infty X).some_spec.inj infer_instance)
  rfl

end topological_space
