/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.convex.extreme
import combinatorics.simplicial_complex.convex_independence
import linear_algebra.affine_space.finite_dimensional

/-!
# Extreme sets
-/

open_locale classical affine big_operators
open set
--TODO: generalise to LCTVS
variables {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {A B C : set E}
  {X : finset E}

--provable from the above by induction on C
lemma erase_subset_convex_hull_erase (hBA : B ⊆ convex_hull 𝕜 A) (hxB : x ∈ convex_hull 𝕜 B) :
  B \ {x} ⊆ convex_hull 𝕜 (A \ {x}) :=
begin
  rintro y ⟨hyB, hxy⟩,
  rw mem_singleton_iff at hxy,
  have := hBA hyB,
  sorry
end

lemma convex.extreme_points_convex_independent (hA : convex 𝕜 A) :
  convex_independent 𝕜 (λ p, p : A.extreme_points → E) :=
(convex_independent_set_iff' _).2 $ λ x hxA hx, (extreme_points_convex_hull_subset
  (inter_extreme_points_subset_extreme_points_of_subset (convex_hull_min
  ((diff_subset _ _).trans extreme_points_subset) hA) ⟨hx, hxA⟩)).2 (mem_singleton _)

lemma eq_extreme_points_convex_hull_iff_convex_independent :
  A = (convex_hull 𝕜 A).extreme_points ↔ convex_independent 𝕜 (λ p, p : A → E) :=
begin
  split,
  { rintro h,
    rw h,
    exact (convex_convex_hull 𝕜 _).extreme_points_convex_independent },
  rintro hA,
  rw convex_independent_set_iff' at hA,
  refine subset.antisymm _ extreme_points_convex_hull_subset,
  rintro x hxA,
  use subset_convex_hull 𝕜 _ hxA,
  by_contra h,
  push_neg at h,
  obtain ⟨x₁, x₂, hx₁, hx₂, hx⟩ := h,
  suffices h : x₁ ∈ convex_hull 𝕜 (A \ {x}) ∧ x₂ ∈ convex_hull 𝕜 (A \ {x}),
  { exact hA _ hxA (convex_iff_open_segment_subset.1 (convex_convex_hull 𝕜 _) h.1 h.2 hx.1) },
  have hx₁₂ : segment x₁ x₂ ⊆ convex_hull 𝕜 A := (convex_convex_hull 𝕜 _).segment_subset hx₁ hx₂,
  refine ⟨erase_subset_convex_hull_erase hx₁₂ (subset_convex_hull 𝕜 _ $ open_segment_subset_segment
    _ _ hx.1) _, erase_subset_convex_hull_erase hx₁₂ (subset_convex_hull 𝕜 _ $
    open_segment_subset_segment _ _ hx.1) _⟩,
  { rw [mem_diff, mem_singleton_iff],
    refine ⟨left_mem_segment _ _, λ h, hx.2 h _⟩,
    rw [h, left_mem_open_segment_iff] at hx,
    exact hx.1.symm },
  rw [mem_diff, mem_singleton_iff],
  refine ⟨right_mem_segment _ _, λ h, hx.2 _ h⟩,
  rw [h, right_mem_open_segment_iff] at hx,
  exact hx.1,
end

-- beurk
lemma inter_frontier_self_inter_convex_hull_extreme :
  is_extreme (closure A) (closure A ∩ frontier (convex_hull 𝕜 A)) :=
begin
  refine ⟨inter_subset_left _ _, λ x₁ x₂ hx₁A hx₂A x hxA hx, ⟨⟨hx₁A, _⟩, hx₂A, _⟩⟩,
  sorry,
  sorry
end

-- beurk
lemma frontier_extreme (hA₁ : convex 𝕜 A) (hA₂ : is_closed A) :
  is_extreme A (frontier A) :=
begin
  convert (inter_frontier_self_inter_convex_hull_extreme : is_extreme (closure A)
    (closure A ∩ frontier (convex_hull 𝕜 A))),
  { exact (is_closed.closure_eq hA₂).symm },
  rw [convex.convex_hull_eq hA₁, inter_eq_self_of_subset_right frontier_subset_closure],
end

-- interesting
lemma convex.frontier_extreme_to_closure (hAconv : convex 𝕜 A) :
  is_extreme (closure A) (frontier A) :=
begin
  use frontier_subset_closure,
  sorry
end

--can be generalized is_extreme.subset_intrinsic_frontier
lemma is_extreme.subset_frontier (hAB : is_extreme A B) (hBA : ¬ A ⊆ B) :
  B ⊆ frontier A :=
begin
  rintro x hxB,
  obtain ⟨y, hyA, hyB⟩ := nonempty_of_ssubset ⟨hAB.1, hBA⟩,
  rw frontier_eq_closure_inter_closure,
  use subset_closure (hAB.1 hxB),
  rw mem_closure_iff_seq_limit,
  let z : ℕ → E := λ n, (1 + 1/n.succ : ℝ) • x - (1/n.succ : ℝ) • y,
  use z,
  /-
  split,
  { rintro n hzn,
    --have := hAB.2 y (f n) hyA hfn x hxB,
    refine hyB (hAB.2 y (z n) hyA hzn x hxB ⟨1/(↑n + 1)/(1/(↑n + 1) + 1), 1/(1/(↑n + 1) + 1),
      _, _, _, _⟩).1,
    { exact (div_pos nat.one_div_pos_of_nat (add_pos nat.one_div_pos_of_nat (by linarith))).le },
    { exact le_of_lt (one_div_pos.2 (add_pos nat.one_div_pos_of_nat (by linarith))).le },
    { rw [←add_div, div_self],
      exact (add_pos nat.one_div_pos_of_nat (by linarith)).ne' },
    {   sorry,
    },
    { rintro rfl,
      exact hyB hxB },
    { rintro h,
      apply hyB,
      suffices h : x = y,
      { rw ←h, exact hxB },
      suffices h : (1/n.succ : ℝ) • x = (1/n.succ : ℝ) • y,
      { exact smul_injective (ne_of_gt nat.one_div_pos_of_nat) h },
      calc
        (1/n.succ : ℝ) • x
            = -(1 • x) + ((1 • x + (1/n.succ : ℝ) • x) - (1/n.succ : ℝ) • y) + (1/n.succ : ℝ) • y
            : sorry
        ... = -(1 • x) + ((1 + 1/n.succ : ℝ) • x - (1/n.succ : ℝ) • y) + (1/n.succ : ℝ) • y : sorry
        ... = -(1 • x) + z n + (1/n.succ : ℝ) • y : by refl
        ... = -(1 • x) + x + (1/n.succ : ℝ) • y : by rw h
        ... = (1/n.succ : ℝ) • y : by simp } },
  rw ←sub_zero x,
  apply filter.tendsto.sub,
  { nth_rewrite 0 ←one_smul _ x,
    apply filter.tendsto.smul_const,
    nth_rewrite 0 ←add_zero (1 : ℝ), --weirdly skips the first two `1`. Might break in the future
    apply filter.tendsto.const_add,
    sorry },
  rw ←zero_smul _ y,
  apply filter.tendsto.smul_const,-/
  sorry
end

lemma convex.is_extreme_iff_open_segment_subset_diff (hAconv : convex 𝕜 A) :
  is_extreme A B ↔ B ⊆ A ∧ ∀ ⦃x y⦄, x ∈ A → y ∈ A \ B → open_segment x y ⊆ A \ B :=
begin
  refine ⟨λ h, ⟨h.1, λ x y hx hy z hz, ⟨hAconv.open_segment_subset hx hy.1 hz, λ hzB, hy.2
    (h.2 x y hx hy.1 z hzB hz).2⟩⟩, λ h, ⟨h.1, λ x y hx hy z hzB hz, ⟨_, _⟩⟩⟩,
  { by_contra hxB,
    rw open_segment_symm at hz,
    exact (h.2 hy ⟨hx, hxB⟩ hz).2 hzB },
  { by_contra hyB,
    exact (h.2 hx ⟨hy, hyB⟩ hz).2 hzB }
end

/-{E : Type*} [add_comm_group E] [module ℝ E] [topological_space E]
  [sequential_space E] [topological_add_group E] [has_continuous_smul ℝ E]-/

lemma closure_eq_closure_interior  {A : set E}
  (hAconv : convex 𝕜 A) (hAnemp : (interior A).nonempty) :
  closure A = closure (interior A) :=
begin
  refine subset.antisymm (λ x hx, _) (closure_mono interior_subset),
  obtain ⟨y, hy⟩ := hAnemp,
  rw mem_closure_iff_seq_limit at ⊢ hx,
  obtain ⟨z, hzA, hzx⟩ := hx,
  use λ n, (1 - 1/(n + 2) : ℝ) • z n + (1/(n + 2) : ℝ) • y,
  split,
  { rintro n,
    rw interior_eq_closure_diff_frontier at ⊢ hy,
    have h₁ : (1 : ℝ) < ↑n + 2 := by { norm_cast, norm_num },
    have h₀ := zero_lt_one.trans h₁,
    exact (hAconv.closure.is_extreme_iff_open_segment_subset_diff.1
      hAconv.frontier_extreme_to_closure).2 (subset_closure (hzA n)) hy
      ⟨1 - 1/(n + 2), 1/(n + 2), sub_pos.2 $ (div_lt_one h₀).2 h₁, div_pos zero_lt_one h₀,
      sub_add_cancel _ _, rfl⟩ },
  have h : filter.tendsto (λ (n : ℕ), 1 / ((n : ℝ) + 2)) filter.at_top (nhds (0 : ℝ)),
  { sorry
  },
  rw [←add_zero x, ←one_smul ℝ x, ←zero_smul _ y],
  nth_rewrite 0 ←sub_zero (1 : ℝ),
  refine filter.tendsto.add (filter.tendsto.smul _ hzx) (filter.tendsto.smul_const h _),
  apply filter.tendsto.const_add,
  exact filter.tendsto.neg h,
end



lemma convex_independent.subset_of_convex_hull_eq_convex_hull {X Y : finset E}
  (hX : convex_independent 𝕜 (λ p, p : (X : set E) → E))
  (h : convex_hull 𝕜 ↑X = convex_hull 𝕜 (Y : set E)) :
  X ⊆ Y :=
begin
  rintro x hx,
  have hxextreme := (eq_extreme_points_convex_hull_iff_convex_independent.2 hX).subset hx,
  rw h at hxextreme,
  exact_mod_cast extreme_points_convex_hull_subset hxextreme,
end

lemma convex_independent.eq_of_convex_hull_eq_convex_hull
  {X Y : finset E}
  (hX : convex_independent 𝕜 (λ p, p : (X : set E) → E))
  (hY : convex_independent 𝕜 (λ p, p : (Y : set E) → E))
  (h : convex_hull 𝕜 (X : set E) = convex_hull 𝕜 (Y : set E)) :
  X = Y :=
(hX.subset_of_convex_hull_eq_convex_hull h).antisymm
  (hY.subset_of_convex_hull_eq_convex_hull h.symm)

/- deprecated because generalised by `eq_extreme_points_convex_hull_iff_convex_independent`
lemma extreme_to_convex_hull_of_affine_independent {s : finset E} (hx : x ∈ s)
  (hs : affine_independent 𝕜 (λ p, p : (s : set E) → E)) :
  x ∈ (convex_hull 𝕜 ↑s : set E).extreme_points :=
begin
  refine ⟨subset_convex_hull 𝕜 _ hx, _⟩,
  rintro y y' hy hy' t,
  rw finset.convex_hull_eq at hy hy',
  obtain ⟨w, hw₀, hw₁, hy⟩ := hy,
  obtain ⟨w', hw'₀, hw'₁, hy'⟩ := hy',
  rw segment_eq_image at t,
  obtain ⟨θ, hθ₁, hθ₂ : _ + _ = _⟩ := t,
  rw finset.center_mass_eq_of_sum_1 _ _ hw₁ at hy,
  rw finset.center_mass_eq_of_sum_1 _ _ hw'₁ at hy',
  change s.sum (λ i, w i • i) = y at hy,
  change s.sum (λ i, w' i • i) = y' at hy',
  let w'' : E → ℝ := λ t, (1 - θ) * w t + θ * w' t - if t = x then 1 else 0,
  have hw''₁ : s.sum w'' = 0,
  { rw [finset.sum_sub_distrib, finset.sum_add_distrib, ← finset.mul_sum, ← finset.mul_sum, hw₁,
      hw'₁, finset.sum_ite_eq' s, if_pos hx],
    simp },
  have hw''₂ : s.sum (λ i, w'' i • i) = 0,
  { simp only [sub_smul, add_smul, finset.sum_add_distrib, finset.sum_sub_distrib],
    simp only [mul_smul, ←finset.smul_sum, hy, hy'],
    simp only [ite_smul, zero_smul, one_smul, finset.sum_ite_eq', if_pos hx, hθ₂, sub_self] },
  by_contra t,
  push_neg at t,
  suffices hw''₃ : ∀ q ∈ s, w'' q = 0,
  { have : θ = 0 ∨ θ = 1,
    { by_contra hθ,
      push_neg at hθ,
      have : 0 < θ ∧ 0 < 1 - θ,
      { split,
        { apply lt_of_le_of_ne hθ₁.1 hθ.1.symm },
        { rw sub_pos,
          apply lt_of_le_of_ne hθ₁.2 hθ.2 } },
      have both_zero : ∀ q ∈ s, q ≠ x → w q = 0,
      { intros q hq₁ hq₂,
        specialize hw''₃ q hq₁,
        change _ + _ = _ at hw''₃,
        rw if_neg hq₂ at hw''₃,
        simp only [add_zero, neg_zero] at hw''₃,
        rw add_eq_zero_iff'
            (mul_nonneg (le_of_lt this.2) (hw₀ q hq₁))
            (mul_nonneg (le_of_lt this.1) (hw'₀ q hq₁)) at hw''₃,
        rw mul_eq_zero at hw''₃,
        apply or.resolve_left hw''₃.1 (ne_of_gt this.2) },
      have : (1 - θ) * w x + θ * w' x = 1,
      { specialize hw''₃ _ hx,
        change (1 - θ) * w x + θ * w' x - ite _ _ _ = 0 at hw''₃,
        rwa [if_pos rfl, sub_eq_zero] at hw''₃ },
      rw finset.sum_eq_single x at hw₁,
      { rw finset.sum_eq_single x at hy,
        { rw hw₁ at hy,
          apply t.1,
          rw ←hy,
          simp },
        { rintro q hq₁ hq₂,
          rw both_zero q hq₁ hq₂,
          simp },
        { exact λ t, (t hx).elim } },
      { intros q hq₁ hq₂,
        apply both_zero q hq₁ hq₂ },
      { exact λ t, (t hx).elim } },
    rcases this with (rfl | rfl),
    { simp only [add_zero, one_smul, sub_zero, zero_smul] at hθ₂,
      apply t.1 hθ₂.symm },
    { simp only [one_smul, zero_smul, zero_add, sub_self] at hθ₂,
      apply t.2 hθ₂.symm } },
  rw affine_independent_iff_of_fintype at hs,
  let w''' : (s : set E) → ℝ := λ t, w'' (t : E),
  have hw''' : finset.univ.sum w''' = 0,
  { rw coe_sum,
    apply hw''₁ },
  specialize hs w''' hw''' _,
  { rw finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ hw''' (0 : E),
    rw finset.weighted_vsub_of_point_apply,
    simp only [vsub_eq_sub, sub_zero],
    rw coe_sum _ (λ i, w'' i • i),
    apply hw''₂ },
  rintro q hq,
  exact hs ⟨q, hq⟩,
end
-/
