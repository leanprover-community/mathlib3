import tactic
import data.real.basic
import linear_algebra.std_basis
import linear_algebra.affine_space.finite_dimensional
import linear_algebra.affine_space.combination
import linear_algebra.finite_dimensional
import algebra.module.linear_map
import analysis.normed_space.operator_norm
import combinatorics.simplicial_complex.convex_independence
import combinatorics.simplicial_complex.to_move.default
import analysis.convex.extreme

open_locale classical affine big_operators
open set
--TODO: generalise to LCTVS
variables {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {A B C : set E}
  {X : finset E}

--provable from the above by induction on C
lemma diff_subset_convex_hull_diff_of_finite (hBA : B ⊆ convex_hull A) (hCB : C ⊆ convex_hull B)
  (hC : finite C) :
  B \ C ⊆ convex_hull (A \ C) :=
begin
  rintro x ⟨hxB, hxC⟩,
  have := hBA hxB,
  sorry
end

lemma convex.extreme_points_convex_independent (hA : convex A) :
  convex_independent (λ p, p : A.extreme_points → E) :=
(convex_independent_set_iff' _).2 $ λ x hxA hx, (extreme_points_convex_hull_subset
  (inter_extreme_points_subset_extreme_points_of_subset (convex_hull_min
  (subset.trans (diff_subset _ _) extreme_points_subset) hA) ⟨hx, hxA⟩)).2 (mem_singleton _)

lemma eq_extreme_points_convex_hull_iff_convex_independent :
  A = (convex_hull A).extreme_points ↔ convex_independent (λ p, p : A → E) :=
begin
  split,
  { rintro h,
    rw h,
    exact (convex_convex_hull _).extreme_points_convex_independent },
  rintro hA,
  rw convex_independent_set_iff' at hA,
  refine subset.antisymm _ extreme_points_convex_hull_subset,
  rintro x hxA,
  use subset_convex_hull _ hxA,
  by_contra h,
  push_neg at h,
  obtain ⟨x₁, x₂, hx₁, hx₂, hx⟩ := h,
  apply hA _ hxA,
  suffices h : x₁ ∈ convex_hull (A \ {x}) ∧ x₂ ∈ convex_hull (A \ {x}),
  { exact convex_iff_open_segment_subset.1 (convex_convex_hull _) h.1 h.2 hx.1 },
  sorry --use diff_subset_convex_hull_diff_of_convex or _of_finite on A = A, B = {x₁, x₂}, C = {x}
end

/- deprecated because generalised by `eq_extreme_points_convex_hull_iff_convex_independent`
lemma extreme_to_convex_hull_of_affine_independent {s : finset E} (hx : x ∈ s)
  (hs : affine_independent ℝ (λ p, p : (s : set E) → E)) :
  x ∈ (convex_hull ↑s : set E).extreme_points :=
begin
  refine ⟨subset_convex_hull _ hx, _⟩,
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
end-/

/- deprecated
lemma inter_frontier_self_inter_convex_hull_extreme :
  is_extreme (closure A) (closure A ∩ frontier (convex_hull A)) :=
begin
  refine ⟨inter_subset_left _ _, λ x₁ x₂ hx₁A hx₂A x hxA hx, ⟨⟨hx₁A, _⟩, hx₂A, _⟩⟩,
  sorry,
  sorry
end

lemma frontier_extreme_to_closure (hA₁ : convex A) (hA₂ : is_closed A) :
  is_extreme A (frontier A) :=
begin
  convert (inter_frontier_self_inter_convex_hull_extreme : is_extreme (closure A)
    (closure A ∩ frontier (convex_hull A))),
  { exact (is_closed.closure_eq hA₂).symm },
  rw [convex.convex_hull_eq hA₁, inter_eq_self_of_subset_right frontier_subset_closure],
end-/

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
    { exact le_of_lt (div_pos nat.one_div_pos_of_nat (add_pos nat.one_div_pos_of_nat (by linarith))),
    },
    {
      exact le_of_lt (one_div_pos.2 (add_pos nat.one_div_pos_of_nat (by linarith))),
    },
    {
      rw [←add_div, div_self],
      exact (ne_of_gt (add_pos nat.one_div_pos_of_nat (by linarith))),
    },
    {
      sorry,
    },
    {
      rintro rfl,
      exact hyB hxB,
    },
    {
      rintro h,
      apply hyB,
      suffices h : x = y,
      { rw ←h, exact hxB },
      suffices h : (1/n.succ : ℝ) • x = (1/n.succ : ℝ) • y,
      { exact smul_injective (ne_of_gt nat.one_div_pos_of_nat) h },
      calc
        (1/n.succ : ℝ) • x
            = -(1 • x) + ((1 • x + (1/n.succ : ℝ) • x) - (1/n.succ : ℝ) • y) + (1/n.succ : ℝ) • y : sorry
        ... = -(1 • x) + ((1 + 1/n.succ : ℝ) • x - (1/n.succ : ℝ) • y) + (1/n.succ : ℝ) • y : sorry
        ... = -(1 • x) + z n + (1/n.succ : ℝ) • y : by refl
        ... = -(1 • x) + x + (1/n.succ : ℝ) • y : by rw h
        ... = (1/n.succ : ℝ) • y : by simp,
    },
  },
  rw ←sub_zero x,
  apply filter.tendsto.sub,
  {
    nth_rewrite 0 ←one_smul _ x,
    apply filter.tendsto.smul_const,
    nth_rewrite 0 ←add_zero (1 : ℝ), --weirdly skips the first two `1`. Might break in the future
    apply filter.tendsto.const_add,
    sorry
  },
  rw ←zero_smul _ y,
  apply filter.tendsto.smul_const,-/
  sorry
end



lemma subset_of_convex_hull_eq_convex_hull_of_convex_independent {X Y : finset E}
  (hX : convex_independent (λ p, p : (X : set E) → E))
  (h : convex_hull ↑X = convex_hull (Y : set E)) :
  X ⊆ Y :=
begin
  rintro x hx,
  have hxextreme := (eq_extreme_points_convex_hull_iff_convex_independent.2 hX).subset hx,
  rw h at hxextreme,
  exact_mod_cast extreme_points_convex_hull_subset hxextreme,
end

lemma eq_of_convex_hull_eq_convex_hull_of_convex_independent
  {X Y : finset E}
  (hX : convex_independent (λ p, p : (X : set E) → E))
  (hY : convex_independent (λ p, p : (Y : set E) → E))
  (h : convex_hull (X : set E) = convex_hull (Y : set E)) :
  X = Y :=
finset.subset.antisymm
  (subset_of_convex_hull_eq_convex_hull_of_convex_independent hX h)
  (subset_of_convex_hull_eq_convex_hull_of_convex_independent hY h.symm)
