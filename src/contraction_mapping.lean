/-
Copyright (c) 2018 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker
-/
import analysis.limits analysis.normed_space
open nat filter

lemma fixed_point_of_iteration_limit {α : Type*} [topological_space α] [t2_space α] {f : α → α}
  {x : α} : continuous f → (∃ x₀ : α, tendsto (λ n, f^[n] x₀) at_top (nhds x)) → x = f x :=
begin
  intros hf hx,
  cases hx with x₀ hx,
  apply @tendsto_nhds_unique α ℕ _ _ (λ n, f^[succ n] x₀) at_top x (f x),
  { exact at_top_ne_bot },
  { rewrite @tendsto_comp_succ_at_top_iff α (λ n, f^[n] x₀) (nhds x),
    exact hx },
  { rewrite funext (λ n, iterate_succ' f n x₀),
    exact tendsto.comp hx (continuous.tendsto hf x) },
end

def lipschitz {α : Type*} [metric_space α] (K : ℝ) (f : α → α) :=
0 ≤ K ∧ ∀ (x y : α), dist (f x) (f y) ≤ K * (dist x y)

lemma uniform_continuous_of_lipschitz {α : Type*} [metric_space α] {K : ℝ} {f : α → α} :
  lipschitz K f → uniform_continuous f :=
λ hf, uniform_continuous_of_metric.mpr (λ ε hε, or.elim (lt_or_le K ε)
  (λ h, ⟨(1 : ℝ), zero_lt_one, (λ x y hd, lt_of_le_of_lt (hf.right x y)
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_of_lt hd) hf.left) (symm (mul_one K) ▸ h)))⟩)
  (λ h, ⟨ε / K, div_pos_of_pos_of_pos hε (lt_of_lt_of_le hε h),
    (λ x y hd, lt_of_le_of_lt (hf.right x y)
      (mul_comm (dist x y) K ▸ mul_lt_of_lt_div (lt_of_lt_of_le hε h) hd))⟩))

lemma iterated_lipschitz_of_lipschitz {α : Type*} [metric_space α] {K : ℝ} {f : α → α} :
   lipschitz K f → ∀ (n : ℕ), lipschitz (K ^ n) (f^[n]) :=
begin
  intros hf n,
  induction n with n ih,
  { apply and.intro,
    { exact pow_zero K ▸ zero_le_one, },
    { intros x y,
      rewrite [pow_zero K, one_mul, iterate_zero f x, iterate_zero f y], }, },
  { apply and.intro,
    { exact mul_nonneg hf.left ih.left, },
    { intros x y,
      rewrite [iterate_succ', iterate_succ'],
      apply le_trans (hf.right (f^[n] x) (f^[n] y)),
      rewrite [pow_succ K n, mul_assoc],
      exact mul_le_mul_of_nonneg_left (ih.right x y) hf.left, }, },
end

lemma dist_inequality_of_contraction {α : Type*} [metric_space α] {K : ℝ} {f : α → α} (hK₁ : K < 1) :
  lipschitz K f → ∀ (x y : α), dist x y ≤ (dist x (f x) + dist y (f y)) / (1 - K) :=
begin
  intros hf x y,
  apply le_div_of_mul_le (sub_pos_of_lt hK₁),
  rewrite [mul_comm, sub_mul, one_mul],
  apply sub_left_le_of_le_add,
  apply le_trans,
    exact dist_triangle_right x y (f x),
  apply le_trans,
    apply add_le_add_left,
    exact dist_triangle_right y (f x) (f y),
  rewrite [←add_assoc, add_comm],
  apply add_le_add_right,
  exact hf.right x y,
end

theorem fixed_point_unique_of_contraction {α : Type*} [metric_space α] {K : ℝ} {f : α → α} :
  K < 1 → lipschitz K f → ∀ (x : α), x = f x → ∀ (y : α), y = f y → x = y :=
begin
  intros hK₁ hf x hx y hy,
  apply iff.mp dist_le_zero,
  apply le_trans,
  exact dist_inequality_of_contraction hK₁ hf x y,
  rewrite [iff.mpr dist_eq_zero hx, iff.mpr dist_eq_zero hy],
  norm_num,
end

lemma dist_bound_of_contraction {α : Type*} [metric_space α] {K : ℝ} {f : α → α} :
  K < 1 → lipschitz K f → ∀ (x₀ : α) (n : ℕ × ℕ),
  dist (f^[n.1] x₀) (f^[n.2] x₀) ≤ (K ^ n.1 + K ^ n.2) * dist x₀ (f x₀) / (1 - K) :=
begin
  intros hK₁ hf x₀ n,
  apply le_trans,
  exact dist_inequality_of_contraction hK₁ hf (f^[n.1] x₀) (f^[n.2] x₀),
  apply div_le_div_of_le_of_pos _ (sub_pos_of_lt hK₁),
  have h : ∀ (m : ℕ), dist (f^[m] x₀) (f (f^[m] x₀)) ≤ K ^ m * dist x₀ (f x₀),
    intro m,
    rewrite [←iterate_succ' f m x₀, iterate_succ f m x₀],
    exact and.right (iterated_lipschitz_of_lipschitz hf m) x₀ (f x₀),
  rewrite add_mul,
  apply add_le_add,
  { exact h n.1, },
  { exact h n.2, },
end

lemma continuous_prod_snd {α β γ  : Type*} [topological_space α] [topological_space β]
  [topological_space γ] {f : α × β → γ} {a : α} (hf : continuous f) : continuous (λ b, f (a, b)) :=
continuous.comp (continuous.prod_mk continuous_const continuous_id) hf

local attribute [instance] prod.prod_semilattice_sup

lemma tendsto_dist_bound_at_top_nhds_0 {K : ℝ} (hK₀ : 0 ≤ K) (hK₁ : K < 1) (z : ℝ) :
  tendsto (λ (n : ℕ × ℕ), (K ^ n.1 + K ^ n.2) * z / (1 - K)) at_top (nhds 0) :=
begin
  let f := λ (n : ℕ × ℕ), (K ^ n.1, K ^ n.2),
  let g := λ (y : ℝ × ℝ), (y.1 + y.2) * z / (1 - K),
  show tendsto (g ∘ f) at_top (nhds 0),
  apply tendsto.comp,
  { show tendsto f at_top (nhds (0, 0)),
    rw ←prod_at_top_at_top_eq,
    apply tendsto_prod_mk_nhds,
    { apply tendsto.comp tendsto_fst,
      exact tendsto_pow_at_top_nhds_0_of_lt_1 hK₀ hK₁, },
    { apply tendsto.comp tendsto_snd,
      exact tendsto_pow_at_top_nhds_0_of_lt_1 hK₀ hK₁, }, },
  { show tendsto g (nhds (0, 0)) (nhds 0),
    have hg : g = λ (y : ℝ × ℝ), z / (1 - K) * (y.1 + y.2),
      ext,
      rewrite [mul_comm, ←mul_div_assoc],
    have hc : continuous g,
      rewrite hg,
      apply continuous.comp,
      exact continuous_add',
      exact continuous_prod_snd continuous_mul',
    have h₀ := continuous.tendsto hc (0, 0),
    suffices h : g (0, 0) = 0,
      rewrite h at h₀,
      exact h₀,
    rewrite hg,
    norm_num, },
end

theorem fixed_point_exists_of_contraction {α : Type*} [inhabited α] [metric_space α]
  [complete_space α] {K : ℝ} {f : α → α} : K < 1 → lipschitz K f → ∃ (x : α), x = f x :=
begin
  intros hK₁ hf,
  let x₀ := default α,
  suffices h : cauchy_seq (λ n, f^[n] x₀),
    cases cauchy_seq_tendsto_of_complete h with x hx,
    use x,
    apply @fixed_point_of_iteration_limit α _,
    { exact uniform_continuous.continuous (uniform_continuous_of_lipschitz hf), },
    { exact ⟨x₀, hx⟩, },
  apply iff.mpr cauchy_seq_iff_tendsto_dist_at_top_0,
  apply squeeze_zero,
  { intro x,
    exact dist_nonneg, },
  { exact dist_bound_of_contraction hK₁ hf x₀, },
  { exact tendsto_dist_bound_at_top_nhds_0 hf.left hK₁ (dist x₀ (f x₀)), },
end
