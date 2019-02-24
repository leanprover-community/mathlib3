/-
Copyright (c) 2018 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl

Lipschitz functions and the Banach fixed-point theorem
-/
import topology.metric_space.basic analysis.specific_limits
open filter

variables {α : Type*} {β : Type*} {γ : Type*}

lemma fixed_point_of_tendsto_iterate [topological_space α] [t2_space α] {f : α → α} {x : α}
  (hf : tendsto f (nhds x) (nhds (f x))) (hx : ∃ x₀ : α, tendsto (λ n, f^[n] x₀) at_top (nhds x)) :
  f x = x :=
begin
  rcases hx with ⟨x₀, hx⟩,
  refine tendsto_nhds_unique at_top_ne_bot _ hx,
  rw [← tendsto_add_at_top_iff_nat 1, funext (assume n, nat.iterate_succ' f n x₀)],
  exact hx.comp hf
end

/-- A Lipschitz function is uniformly continuous -/
lemma uniform_continuous_of_lipschitz [metric_space α] [metric_space β] {K : ℝ}
  {f : α → β} (H : ∀x y, dist (f x) (f y) ≤ K * dist x y) : uniform_continuous f :=
begin
  have : 0 < max K 1 := lt_of_lt_of_le zero_lt_one (le_max_right K 1),
  refine metric.uniform_continuous_iff.2 (λε εpos, _),
  exact ⟨ε/max K 1, div_pos εpos this, assume y x Dyx, calc
    dist (f y) (f x) ≤ K * dist y x : H y x
    ... ≤ max K 1 * dist y x : mul_le_mul_of_nonneg_right (le_max_left K 1) (dist_nonneg)
    ... < max K 1 * (ε/max K 1) : mul_lt_mul_of_pos_left Dyx this
    ... = ε : mul_div_cancel' _ (ne_of_gt this)⟩
end

/-- A Lipschitz function is continuous -/
lemma continuous_of_lipschitz [metric_space α] [metric_space β] {K : ℝ}
  {f : α → β} (H : ∀x y, dist (f x) (f y) ≤ K * dist x y) : continuous f :=
uniform_continuous.continuous (uniform_continuous_of_lipschitz H)

lemma uniform_continuous_of_le_add [metric_space α] {f : α → ℝ} (K : ℝ)
  (h : ∀x y, f x ≤ f y + K * dist x y) : uniform_continuous f :=
begin
  have I : ∀ (x y : α), f x - f y ≤ K * dist x y := λx y, calc
    f x - f y ≤ (f y + K * dist x y) - f y : add_le_add (h x y) (le_refl _)
    ... = K * dist x y : by ring,
  refine @uniform_continuous_of_lipschitz _ _ _ _ K _ (λx y, _),
  rw real.dist_eq,
  refine abs_sub_le_iff.2 ⟨_, _⟩,
  { exact I x y },
  { rw dist_comm, exact I y x }
end

/-- `lipschitz_with K f`: the function `f` is Lipschitz continuous w.r.t. the Lipschitz
constant `K`. -/
def lipschitz_with [metric_space α] [metric_space β] (K : ℝ) (f : α → β) :=
0 ≤ K ∧ ∀x y, dist (f x) (f y) ≤ K * dist x y

namespace lipschitz_with

variables [metric_space α] [metric_space β] [metric_space γ] {K : ℝ}

protected lemma weaken (K' : ℝ) {f : α → β} (hf : lipschitz_with K f) (h : K ≤ K') :
  lipschitz_with K' f :=
⟨le_trans hf.1 h, assume x y, le_trans (hf.2 x y) $ mul_le_mul_of_nonneg_right h dist_nonneg⟩

protected lemma to_uniform_continuous {f : α → β} (hf : lipschitz_with K f) : uniform_continuous f :=
uniform_continuous_of_lipschitz hf.2

protected lemma to_continuous {f : α → β} (hf : lipschitz_with K f) : continuous f :=
continuous_of_lipschitz hf.2

protected lemma const (b : β) : lipschitz_with 0 (λa:α, b) :=
⟨le_refl 0, assume x y, by simp⟩

protected lemma id : lipschitz_with 1 (@id α) :=
⟨zero_le_one, by simp [le_refl]⟩

protected lemma comp {Kf Kg : ℝ} {f : β → γ} {g : α → β}
  (hf : lipschitz_with Kf f) (hg : lipschitz_with Kg g) : lipschitz_with (Kf * Kg) (f ∘ g) :=
⟨mul_nonneg hf.1 hg.1, assume x y,
  calc dist (f (g x)) (f (g y)) ≤ Kf * dist (g x) (g y) : hf.2 _ _
    ... ≤ Kf * (Kg * dist x y) : mul_le_mul_of_nonneg_left (hg.2 _ _) hf.1
    ... = (Kf * Kg) * dist x y : by rw mul_assoc⟩

protected lemma iterate {f : α → α} (hf : lipschitz_with K f) : ∀n, lipschitz_with (K ^ n) (f^[n])
| 0       := lipschitz_with.id
| (n + 1) := by rw [← nat.succ_eq_add_one, pow_succ, mul_comm]; exact (iterate n).comp hf

section contraction
variables {f : α → α} {x y : α}

lemma dist_inequality_of_contraction (hK₁ : K < 1) (hf : lipschitz_with K f) :
   dist x y ≤ (dist x (f x) + dist y (f y)) / (1 - K) :=
suffices dist x y ≤ dist x (f x) + (dist y (f y) + K * dist x y),
  by rwa [le_div_iff (sub_pos_of_lt hK₁), mul_comm, sub_mul, one_mul, sub_le_iff_le_add, add_assoc],
calc dist x y ≤ dist x (f x) + dist y (f x) :
    dist_triangle_right x y (f x)
  ... ≤ dist x (f x) + (dist y (f y) + dist (f x) (f y)) :
    add_le_add_left (dist_triangle_right y (f x) (f y)) _
  ... ≤ dist x (f x) + (dist y (f y) + K * dist x y) :
    add_le_add_left (add_le_add_left (hf.2 _ _) _) _

theorem fixed_point_unique_of_contraction (hK : K < 1) (hf : lipschitz_with K f)
  (hx : f x = x) (hy : f y = y) : x = y :=
dist_le_zero.1 $ le_trans (dist_inequality_of_contraction hK hf) $
  by rewrite [iff.mpr dist_eq_zero hx.symm, iff.mpr dist_eq_zero hy.symm]; simp

lemma dist_bound_of_contraction (hK : K < 1) (hf : lipschitz_with K f) {n m : ℕ} :
  dist (f^[n] x) (f^[m] x) ≤ (K ^ n + K ^ m) * dist x (f x) / (1 - K) :=
begin
  apply le_trans,
  exact dist_inequality_of_contraction hK hf,
  apply div_le_div_of_le_of_pos _ (sub_pos_of_lt hK),
  have h : ∀ (m : ℕ), dist (f^[m] x) (f (f^[m] x)) ≤ K ^ m * dist x (f x),
  { intro m,
    rewrite [←nat.iterate_succ' f m x, nat.iterate_succ f m x],
    exact and.right (hf.iterate m) x (f x) },
  rewrite add_mul,
  exact add_le_add (h n) (h m)
end

private lemma tendsto_dist_bound_at_top_nhds_0 (hK₀ : 0 ≤ K) (hK₁ : K < 1) (z : ℝ) :
  tendsto (λ (n : ℕ × ℕ), (K ^ n.1 + K ^ n.2) * z / (1 - K)) at_top (nhds 0) :=
suffices tendsto (λ (n : ℕ × ℕ), (K ^ n.1 + K ^ n.2) * z / (1 - K))
    (at_top.prod at_top) (nhds (((0 + 0) * z) * (1 - K)⁻¹)),
  by simpa [prod_at_top_at_top_eq],
tendsto_mul (tendsto_mul (tendsto_add
  (tendsto_fst.comp (tendsto_pow_at_top_nhds_0_of_lt_1 hK₀ hK₁))
  (tendsto_snd.comp (tendsto_pow_at_top_nhds_0_of_lt_1 hK₀ hK₁))) tendsto_const_nhds)
  tendsto_const_nhds

/-- Banach fixed-point theorem, contraction mapping theorem -/
theorem exists_fixed_point_of_contraction [hα : nonempty α] [complete_space α]
  (hK : K < 1) (hf : lipschitz_with K f) : ∃x, f x = x :=
let ⟨x₀⟩ := hα in
have tendsto (λ (n : ℕ × ℕ), dist (f^[n.fst] x₀) (f^[n.snd] x₀)) at_top (nhds 0) :=
  squeeze_zero (assume x, dist_nonneg)
    (assume p, dist_bound_of_contraction hK hf)
    (tendsto_dist_bound_at_top_nhds_0 hf.left hK (dist x₀ (f x₀))),
have cauchy_seq (λ n, f^[n] x₀), by rwa [cauchy_seq_iff_tendsto_dist_at_top_0],
let ⟨x, hx⟩ := cauchy_seq_tendsto_of_complete this in
⟨x, fixed_point_of_tendsto_iterate (hf.to_uniform_continuous.continuous.tendsto x) ⟨x₀, hx⟩⟩

end contraction

end lipschitz_with
