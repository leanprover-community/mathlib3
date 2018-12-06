/-
Copyright (c) 2018 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard
-/
--Working towards a proof of the Banach Contraction Theorem
import analysis.limits
import analysis.topology.metric_sequences
import data.complex.exponential

open filter
lemma tendsto_succ (X : Type*) (f : ℕ → X) (F : filter X) (H : tendsto f at_top F) :
tendsto (λ n, f (n + 1)) at_top F :=
tendsto.comp (tendsto_def.2 $ λ U HU,
  let ⟨a,Ha⟩ := mem_at_top_sets.1 HU in
  mem_at_top_sets.2 ⟨a,λ x Hx,Ha _ $ le_trans Hx $ by simp⟩) H

local attribute [instance, priority 0] classical.prop_decidable
noncomputable theory

open function
--The following material comes from "Metric Spaces and Topology" by Sutherland
--Half of Proposition 17.4
theorem complete_of_complete_of_uniform_cts_bij {α : Type*} [metric_space α] {β : Type*} [metric_space β] (f : α → β)
    (g : β → α) (Hf : uniform_continuous f) (Hg : uniform_continuous g) (left_inv : function.left_inverse g f)
    (right_inv : function.right_inverse g f) : complete_space α → complete_space β :=
begin
  rintro ⟨H1⟩,
  split,
  intros filt Hfilt,
  cases H1 (cauchy_map Hg Hfilt) with x H_converges_to_x,
  existsi f x,
  rw [map_le_iff_le_comap,
      ←filter.map_eq_comap_of_inverse (id_of_right_inverse right_inv) (id_of_left_inverse left_inv)] at H_converges_to_x,
  exact le_trans H_converges_to_x (continuous.tendsto Hf.continuous x)
end

--Proposition 17.4
theorem complete_iff_of_uniform_cts_bij {α : Type*} [metric_space α] {β : Type*} [metric_space β] (f : α → β) 
    (g : β → α) (Hf : uniform_continuous f) (Hg : uniform_continuous g) (left_inv : function.left_inverse g f)
    (right_inv : function.right_inverse g f) : complete_space α ↔ complete_space β := 
        ⟨complete_of_complete_of_uniform_cts_bij f g Hf Hg left_inv right_inv,
        complete_of_complete_of_uniform_cts_bij g f Hg Hf right_inv left_inv⟩

open nat
def iteration_map {α : Type*} (f : α → α) (start : α) : ℕ → α
| zero := start
| (succ x) := f (iteration_map x)

--Definition 17.24
def is_contraction {α : Type*} [metric_space α] (f : α → α) := 
∃ (k : ℝ) (H1 : k < 1) (H2 : 0 < k), ∀ (x y : α), dist (f x) (f y) ≤ k* (dist x y)

lemma fixed_point_of_iteration_limit' {α : Type*} [topological_space α] [t2_space α] {f : α → α} {p : α} :
  continuous f → (∃ p₀ : α, tendsto (iteration_map f p₀) at_top (nhds p)) → f p = p :=
begin
  intros hf hp,
  cases hp with p₀ hp,
  apply @tendsto_nhds_unique α ℕ _ _ (f ∘ iteration_map f p₀) at_top (f p) p,
  { exact at_top_ne_bot },
  { exact tendsto.comp hp (continuous.tendsto hf p) },
  { exact tendsto_succ α (iteration_map f p₀) (nhds p) hp },
end

lemma fixed_point_of_iteration_limit {α : Type*} [topological_space α] [t2_space α] {f : α → α} {p : α} :
  continuous f → (∃ p₀ : α, tendsto (λ n, f ^[n] p₀) at_top (nhds p)) → p = f p :=
begin
  intros hf hp,
  cases hp with p₀ hp,
  apply @tendsto_nhds_unique α ℕ _ _ (λ n, (f ^[succ n] p₀)) at_top p (f p),
  { exact at_top_ne_bot },
  { rewrite @tendsto_comp_succ_at_top_iff α (λ n, f ^[n] p₀) (nhds p),
    exact hp },
  { rewrite funext (λ n, iterate_succ' f n p₀),
    exact tendsto.comp hp (continuous.tendsto hf p) },
end

def lipschitz {α : Type*} [metric_space α] (K : ℝ) (f : α → α) := ∀ (x y : α), dist (f x) (f y) ≤ K * (dist x y)

lemma uniform_continuous_of_lipschitz {α : Type*} [metric_space α] {K : ℝ} {f : α → α} :
  0 ≤ K → lipschitz K f → uniform_continuous f :=
begin
  intros hK₀ hf,
  apply iff.mpr uniform_continuous_of_metric,
  intros ε hε,
  cases eq_or_lt_of_le hK₀ with hz hp,
  { use (1 : ℝ),
    use zero_lt_one,
    intros x y hd,
    apply lt_of_le_of_lt (hf x y),
    rewrite [←hz, zero_mul],
    exact hε },
  { use ε / K,
    use div_pos_of_pos_of_pos hε hp,
    intros x y hd,
    apply lt_of_le_of_lt (hf x y),
    rewrite ←mul_div_cancel' ε (ne_of_gt hp),
    exact mul_lt_mul_of_pos_left hd hp },
end

lemma iterated_lipschitz_of_lipschitz {α : Type*} [metric_space α] {K : ℝ} {f : α → α} :
   0 ≤ K → lipschitz K f → ∀ (n : ℕ), lipschitz (K ^n) (f ^[n]) :=
begin
  intros hK₀ hf n,
  induction n with n ih,
    intros x y,
    rewrite [pow_zero K, one_mul, iterate_zero f x, iterate_zero f y],
  intros x y,
  repeat { rewrite iterate_succ' },
  apply le_trans (hf (f ^[n] x) (f ^[n] y)),
  rewrite [pow_succ K n, mul_assoc],
  exact mul_le_mul_of_nonneg_left (ih x y) hK₀,
end

lemma palais_inequality {α : Type*} [metric_space α] {K : ℝ} {f : α → α} :
  K < 1 → lipschitz K f → ∀ (x y : α), dist x y ≤ (dist x (f x) + dist y (f y)) / (1 - K) :=
begin
  intros hK₁ hf x y,
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
  exact hf x y,
end

theorem fixed_point_unique {α : Type*} [metric_space α] {K : ℝ} {f : α → α} :
  K < 1 → lipschitz K f → ∀ (p : α), p = f p → ∀ (p' : α), p' = f p' → p = p' :=
begin
  intros hK₁ hf p hp p' hp',
  apply iff.mp dist_le_zero,
  apply le_trans,
  exact palais_inequality hK₁ hf p p',
  rewrite iff.mpr dist_eq_zero hp,
  rewrite iff.mpr dist_eq_zero hp',
  norm_num,
end

lemma cauchy_of_contraction {α : Type*} [metric_space α] {K : ℝ} {f : α → α} :
  0 ≤ K → K < 1 → lipschitz K f → ∀ (p₀ : α) (m n : ℕ), dist (f ^[m] p₀) (f ^[n] p₀) ≤ (K ^m + K ^n) * dist p₀ (f p₀) / (1 - K) :=
begin
  intros hK₀ hK₁ hf p₀ m n,
  apply le_trans,
  exact palais_inequality hK₁ hf (f ^[m] p₀) (f ^[n] p₀),
  apply div_le_div_of_le_of_pos _ (sub_pos_of_lt hK₁),
  have h : ∀ (n : ℕ), dist (f ^[n] p₀) (f (f ^[n] p₀)) ≤ K ^n * dist p₀ (f p₀),
    intro n,
    rewrite [←iterate_succ' f n p₀, iterate_succ f n p₀],
    exact iterated_lipschitz_of_lipschitz hK₀ hf n p₀ (f p₀),
  rewrite add_mul,
  apply add_le_add,
  { exact h m },
  { exact h n },
end

--Banach's Fixed Point Theorem (Exists Statement)
theorem Banach_fixed_point_exists {α : Type*} [metric_space α] [complete_space α] (H1 : nonempty α) {f : α → α} (H : is_contraction f)
: ∃ (p : α), f p = p :=
begin
  cases classical.exists_true_of_nonempty H1 with start trivial,
  let seq := iteration_map f start,
  let H' := H,
  rcases H with ⟨K, HK1, HK2, Hf⟩,
  have consecutive_distance : ∀ n, dist (seq (n+1)) (seq (n)) ≤ K^n * dist (seq 1) (seq 0),
  { intro n, induction n with N HN,
    show dist (seq 1) (seq 0) ≤ 1 * dist (seq 1) (seq 0),
    rw one_mul,
    have K_times_HN := (mul_le_mul_left HK2).2 HN,
    rw ← mul_assoc at K_times_HN,
    exact le_trans (Hf (seq (N+1)) (seq (N+0))) K_times_HN },
  
  --Now repeatedly use the triangle inequality
  let sum_consecutives := λ m n, finset.sum (finset.range (m)) (λ x, dist (seq (n+x+1)) (seq (n+x))), 
  have le_sum_consecutives : ∀ m n, dist (seq (n+m)) (seq n) ≤ sum_consecutives m n,
  { intros m n,
    induction m with M HM,
    { rw add_zero, rw dist_self,
      apply finset.zero_le_sum,
      intros n Hn, exact dist_nonneg },
    have sum_cons_insert : sum_consecutives (succ M) n = 
        finset.sum (insert (M) (finset.range (M))) (λ (x : ℕ), dist (seq (n + x + 1)) (seq (n + x))),
    { have : (finset.range (succ M)) = insert M (finset.range M),
      { rw finset.range_succ },
      dsimp [sum_consecutives],
      rw this },
    have dist_triangleone : dist (seq (n + succ M)) (seq n) ≤ 
        dist (seq (n + succ M)) (seq (n+M)) + dist (seq (n + M)) (seq n) := dist_triangle _ _ _,
    refine le_trans dist_triangleone _,
    rw sum_cons_insert,
    rw finset.sum_insert (by rw finset.mem_range; exact lt_irrefl M),
    apply add_le_add_left, exact HM },

  let sum_consecutives_K := λ m n, finset.sum (finset.range (m)) (λ x,(K^(n+x))*dist (seq 1) (seq 0)),

  have sum_le : ∀ m n, sum_consecutives m n ≤ sum_consecutives_K m n,
  { intros m n, apply finset.sum_le_sum,
    intros x Hx, exact consecutive_distance (n+x) },
  
  have take_out_dist : ∀ m n, sum_consecutives_K m n = 
      (finset.sum (finset.range m) (λ (x : ℕ), K ^ (x)))* (K^n)*dist (seq 1) (seq 0),
  { intros m n, rw [finset.sum_mul, finset.sum_mul],
    simp only [(_root_.pow_add _ _ _).symm, add_comm] },

  replace take_out_dist : ∀ (m n : ℕ), sum_consecutives_K m n = (1 - K ^ m) / (1 - K) * K ^ n * dist (seq 1) (seq 0),
  { intros m n, rw [← geo_sum_eq _ (ne_of_lt HK1), take_out_dist m n] },
  
  have : ∀ (m : ℕ), (1 - K ^ m) ≤ 1,
  { intros m, refine sub_le_self 1 ((pow_nonneg (le_of_lt HK2)) m) },

  have this2 : ∀ (n : ℕ), 0 ≤ (1 - K)⁻¹ * (K ^ n * dist (seq 1) (seq 0)),
  { intro n, rw ← mul_assoc, 
    refine mul_nonneg (mul_nonneg (le_of_lt (inv_pos'.2 (by linarith))) (le_of_lt ((pow_pos HK2) n))) dist_nonneg },

  have k_sum_le_k_sum : ∀ (m n : ℕ), (1 - K ^ m) / (1 - K) * K ^ n * dist (seq 1) (seq 0) 
      ≤ 1 / (1 - K) *(K ^ n)* dist (seq 1) (seq 0),
  { intros m n, rw [mul_assoc, mul_assoc, div_eq_mul_inv, mul_assoc, div_eq_mul_inv, mul_assoc],
    refine mul_le_mul_of_nonneg_right (this m) (this2 n) },

  have k_to_n_converges := tendsto_pow_at_top_nhds_0_of_lt_1 (le_of_lt HK2) HK1,
  have const_converges : filter.tendsto (λ (n : ℕ), 1 / (1 - K) * dist (seq 1) (seq 0)) 
      filter.at_top (nhds (1 / (1 - K) * dist (seq 1) (seq 0))) := tendsto_const_nhds,

  have k_sum_converges := tendsto_mul k_to_n_converges const_converges, 
  dsimp at k_sum_converges, rw [zero_mul, tendsto_at_top_metric] at k_sum_converges,

  have equal : ∀ (n : ℕ), K ^ n * (1 / (1 + -K) * dist (seq 1) (seq 0)) =  1 / (1 - K) * K ^ n * dist (seq 1) (seq 0),
  { intro n, conv in (_ * K ^ n) begin rw mul_comm, end, rw mul_assoc, refl },
  
  have cauchy_seq : ∀ ε > 0, ∃ (N : ℕ), ∀ {m n}, m ≥ N → n ≥ N → dist (seq n) (seq m) < ε,
  { intros ε Hε,
    cases k_sum_converges ε Hε with N HN,
    existsi N,
    intros s r Hs Hr,
    wlog h : s ≤ r,
    { have := HN _ Hs,
      rw real.dist_eq at this, rw sub_zero at this,
      replace := (abs_lt.1 this).2, rw equal at this,
      have this2 := λ m, lt_of_le_of_lt (k_sum_le_k_sum m s) this,
      have this3 : ∀ (m : ℕ), sum_consecutives_K m s < ε,
      { intro m, rw take_out_dist, exact this2 m },
      have this4 := λ m, lt_of_le_of_lt (sum_le m s) (this3 m),
      have this5 := λ m, lt_of_le_of_lt (le_sum_consecutives m s) (this4 m),
      cases le_iff_exists_add.1 h with c Hc, rw Hc,
      exact this5 c },
    rw dist_comm, exact this_1 Hr Hs },
    
  rw ← cauchy_seq_metric at cauchy_seq,
  cases @complete_space.complete _ _ _inst_2 _ cauchy_seq with p Hseq_tendsto_p,
  existsi p,

  have f_cont : continuous f := uniform_continuous.continuous (uniform_continuous_of_lipschitz (le_of_lt HK2) Hf),
  apply fixed_point_of_iteration_limit' f_cont,
  exact exists.intro start Hseq_tendsto_p,
end

def Banach's_fixed_point {α : Type*} [metric_space α] [complete_space α] (H1 : nonempty α) {f : α → α} (H : is_contraction f)
: α := classical.some (Banach_fixed_point_exists H1 H)

theorem Banach's_fixed_point_is_fixed_point {α : Type*} [metric_space α] [complete_space α] (H1 : nonempty α) {f : α → α} (H : is_contraction f)
: f (Banach's_fixed_point H1 H) = Banach's_fixed_point H1 H := classical.some_spec (Banach_fixed_point_exists H1 H)

theorem Banach's_fixed_point_is_unique {α : Type*} [metric_space α] [complete_space α] (H1 : nonempty α) {f : α → α} (H : is_contraction f)
: ∀ (p : α), f p = p → p = Banach's_fixed_point H1 H :=
begin 
  intros y Hy,
  by_contra Hnot,
  let p := Banach's_fixed_point H1 H,
  have H4 := @dist_nonneg _ _ p y,
  have H3 : 0 < dist p y, from iff.mpr dist_pos (λ h, Hnot (eq.symm h)),
  let H' := H,
  rcases H with ⟨K,HK1,_,Hf⟩, 
  have := Hf p y, rw [Hy, (Banach's_fixed_point_is_fixed_point H1 H')] at this,
  have this1_5 : K * dist p y < 1 * dist p y,
  { apply lt_of_sub_pos, rw ← mul_sub_right_distrib, refine mul_pos (sub_pos_of_lt HK1) H3 },

  have this2 : dist p y < 1 * dist p y,
  { refine lt_of_le_of_lt this this1_5 },
  rw one_mul at this2, exact lt_irrefl (dist p y) this2,
end
