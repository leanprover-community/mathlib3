/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.fekete
import analysis.inner_product_space.basic
import tactic.by_contra
import analysis.normed_space.dual

noncomputable theory
open_locale topological_space
open filter normed_space metric

variables {α β : Type*} [metric_space α] [metric_space β]

lemma exists_high_score (u : ℕ → ℝ) (hu : tendsto u at_top at_top) (N : ℕ) :
  ∃ n ≥ N, ∀ m ≤ n, u m ≤ u n :=
begin
  by_contra' hN,
  let M := (finset.image u (finset.range (N+1))).max' (by simp),
  have A : ∀ n, u n ≤ M,
  { assume n,
    induction n using nat.strong_induction_on with n IH,
    rcases le_total n N with hnN|hNn,
    { apply finset.le_max',
      simp,
      exact ⟨n, by linarith, rfl⟩ },
    { obtain ⟨m, m_le_n, hm⟩ : ∃ (m : ℕ), m ≤ n ∧ u n < u m := hN n hNn,
      have m_lt_n : m < n,
      { apply lt_of_le_of_ne m_le_n,
        rintros rfl,
        exact lt_irrefl _ hm },
      apply hm.le.trans (IH _ m_lt_n) } },
  obtain ⟨n, hn⟩ : ∃ n, M + 1 ≤ u n := (filter.tendsto_at_top.mp hu (M + 1)).exists,
  show false, by linarith [A n],
end

def semicontraction (f : α → β) :=
∀ x y, dist (f x) (f y) ≤ dist x y

namespace semicontraction

lemma comp {γ : Type*} [metric_space γ] {g : β → γ} {f : α → β}
  (hg : semicontraction g) (hf : semicontraction f) :
  semicontraction (g ∘ f) :=
λ x y, (hg (f x) (f y)).trans (hf x y)

lemma iterate {f : α → α} (h : semicontraction f) (n : ℕ) :
  semicontraction (f ^[n]) :=
begin
  induction n with n IH,
  { simp [semicontraction] },
  { simp [IH.comp h] }
end

variables {E : Type*} [inner_product_space ℝ E] [finite_dimensional ℝ E]
  {f : E → E} (h : semicontraction f)
include h

def u (n : ℕ) : ℝ := dist (0 : E) (f^[n] 0)

lemma u_subadditive : subadditive h.u :=
begin
  assume m n,
  calc h.u (m + n) = dist (0 : E) (f^[m + n] 0) : rfl
  ... ≤ dist (0 : E) (f^[m] 0) + dist (f^[m] 0) (f^[m+n] 0) : dist_triangle _ _ _
  ... = dist (0 : E) (f^[m] 0) + dist (f^[m] 0) (f^[m] (f^[n] 0)) :
    by simp [function.iterate_add_apply]
  ... ≤ dist (0 : E) (f^[m] 0) + dist (0 : E) (f^[n] 0) :
    add_le_add le_rfl (h.iterate _ _ _)
  ... = h.u m + h.u n : rfl
end

def l := h.u_subadditive.lim

lemma tendsto_lim : tendsto (λ n, h.u n / n) at_top (𝓝 h.l) :=
begin
  have B : bdd_below (set.range (λ (n : ℕ), h.u n / ↑n)),
  { refine ⟨0, λ x, _⟩,
    simp,
    rintros n rfl,
    simp [u, div_nonneg] },
  exact h.u_subadditive.tendsto_lim B,
end

lemma tendsto_sub_at_top {w : ℝ} (hw : w < h.l) :
  tendsto (λ (n : ℕ), h.u n - n * w) at_top at_top :=
begin
  have A : tendsto (λ n, h.u n / n - w) at_top (𝓝 (h.l - w)) :=
    h.tendsto_lim.sub tendsto_const_nhds,
  have : tendsto (λ (n : ℕ), (h.u n / n - w) * n) at_top at_top,
  { have I : 0 < h.l - w, by linarith,
    apply A.mul_at_top I,
    exact tendsto_coe_nat_at_top_at_top }, -- library_search
  apply tendsto.congr' _ this,
  apply eventually_at_top.2 ⟨1, λ n hn, _⟩,
  have n_ne_zero : n ≠ 0 := (zero_lt_one.trans_le hn).ne',
  field_simp [n_ne_zero],
end

lemma exists_dual_up_to_of_lt {w : ℝ} (hw : w < h.l) (N : ℕ) :
  ∃ (v : dual ℝ E), ∥v∥ ≤ 1 ∧ ∀ i ≤ N, v (f^[i] 0) ≤ - i * w :=
begin
  obtain ⟨n, Nn, hn⟩ : ∃ n ≥ N, ∀ m ≤ n, h.u m - m * w ≤ h.u n - n * w :=
    exists_high_score _ (h.tendsto_sub_at_top hw) N,
  obtain ⟨v, vnorm, hv⟩ : ∃ (v : dual ℝ E), ∥v∥ ≤ 1 ∧ v (-(f^[n] 0)) = norm (-(f^[n] 0)) :=
    exists_dual_vector'' ℝ (-(f^[n] 0)),
  refine ⟨v, vnorm, λ i hi, _⟩,
  have A : i ≤ n := hi.trans Nn,
  show v (f^[i] 0) ≤ -i * w, from calc
  v (f^[i] 0) = v (f^[i] 0 - (f^[n]) 0) - v (- (f^[n] 0)) :
    by simp only [continuous_linear_map.map_neg, sub_add_cancel, continuous_linear_map.map_sub,
                  sub_neg_eq_add] -- squeeze_simp
  ... ≤ 1 * ∥(f^[i]) 0 - (f^[n]) 0∥ - ∥-(f^[n]) 0∥ :
    begin
      rw hv,
      refine sub_le_sub ((le_abs_self _).trans _) le_rfl,
      rw ← real.norm_eq_abs,
      exact v.le_of_op_norm_le vnorm _,
    end
  ... = dist (f^[i] 0) (f^[i] (f^[n-i] 0)) - dist 0 (f^[n] 0) :
    by rw [← function.iterate_add_apply, one_mul, dist_eq_norm, dist_eq_norm, zero_sub,
           ← nat.add_sub_assoc A, nat.add_sub_cancel_left]
  ... ≤ dist 0 (f^[n-i] 0) - dist 0 (f^[n] 0) : sub_le_sub (h.iterate i _ _) le_rfl
  ... = h.u (n-i) - h.u n : rfl
  ... ≤ - n * w + (n-i : ℕ) * w : by linarith [hn (n-i) (nat.sub_le n i)]
  ... = - i * w : by { rw [nat.cast_sub A], ring }
end

lemma exists_dual : ∃ (v : dual ℝ E), ∥v∥ ≤ 1 ∧ ∀ i, v (f^[i] 0) ≤ -i * h.l :=
begin
  have : proper_space E := by apply_instance,
  have : proper_space (dual ℝ E) := by apply_instance,
  obtain ⟨w, -, w_lt, w_lim⟩ : ∃ (w : ℕ → ℝ), strict_mono w ∧ (∀ (n : ℕ), w n < h.l)
    ∧ tendsto w at_top (𝓝 h.l) := exists_seq_strict_mono_tendsto _,
  have : ∀ n, ∃ (v : dual ℝ E), ∥v∥ ≤ 1 ∧ ∀ i ≤ n, v (f^[i] 0) ≤ - i * w n :=
    λ n, h.exists_dual_up_to_of_lt (w_lt n) n,
  choose v hv using this,
  have : ∃ y ∈ closed_ball (0 : dual ℝ E) 1, ∃ (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (v ∘ φ) at_top (𝓝 y),
  { apply is_compact.tendsto_subseq,
    apply proper_space.is_compact_closed_ball,


  },
end

#exit

  have : ∀ n, v n ∈ metric.closed_ball (0 : dual ℝ E) 1 :=
    λ n, by simp [(hv n).1],
  have Z := is_compact.tendsto_subseq,
end


end semicontraction
