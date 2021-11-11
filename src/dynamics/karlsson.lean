/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.fekete
import analysis.inner_product_space.dual
import tactic.by_contra
import analysis.normed_space.dual

/-!
# Karlsson's proof of the existence of an asymptotic vector for semicontractions
-/

noncomputable theory
open_locale topological_space
open filter normed_space metric

notation `⟪`x`, `y`⟫` := @inner ℝ _ _ x y


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

/-- A semicontraction between two metric spaces is a map that does not increase distances. -/
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

/-- A convenient notation for the distance between `0` and `f^n 0`. -/
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

/-- `h.l` is such that `h.u n` grows like `n * h.l`. -/
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

lemma l_nonneg : 0 ≤ h.l :=
ge_of_tendsto' h.tendsto_lim (λ n, div_nonneg dist_nonneg (nat.cast_nonneg _))

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
  obtain ⟨v, vnorm, hv⟩ : ∃ (v : dual ℝ E), ∥v∥ ≤ 1 ∧ v (-(f^[n] 0)) = ∥-(f^[n] 0)∥ :=
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
  obtain ⟨w, -, w_lt, w_lim⟩ : ∃ (w : ℕ → ℝ), strict_mono w ∧ (∀ (n : ℕ), w n < h.l)
    ∧ tendsto w at_top (𝓝 h.l) := exists_seq_strict_mono_tendsto _,
  have : ∀ n, ∃ (y : dual ℝ E), ∥y∥ ≤ 1 ∧ ∀ i ≤ n, y (f^[i] 0) ≤ - i * w n :=
    λ n, h.exists_dual_up_to_of_lt (w_lt n) n,
  choose y hy using this,
  obtain ⟨v, v_mem, φ, φ_mono, φlim⟩ : ∃ v ∈ closed_ball (0 : dual ℝ E) 1, ∃ (φ : ℕ → ℕ),
    strict_mono φ ∧ tendsto (y ∘ φ) at_top (𝓝 v),
  { -- dual ℝ E est propre
    refine is_compact.tendsto_subseq (proper_space.is_compact_closed_ball _ _) _,
    assume n,
    simp [(hy n).1] },
  refine ⟨v, by simpa using v_mem, λ i, _⟩,
  have A : tendsto (λ n, ((y ∘ φ) n) (f^[i] 0)) at_top (𝓝 (v (f^[i] 0))) :=
    ((is_bounded_bilinear_map_apply.is_bounded_linear_map_left (f^[i] 0)).continuous.tendsto _)
      .comp φlim,
  have B : tendsto (λ n, -(i : ℝ) * w (φ n)) at_top (𝓝 (- i * h.l)) :=
    (tendsto_const_nhds.mul w_lim).comp φ_mono.tendsto_at_top,
  have C : ∀ᶠ n in at_top, ((y ∘ φ) n) (f^[i] 0) ≤ - i * w (φ n),
  { apply eventually_at_top.2 ⟨i, λ n hn, _⟩,
    apply (hy (φ n)).2 i,
    exact le_trans hn (φ_mono.id_le n) },
  exact le_of_tendsto_of_tendsto A B C
end

lemma exists_asymp_vector :
  ∃ (v : E), ∥v∥ ≤ 1 ∧ ∀ (i : ℕ), (i : ℝ) * h.l ≤ ⟪v, (f^[i] 0)⟫ :=
begin
  obtain ⟨v', v'_norm, hv'⟩ : ∃ (v' : dual ℝ E), ∥v'∥ ≤ 1 ∧ ∀ i, v' (f^[i] 0) ≤ -i * h.l :=
    h.exists_dual,
  let v := (inner_product_space.to_dual ℝ E).symm (-v'),
  refine ⟨v, by simpa using v'_norm, λ i, _⟩,
  simp [v],
  linarith [hv' i]
end

/-- A semicontraction on a finite-dimensional vector space admits an asymptotic
translation vector. -/
theorem exists_tendsto_div :
  ∃ (v : E), tendsto (λ (n : ℕ), (1 / (n : ℝ)) • (f^[n] 0)) at_top (𝓝 v) :=
begin
  obtain ⟨v₀, v₀_norm, h₀⟩ : ∃ (v : E), ∥v∥ ≤ 1 ∧ ∀ (i : ℕ), (i : ℝ) * h.l ≤ ⟪v, (f^[i] 0)⟫ :=
    h.exists_asymp_vector,
  let v := h.l • v₀,
  use v,
  have A : ∀ᶠ (n : ℕ) in at_top,
    ∥(1 / (n : ℝ)) • (f^[n] 0) - v∥^2 ≤ (h.u n / n)^2 - h.l^2,
  { apply eventually_at_top.2 ⟨1, λ n hn, _⟩,
    have n_ne_zero : n ≠ 0 := (zero_lt_one.trans_le hn).ne',
    calc ∥(1 / (n : ℝ)) • (f^[n] 0) - v∥ ^ 2 =
    ∥(1 / (n : ℝ)) • (f^[n] 0)∥^2 - 2 * ⟪(1 / (n : ℝ)) • (f^[n] 0), v⟫ + ∥v∥^2 :
      norm_sub_sq_real
    ... = (h.u n / n)^2 - 2 * h.l / n * ⟪v₀, (f^[n] 0)⟫ + h.l^2 * ∥v₀∥^2 :
       begin
        congr' 2,
        { simp [norm_smul, real.norm_eq_abs, u, dist_zero_left, div_eq_inv_mul, mul_pow] },
        { simp [real_inner_smul_left, real_inner_smul_right, div_eq_inv_mul, real_inner_comm],
          ring },
        { simp [norm_smul, real.norm_eq_abs, mul_pow] }
      end
    ... ≤ (h.u n / n)^2 - 2 * h.l / n * (n * h.l) + h.l^2 * 1^2 :
      begin
        refine add_le_add (sub_le_sub le_rfl _) _,
        { apply mul_le_mul_of_nonneg_left (h₀ n),
          exact mul_nonneg (mul_nonneg zero_le_two h.l_nonneg) (by simp) },
        { refine mul_le_mul_of_nonneg_left _ (sq_nonneg _),
          exact pow_le_pow_of_le_left (norm_nonneg _) v₀_norm _ }
      end
    ... = (h.u n / n)^2 - h.l^2 : by { field_simp [n_ne_zero], ring } },
  have B : tendsto (λ (n : ℕ), (h.u n / n)^2 - h.l^2) at_top (𝓝 (h.l^2 - h.l^2)) :=
    (h.tendsto_lim.pow 2).sub tendsto_const_nhds,
  have C : tendsto (λ (n : ℕ), ∥(1 / (n : ℝ)) • (f^[n] 0) - v∥^2) at_top (𝓝 0),
  { rw [sub_self] at B,
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds B _ A,
    exact eventually_of_forall (λ n, by simp) },
  have D : tendsto (λ (n : ℕ), ∥(1 / (n : ℝ)) • (f^[n] 0) - v∥) at_top (𝓝 0),
    by { convert C.sqrt; simp },
  exact tendsto_iff_norm_tendsto_zero.2 D,
end






/-- Attention: si on ne fait pas attention à l'énoncé, on peut donner une preuve triviale
d'un résultat stupide. -/
lemma wrong_exists_tendsto_div' :
  ∃ (v : E), tendsto (λ (n : ℕ), (1 / n) • (f^[n] 0)) at_top (𝓝 v) :=
⟨(0 : E), tendsto_const_nhds.congr' $
  eventually_at_top.2 ⟨2, λ n hn, by simp [nat.div_eq_of_lt hn]⟩⟩

/-- Version un peu plus détaillée du précédent -/
lemma wrong_exists_tendsto_div :
  ∃ (v : E), tendsto (λ (n : ℕ), (1 / n) • (f^[n] 0)) at_top (𝓝 v) :=
begin
  use 0,
  have A : ∀ n ≥ 2, 1/n = 0,
  { assume n hn,
    exact nat.div_eq_of_lt hn },
  have : tendsto (λ (n : ℕ), (0 : E)) at_top (𝓝 0) := tendsto_const_nhds,
  apply tendsto.congr' _ this,
  apply eventually_at_top.2 ⟨2, _⟩,
  assume n hn,
  simp [A n hn]
end


end semicontraction

#lint
