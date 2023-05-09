/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.instances.real
import order.filter.archimedean

/-!
# Convergence of subadditive sequences

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A subadditive sequence `u : ℕ → ℝ` is a sequence satisfying `u (m + n) ≤ u m + u n` for all `m, n`.
We define this notion as `subadditive u`, and prove in `subadditive.tendsto_lim` that, if `u n / n`
is bounded below, then it converges to a limit (that we denote by `subadditive.lim` for
convenience). This result is known as Fekete's lemma in the literature.
-/

noncomputable theory
open set filter
open_locale topology

/-- A real-valued sequence is subadditive if it satisfies the inequality `u (m + n) ≤ u m + u n`
for all `m, n`. -/
def subadditive (u : ℕ → ℝ) : Prop :=
∀ m n, u (m + n) ≤ u m + u n

namespace subadditive

variables {u : ℕ → ℝ} (h : subadditive u)
include h

/-- The limit of a bounded-below subadditive sequence. The fact that the sequence indeed tends to
this limit is given in `subadditive.tendsto_lim` -/
@[irreducible, nolint unused_arguments]
protected def lim := Inf ((λ (n : ℕ), u n / n) '' (Ici 1))

lemma lim_le_div (hbdd : bdd_below (range (λ n, u n / n))) {n : ℕ} (hn : n ≠ 0) :
  h.lim ≤ u n / n :=
begin
  rw subadditive.lim,
  apply cInf_le _ _,
  { rcases hbdd with ⟨c, hc⟩,
    exact ⟨c, λ x hx, hc (image_subset_range _ _ hx)⟩ },
  { apply mem_image_of_mem,
    exact zero_lt_iff.2 hn }
end

lemma apply_mul_add_le (k n r) : u (k * n + r) ≤ k * u n + u r :=
begin
  induction k with k IH, { simp only [nat.cast_zero, zero_mul, zero_add] },
  calc
  u ((k+1) * n + r)
      = u (n + (k * n + r)) : by { congr' 1, ring }
  ... ≤ u n + u (k * n + r) : h _ _
  ... ≤ u n + (k * u n + u r) : add_le_add_left IH _
  ... = (k+1 : ℕ) * u n + u r : by simp; ring
end

lemma eventually_div_lt_of_div_lt {L : ℝ} {n : ℕ} (hn : n ≠ 0) (hL : u n / n < L) :
  ∀ᶠ p in at_top, u p / p < L :=
begin
  have I : ∀ (i : ℕ), 0 < i → (i : ℝ) ≠ 0,
  { assume i hi, simp only [hi.ne', ne.def, nat.cast_eq_zero, not_false_iff] },
  obtain ⟨w, nw, wL⟩ : ∃ w, u n / n < w ∧ w < L := exists_between hL,
  obtain ⟨x, hx⟩ : ∃ x, ∀ i < n, u i - i * w ≤ x,
  { obtain ⟨x, hx⟩ : bdd_above (↑(finset.image (λ i, u i - i * w) (finset.range n))) :=
      finset.bdd_above _,
    refine ⟨x, λ i hi, _⟩,
    simp only [upper_bounds, mem_image, and_imp, forall_exists_index, mem_set_of_eq,
      forall_apply_eq_imp_iff₂, finset.mem_range, finset.mem_coe, finset.coe_image] at hx,
    exact hx _ hi },
  have A : ∀ (p : ℕ), u p ≤ p * w + x,
  { assume p,
    let s := p / n,
    let r := p % n,
    have hp : p = s * n + r, by rw [mul_comm, nat.div_add_mod],
    calc u p = u (s * n + r) : by rw hp
    ... ≤ s * u n + u r : h.apply_mul_add_le _ _ _
    ... = s * n * (u n / n) + u r : by { field_simp [I _ hn.bot_lt], ring }
    ... ≤ s * n * w + u r : add_le_add_right
      (mul_le_mul_of_nonneg_left nw.le (mul_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _))) _
    ... = (s * n + r) * w + (u r - r * w) : by ring
    ... = p * w + (u r - r * w) : by { rw hp, simp only [nat.cast_add, nat.cast_mul] }
    ... ≤ p * w + x : add_le_add_left (hx _ (nat.mod_lt _ hn.bot_lt)) _ },
  have B : ∀ᶠ p in at_top, u p / p ≤ w + x / p,
  { refine eventually_at_top.2 ⟨1, λ p hp, _⟩,
    simp only [I p hp, ne.def, not_false_iff] with field_simps,
    refine div_le_div_of_le_of_nonneg _ (nat.cast_nonneg _),
    rw mul_comm,
    exact A _ },
  have C : ∀ᶠ (p : ℕ) in at_top, w + x / p < L,
  { have : tendsto (λ (p : ℕ), w + x / p) at_top (𝓝 (w + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_at_top tendsto_coe_nat_at_top_at_top),
    rw add_zero at this,
    exact (tendsto_order.1 this).2 _ wL },
  filter_upwards [B, C] with _ hp h'p using hp.trans_lt h'p,
end

/-- Fekete's lemma: a subadditive sequence which is bounded below converges. -/
theorem tendsto_lim (hbdd : bdd_below (range (λ n, u n / n))) :
  tendsto (λ n, u n / n) at_top (𝓝 h.lim) :=
begin
  refine tendsto_order.2 ⟨λ l hl, _, λ L hL, _⟩,
  { refine eventually_at_top.2
      ⟨1, λ n hn, hl.trans_le (h.lim_le_div hbdd ((zero_lt_one.trans_le hn).ne'))⟩ },
  { obtain ⟨n, npos, hn⟩ : ∃ (n : ℕ), 0 < n ∧ u n / n < L,
    { rw subadditive.lim at hL,
      rcases exists_lt_of_cInf_lt (by simp) hL with ⟨x, hx, xL⟩,
      rcases (mem_image _ _ _).1 hx with ⟨n, hn, rfl⟩,
      exact ⟨n, zero_lt_one.trans_le hn, xL⟩ },
    exact h.eventually_div_lt_of_div_lt npos.ne' hn }
end

end subadditive
