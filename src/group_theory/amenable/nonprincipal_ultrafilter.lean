/-
Copyright (c) 2022 Matthias Uschold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Uschold.
-/

import order.filter.basic
import data.real.basic
import topology.basic
import topology.sequences

import topology.continuous_function.bounded

/-!

# Nonprincipal ultrafilters

This file provides some statements about nonprincipal ultrafilters
(mainly by modifying slightly the theorems in the mathlib about ultrafilters).

We mainly want to use `hyperfilter ℕ`, the/one ultrafilter extending the cofinite filter

## Implementation Notes

TODO : These statements are probably already in the mathlib
(probably in some more general form). These lemmas may be
replaced by / moved to different parts of the mathlib.


## Tags

hyperfilter, ultrafilter, ultrafilter convergence theorem

-/

open classical
open filter


theorem ultrafilter_convergence
  {X : Type*} [topological_space X]
  {S: set X}
  (S_cmpt : is_compact S)
  {fil: ultrafilter ℕ}
  {a: ℕ → X }
  (an_in_S: ∀ n, a n ∈ S)
  : ∃ x, filter.tendsto a fil (nhds x)
:= begin
  unfold filter.tendsto,
  have hx : (∃ x ∈ S, (filter.map a fil) ≤ nhds x),
  {
    rw ← ultrafilter.coe_map _ _,
    apply is_compact.ultrafilter_le_nhds S_cmpt,
    simp,
    have : a⁻¹' S = set.univ,
    {
      ext n,
      split,
        intro,
        simp,
      intro,
      simp,
      exact an_in_S n,
    },
    rw this,
    exact fil.univ_sets,
  },
  rcases hx with ⟨x, ⟨xinS, hx⟩⟩,
  use x,
  exact hx,
end


lemma ultrafilter_convergence_R
  {fil: ultrafilter ℕ}
  {a: ℕ → ℝ }
  (a_bounded : ∃ (C:ℝ), ∀ (n:ℕ), abs (a n) ≤ C)
  : ∃ (x:ℝ), filter.tendsto a fil (nhds x)
:= begin
  rcases a_bounded with ⟨C, a_bounded⟩,
  let S : set ℝ := set.Icc (-C) C,
  have : is_compact S := is_compact_Icc,
  apply ultrafilter_convergence this,
  assume n,
  specialize a_bounded n,
  dsimp[S],
  split,
    exact neg_le_of_abs_le a_bounded,
  exact le_of_abs_le a_bounded,
end


lemma conv_hyperfilter_of_conv
  {a: ℕ → ℝ}
  {fil: filter ℝ}
  (ha : filter.tendsto a filter.at_top fil)
  : filter.tendsto a (hyperfilter ℕ) fil
:= begin
  rw ← nat.cofinite_eq_at_top at ha,
  exact  filter.tendsto.mono_left ha filter.hyperfilter_le_cofinite,
end



lemma limit_positive_of_positive_ultrafilter
  {a: ℕ → ℝ}
  {x : ℝ}
  (a_conv_x : filter.tendsto a (hyperfilter ℕ) (nhds x))
  (apos : ∀ n, a n ≥ 0)
  : x ≥ 0
:= begin
  by_contradiction xneg,
  have Iio_in_nhds: set.Iio (0:ℝ) ∈ nhds x,
  {
    rw mem_nhds_iff,
    use set.Iio (0:ℝ),
    simp,
    split,
      exact is_open_Iio,
    by linarith only[xneg],
  },

  rw filter.tendsto_def at a_conv_x,

  let s : set ℝ  := set.Iio (0:ℝ),

  -- This yields the contradiction as this preimage is empty
  have preimg_in_ultrafilter: a ⁻¹' s ∈ ↑(hyperfilter ℕ)
      := a_conv_x s (by simp[Iio_in_nhds]),
  have : a ⁻¹' s = ∅,
  {
    rw ←  set.not_nonempty_iff_eq_empty,
    unfold set.nonempty,
    by_contradiction n_in_preimg,
    rcases n_in_preimg with ⟨n, n_in_preimg⟩,
    have : a n ∈ s := set.mem_preimage.mp n_in_preimg,
    have : a n < 0,
    {
      dsimp[s] at this,
      exact set.mem_Iio.mp this,
    },
    by linarith [apos n],
  },
  rw this at preimg_in_ultrafilter,
  exact filter.nmem_hyperfilter_of_finite (set.finite_empty) preimg_in_ultrafilter,
end




lemma limit_wedge_zero
  {a b: ℕ → ℝ}
  (a_le_b : ∀ n, |a n| ≤ b n)
  (b_conv_0 : filter.tendsto b filter.at_top (nhds 0))
  : filter.tendsto a filter.at_top (nhds 0)
:= begin
  rw metric.tendsto_at_top at *,
  intros ε εpos,
  specialize b_conv_0 ε εpos,
  rcases b_conv_0 with ⟨N, hb⟩,
  use N,
  intros n ngeN,
  specialize hb n ngeN,
  specialize a_le_b n,
  simp at hb,
  simp,
  calc  |a n |
      ≤ b n
        : a_le_b
  ... ≤ |b n|
        : le_abs_self (b n)
  ... < ε
        : hb,
end
