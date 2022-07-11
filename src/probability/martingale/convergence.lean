/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability.martingale.upcrossing

/-!

# Maringale convergence theorems

-/

open topological_space filter
open_locale nnreal ennreal measure_theory probability_theory big_operators topological_space

namespace measure_theory

variables {α ι : Type*} {m0 : measurable_space α} {μ : measure α} {ℱ : filtration ℕ m0}
variables {a b : ℝ} {f : ℕ → α → ℝ} {N : ℕ} {n m : ℕ} {x : α}

/-! We will now begin to prove the martingale convergence theorem.

Firstly, we want to show a real sequence `x` converges if
(a) `limsup |x| < ∞`,
(b) For all `a < b : ℚ` we have `sup N, upcrossing_before a b x N < ∞`.

With this, for all `x` satisfying `limsup |λ n, f n x| < ∞` and
for all `a < b : ℚ`, `sup N, upcrossing_before a b f N x < ∞`, we have `λ n, f n x` converges.

Assuming `f` is L¹-bounded, using Fatou's lemma,
we have `𝔼[limsup |f|] ≤ limsup 𝔼[|f|] < ∞` implying `limsup |f| < ∞ a.e`. Furthermore, by
the upcrossing_before lemma, `sup N, upcrossing_before a b f N < ∞ a.e.` implying `f` converges pointwise almost
everywhere.

-/

/-- If a realization of a stochastic process has bounded upcrossing_befores from below `a` to above `b`,
then that realization does not frequently visit both below `a` and above `b`. -/
lemma not_frequently_of_upcrossing_lt_top (hab : a < b) (hx : upcrossing a b f x < ∞) :
  ¬((∃ᶠ n in at_top, f n x < a) ∧ (∃ᶠ n in at_top, b < f n x)) :=
begin
  rw upcrossing_lt_top_iff at hx,
  replace hx : ∃ k, ∀ N, upcrossing_before a b f N x < k,
  { obtain ⟨k, hk⟩ := hx,
    exact ⟨k + 1, λ N, lt_of_le_of_lt (hk N) k.lt_succ_self⟩ },
  rintro ⟨h₁, h₂⟩,
  rw frequently_at_top at h₁ h₂,
  refine not_not.2 hx _,
  push_neg,
  intro k,
  induction k with k ih,
  { simp only [zero_le', exists_const] },
  { obtain ⟨N, hN⟩ := ih,
    obtain ⟨N₁, hN₁, hN₁'⟩ := h₁ N,
    obtain ⟨N₂, hN₂, hN₂'⟩ := h₂ N₁,
    exact ⟨(N₂ + 1), nat.succ_le_of_lt $ lt_of_le_of_lt hN
      (upcrossing_lt_upcrossing_of_exists_upcrossing hab hN₁ hN₁' hN₂ hN₂')⟩ }
end

/-- A realization of a stochastic process with bounded upcrossings and bounded limit infimums is
convergent. -/
lemma tendsto_of_bdd_uncrossing {x : α}
  (hf₁ : ∃ R, at_top.liminf (λ n, |f n x|) < R)
  (hf₂ : ∀ a b : ℚ, a < b → upcrossing a b f x < ∞) :
  ∃ c, tendsto (λ n, f n x) at_top (𝓝 c) :=
begin
  refine tendsto_of_no_upcrossings rat.dense_range_cast _ _ _,
  { intros a ha b hb hab,
    obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := ⟨ha, hb⟩,
    exact not_frequently_of_upcrossing_lt_top hab (hf₂ a b (rat.cast_lt.1 hab)) },
  { sorry },
  { sorry }
end

lemma submartingale.upcrossing_ae_lt_top' (hf : submartingale f ℱ μ) (hab : a < b) :
  ∀ᵐ x ∂μ, upcrossing a b f x < ∞ :=
begin
  refine ae_lt_top (hf.adapted.measurable_upcrossing hab) _,
  sorry
end

lemma submartingale.upcrossing_ae_lt_top (hf : submartingale f ℱ μ) :
  ∀ᵐ x ∂μ, ∀ a b : ℚ, a < b → upcrossing a b f x < ∞ :=
begin
  suffices : ∀ a b : ℚ, a < b → ∀ᵐ x ∂μ, upcrossing a b f x < ∞,
  { simp_rw ae_iff at this ⊢,
    push_neg at this ⊢,
    rw set.set_of_exists,
    refine nonpos_iff_eq_zero.1 ((measure_Union_le _).trans
      (((tsum_eq_zero_iff ennreal.summable).2 (λ a, _)).le)),
    rw set.set_of_exists,
    refine nonpos_iff_eq_zero.1 ((measure_Union_le _).trans
      (((tsum_eq_zero_iff ennreal.summable).2 (λ b, _)).le)),
    rw set.set_of_and,
    by_cases hab : a < b,
    { simp only [hab, set.set_of_true, set.univ_inter, this a b] },
    { simp only [hab, set.set_of_false, set.empty_inter, measure_empty] } },
  rintro a b hab,
  exact hf.upcrossing_ae_lt_top' (rat.cast_lt.2 hab),
end

lemma liminf_at_top_ae_bdd_of_snorm_bdd (hbbd : ∃ R, ∀ n, snorm (f n) 1 μ ≤ R) :
  ∀ᵐ x ∂μ, ∃ R, at_top.liminf (λ n, |f n x|) < R :=
begin
  sorry
end

/-- An L¹-bounded submartingale converges almost everywhere. -/
lemma submartingale.exists_ae_tendsto_of_bdd
  (hf : submartingale f ℱ μ) (hbbd : ∃ R, ∀ n, snorm (f n) 1 μ ≤ R) :
  ∀ᵐ x ∂μ, ∃ c, tendsto (λ n, f n x) at_top (𝓝 c) :=
begin
  filter_upwards [hf.upcrossing_ae_lt_top, liminf_at_top_ae_bdd_of_snorm_bdd hbbd] with x h₁ h₂,
  exact tendsto_of_bdd_uncrossing h₂ h₁,
end

/-- **Almost everywhere martingale convergence theorem**: An L¹-bounded submartingale converges
almost everywhere to a L¹ random variable. -/
lemma submartingale.exists_mem_ℒ1_ae_tendsto_of_bdd
  (hf : submartingale f ℱ μ) (hbbd : ∃ R, ∀ n, snorm (f n) 1 μ ≤ R) :
  ∃ g : α → ℝ, mem_ℒp g 1 μ ∧
  ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 (g x)) :=
begin
  sorry
end

end measure_theory
