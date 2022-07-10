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

variables {α ι : Type*} {m0 : measurable_space α} {μ : measure α}
variables {a b : ℝ} {f : ℕ → α → ℝ} {N : ℕ} {n m : ℕ} {x : α}

/-! We will now begin to prove the martingale convergence theorem.

Firstly, we want to show a real sequence `x` converges if
(a) `limsup |x| < ∞`,
(b) For all `a < b : ℚ` we have `sup N, upcrossing a b x N < ∞`.

With this, for all `x` satisfying `limsup |λ n, f n x| < ∞` and
for all `a < b : ℚ`, `sup N, upcrossing a b f N x < ∞`, we have `λ n, f n x` converges.

Now, we want another lemma which states if `𝔼[|X|] < ∞` then `|X| < ∞ a.e.`.

With this lemma and assumping `f` is L¹-bounded, using Fatou's lemma,
we have `𝔼[limsup |f|] ≤ limsup 𝔼[|f|] < ∞` implying `limsup |f| < ∞ a.e`. Furthermore, by
the upcrossing lemma, `sup N, upcrossing a b f N < ∞ a.e.` implying `f` converges pointwise almost
everywhere.

-/

/-- If a realization of a stochastic process has bounded upcrossings from below `a` to above `b`,
then that realization does not frequently visit both below `a` and above `b`. -/
lemma of_bdd_upcrossing (hab : a < b) (hx : ∃ k, ∀ N, upcrossing a b f N x < k) :
  ¬((∃ᶠ n in at_top, f n x < a) ∧ (∃ᶠ n in at_top, b < f n x)) :=
begin
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
  (hf₁ : ∃ R, liminf at_top (λ n, f n x) < R)
  (hf₂ : ∀ a b : ℚ, ∃ K, ∀ N, upcrossing a b f N x < K) :
  ∃ c, tendsto (λ n, f n x) at_top (𝓝 c) :=
begin
  refine tendsto_of_no_upcrossings rat.dense_range_cast _ _ _,
  { intros a ha b hb hab,
    obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := ⟨ha, hb⟩,
    exact of_bdd_upcrossing hab (hf₂ a b) },
  { sorry },
  { sorry }
end


end measure_theory
