/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import analysis.specific_limits

/-!
# Hofer's lemma

This is an elementary lemma about complete metric spaces. It is motivated by an
application to the bubbling-off analysis for holomorphic curves in symplectic topology.
We are *very* far away from having these applications, but the proof here is a nice
example of a proof needing to construct a sequence by induction in the middle of the proof.

## References:

* H. Hofer and C. Viterbo, *The Weinstein conjecture in the presence of holomorphic spheres*
-/

open_locale classical topological_space big_operators
open filter finset

local notation `d` := dist

lemma hofer {X: Type*} [metric_space X] [complete_space X]
  (x : X) (ε : ℝ) (ε_pos : 0 < ε)
  {ϕ : X → ℝ} (cont : continuous ϕ) (nonneg : ∀ y, 0 ≤ ϕ y) :
  ∃ (ε' > 0) (x' : X), ε' ≤ ε ∧
                       d x' x ≤ 2*ε ∧
                       ε * ϕ(x) ≤ ε' * ϕ x' ∧
                       ∀ y, d x' y ≤ ε' → ϕ y ≤ 2*ϕ x' :=
begin
  by_contradiction H,
  have reformulation : ∀ x' (k : ℕ), ε * ϕ x ≤ ε / 2 ^ k * ϕ x' ↔ 2^k * ϕ x ≤ ϕ x',
  { intros x' k,
    rw [div_mul_eq_mul_div, le_div_iff, mul_assoc, mul_le_mul_left ε_pos, mul_comm],
    exact pow_pos (by norm_num) k, },
  -- Now let's specialize to `ε/2^k`
  replace H : ∀ k : ℕ, ∀ x', d x' x ≤ 2 * ε ∧ 2^k * ϕ x ≤ ϕ x' →
    ∃ y, d x' y ≤ ε/2^k ∧ 2 * ϕ x' < ϕ y,
  { intros k x',
    push_neg at H,
    simpa [reformulation] using
      H (ε/2^k) (by simp [ε_pos, zero_lt_two]) x' (by simp [ε_pos, zero_lt_two, one_le_two]) },
  clear reformulation,
  haveI : nonempty X := ⟨x⟩,
  choose! F hF using H,  -- Use the axiom of choice
  -- Now define u by induction starting at x, with u_{n+1} = F(n, u_n)
  let u : ℕ → X := λ n, nat.rec_on n x F,
  have hu0 : u 0 = x := rfl,
  -- The properties of F translate to properties of u
  have hu :
    ∀ n,
      d (u n) x ≤ 2 * ε ∧ 2^n * ϕ x ≤ ϕ (u n) →
      d (u n) (u $ n + 1) ≤ ε / 2 ^ n ∧ 2 * ϕ (u n) < ϕ (u $ n + 1),
  { intro n,
    exact hF n (u n) },
  clear hF,
  -- Key properties of u, to be proven by induction
  have key : ∀ n, d (u n) (u (n + 1)) ≤ ε / 2 ^ n ∧ 2 * ϕ (u n) < ϕ (u (n + 1)),
  { intro n,
    induction n using nat.case_strong_induction_on with n IH,
    { specialize hu 0,
      simpa [hu0, mul_nonneg_iff, zero_le_one, ε_pos.le, le_refl] using hu },
    have A : d (u (n+1)) x ≤ 2 * ε,
    { rw [dist_comm],
      let r := range (n+1), -- range (n+1) = {0, ..., n}
      calc
      d (u 0) (u (n + 1))
          ≤ ∑ i in r, d (u i) (u $ i+1) : dist_le_range_sum_dist u (n + 1)
      ... ≤ ∑ i in r, ε/2^i             : sum_le_sum (λ i i_in, (IH i $ nat.lt_succ_iff.mp $
                                                                  finset.mem_range.mp i_in).1)
      ... = ∑ i in r, (1/2)^i*ε         : by { congr' with i, field_simp }
      ... = (∑ i in r, (1/2)^i)*ε       : finset.sum_mul.symm
      ... ≤ 2*ε                         : mul_le_mul_of_nonneg_right (sum_geometric_two_le _)
                                            (le_of_lt ε_pos), },
    have B : 2^(n+1) * ϕ x ≤ ϕ (u (n + 1)),
    { refine @geom_le (ϕ ∘ u) _ zero_le_two (n + 1) (λ m hm, _),
      exact (IH _ $ nat.lt_add_one_iff.1 hm).2.le },
    exact hu (n+1) ⟨A, B⟩, },
  cases forall_and_distrib.mp key with key₁ key₂,
  clear hu key,
  -- Hence u is Cauchy
  have cauchy_u : cauchy_seq u,
  { refine cauchy_seq_of_le_geometric _ ε one_half_lt_one (λ n, _),
    simpa only [one_div, inv_pow₀] using key₁ n },
  -- So u converges to some y
  obtain ⟨y, limy⟩ : ∃ y, tendsto u at_top (𝓝 y),
    from complete_space.complete cauchy_u,
  -- And ϕ ∘ u goes to +∞
  have lim_top : tendsto (ϕ ∘ u) at_top at_top,
  { let v := λ n, (ϕ ∘ u) (n+1),
    suffices : tendsto v at_top at_top,
      by rwa tendsto_add_at_top_iff_nat at this,
    have hv₀ : 0 < v 0,
    { have : 0 ≤ ϕ (u 0) := nonneg x,
      calc 0 ≤ 2 * ϕ (u 0) : by linarith
      ... < ϕ (u (0 + 1)) : key₂ 0 },
    apply tendsto_at_top_of_geom_le hv₀ one_lt_two,
    exact λ n, (key₂ (n+1)).le },
  -- But ϕ ∘ u also needs to go to ϕ(y)
  have lim : tendsto (ϕ ∘ u) at_top (𝓝 (ϕ y)),
    from tendsto.comp cont.continuous_at limy,
  -- So we have our contradiction!
  exact not_tendsto_at_top_of_tendsto_nhds lim lim_top,
end
