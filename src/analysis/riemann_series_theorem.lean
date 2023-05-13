import topology.algebra.ring.basic
import algebra.big_operators.basic
import order.filter.at_top_bot
import analysis.specific_limits.normed
import topology.metric_space.cau_seq_filter
import tactic

open_locale big_operators topology

universe u

noncomputable def rearrangement (a : ℕ → ℝ) (M : ℝ) : ℕ → ℕ
| 0 := 0
| (n+1) :=
  if ∑ (x : fin (n + 1)) in finset.univ, a (rearrangement ↑x) ≤ M then
    have h : ∃ k, k ∉ set.range (λ x : fin (n + 1), rearrangement ↑x) ∧ 0 ≤ a k := sorry,
    nat.find h
  else
    have h : ∃ k, k ∉ set.range (λ x : fin (n + 1), rearrangement ↑x) ∧ a k ≤ 0 := sorry,
    nat.find h
