import topology.algebra.ring.basic
import algebra.big_operators.basic
import order.filter.at_top_bot
import analysis.specific_limits.normed
import topology.metric_space.cau_seq_filter
import tactic

open filter

open_locale big_operators topology

universe u
/--
`partial_sum f n` is the sum `f 0 + f 1 + f 2 + ... + f (n - 1)`. Note that this does not include
the term `f n`.
-/
def partial_sum {R : Type u} [add_comm_monoid R] (f : ℕ → R) (n : ℕ) :=
∑ i in finset.range n, f i

@[simp]
lemma partial_sum_zero {R : Type u} [add_comm_monoid R] (f : ℕ → R) : partial_sum f 0 = 0 :=
begin
  unfold partial_sum,
  simp,
end

lemma partial_sum_next {R : Type u} [add_comm_monoid R] (f : ℕ → R) (n : ℕ) :
  partial_sum f (n + 1) = f n + partial_sum f n :=
begin
  unfold partial_sum,
  rw finset.range_succ,
  apply finset.sum_insert,
  exact finset.not_mem_range_self
end

noncomputable def rearrangement (a : ℕ → ℝ) (M : ℝ) : ℕ → ℕ
| 0 := 0
| (n+1) :=
  if ∑ (x : fin (n + 1)) in finset.univ, a (rearrangement ↑x) ≤ M then
    have h : ∃ k, k ∉ set.range (λ x : fin (n + 1), rearrangement ↑x) ∧ 0 ≤ a k := sorry,
    nat.find h
  else
    have h : ∃ k, k ∉ set.range (λ x : fin (n + 1), rearrangement ↑x) ∧ a k ≤ 0 := sorry,
    nat.find h

theorem riemann_series_theorem {a : ℕ → ℝ} (h₁ : ∃ C : ℝ, tendsto (partial_sum a) at_top (nhds C))
  (h₂ : ¬∃ C : ℝ, tendsto (partial_sum (λ k, ‖a k‖)) at_top (nhds C)) (M : ℝ) : ∃ (p : equiv.perm ℕ),
    filter.tendsto (partial_sum (λ n, a (p n))) filter.at_top (𝓝 M) := sorry
