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

lemma diff_partial_sums_of_agrees' {a b : ℕ → ℝ} {k : ℕ} (h : ∀ n : ℕ, k ≤ n → a n = b n) (n : ℕ)
  : partial_sum a (n + k) - partial_sum b (n + k) = partial_sum a k - partial_sum b k :=
begin
  induction n with n hi,
  { simp },
  have : a (n + k) + partial_sum a (n + k) - (b (n + k) + partial_sum b (n + k)) =
    (a (n + k) - b (n + k)) + (partial_sum a (n + k) - partial_sum b (n + k)) := by ring,
  simp [this, (show n + 1 + k = n + k + 1, by ring), partial_sum_next, hi, h (n + k) (le_add_self)]
end

lemma diff_partial_sums_of_agrees {a b : ℕ → ℝ} {k : ℕ} (h : ∀ n : ℕ, k ≤ n → a n = b n) {n : ℕ}
  (hn : k ≤ n) : partial_sum a n - partial_sum b n = partial_sum a k - partial_sum b k :=
begin
  have := diff_partial_sums_of_agrees' h (n - k),
  rw nat.sub_add_cancel hn at this,
  exact this,
end

lemma converges_of_agrees_converges {a b : ℕ → ℝ} {k : ℕ} (h : ∀ n : ℕ, k ≤ n → a n = b n)
  (h₁ : ∃ C, tendsto (partial_sum a) at_top (𝓝 C)) : ∃ C, tendsto (partial_sum b) at_top (𝓝 C) :=
begin
  cases h₁ with C ha,
  let D := partial_sum b k - partial_sum a k,
  use C + D,
  rw tendsto_def,
  intros s hs,
  rw mem_at_top_sets,
  use k,
  intros n hn,
  rw set.mem_preimage,
  sorry
end

lemma agrees_converges {a b : ℕ → ℝ} {k : ℕ} (h : ∀ n : ℕ, k ≤ n → a n = b n) :
  (∃ C, tendsto (partial_sum a) at_top (𝓝 C)) ↔ (∃ C, tendsto (partial_sum b) at_top (𝓝 C)) :=
begin
  split; intro h₁,
  { exact converges_of_agrees_converges h h₁ },
  { exact converges_of_agrees_converges (λ n hn, (h n hn).symm) h₁ }
end

theorem riemann_series_theorem {a : ℕ → ℝ} (h₁ : ∃ C : ℝ, tendsto (partial_sum a) at_top (nhds C))
  (h₂ : ¬∃ C : ℝ, tendsto (partial_sum (λ k, ‖a k‖)) at_top (nhds C)) (M : ℝ) : ∃ (p : equiv.perm ℕ),
    filter.tendsto (partial_sum (λ n, a (p n))) filter.at_top (𝓝 M) := sorry
