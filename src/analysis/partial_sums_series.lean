import topology.algebra.ring.basic
import algebra.big_operators.basic
import order.filter.at_top_bot
import analysis.specific_limits.normed
import topology.metric_space.cau_seq_filter
import tactic

open_locale big_operators topology

universe u

/--
`partial_sum f n` is the sum `f 0 + f 1 + f 2 + ... + f (n - 1)`. Note that this does not include
the term `f n`.
-/
def partial_sum {R : Type u} [add_comm_monoid R] (f : ℕ → R) (n : ℕ) :=
∑ i in finset.range n, f i

lemma partial_sum_zero (R : Type u) [add_comm_monoid R] (n : ℕ) : partial_sum (λ _ : ℕ, 0) n = 0 :=
finset.sum_eq_zero (λ _ _, rfl)

lemma partial_sum_next {R : Type u} [add_comm_monoid R] {f : ℕ → R} (n : ℕ) :
  partial_sum f (n + 1) = f n + partial_sum f n :=
begin
  unfold partial_sum,
  rw finset.range_succ,
  apply finset.sum_insert,
  exact finset.not_mem_range_self
end

def series_sums_to {R : Type u} [add_comm_monoid R] [topological_space R] (f : ℕ → R) (a : R) :=
filter.tendsto (partial_sum f) filter.at_top (𝓝 a)

def series_converges {R : Type u} [add_comm_monoid R] [topological_space R] (f : ℕ → R) :=
∃ a : R, series_sums_to f a

def series_converges_absolutely {R : Type u} [add_comm_monoid R] [topological_space R] [has_abs R] (f : ℕ → R) :=
series_converges (λ x, |f x|)

lemma tail_limit {R : Type u} [topological_space R] (f : ℕ → R) (T : R) (h : filter.tendsto f filter.at_top (𝓝 T)) :
  filter.tendsto (λ k, f (k + 1)) filter.at_top (𝓝 T) :=
begin
  rw filter.tendsto_def at h ⊢,
  intros s hs,
  specialize h s hs,
  rw filter.mem_at_top_sets at h ⊢,
  cases h with a h,
  use a,
  intros b hb,
  exact h (b + 1) (nat.le_succ_of_le hb)
end

lemma seq_tendsto_zero (a : ℕ → ℝ) (h : series_converges a) : filter.tendsto a filter.at_top (𝓝 0) :=
begin
  cases h with x hx,
  unfold series_sums_to at hx,
  replace hx := filter.tendsto.cauchy_seq hx,
  have := cauchy_seq.is_cau_seq hx,
  rw filter.tendsto_def,
  intros s hs,
  rw filter.mem_at_top_sets,
  rw metric.mem_nhds_iff at hs,
  rcases hs with ⟨ε, H, hε⟩,
  replace this := is_cau_seq.cauchy₂ this H,
  cases this with i hi,
  use i + 1,
  intros b hb,
  rw set.mem_preimage,
  refine set.mem_of_mem_of_subset _ hε,
  rw metric.mem_ball,
  rw dist_eq_norm,
  rw sub_zero,
  specialize hi (b + 1) (by linarith) b (by linarith),
  rw partial_sum_next at hi,
  simpa using hi,
end

lemma partial_sums_le (a b : ℕ → ℝ) (h : ∀ n, a n ≤ b n) : ∀ n, partial_sum a n ≤ partial_sum b n :=
begin
  intro n,
  induction n with n hi,
  { unfold partial_sum,
    simp },
  calc partial_sum a (n + 1) = a n + partial_sum a n : partial_sum_next n
    ... ≤ b n + partial_sum b n : add_le_add (h n) (hi)
    ... = partial_sum b (n + 1) : (partial_sum_next n).symm
end

lemma cau_seq_of_le (a b : ℕ → ℝ) (h : ∀ n, 0 < a n ∧ a n < b n) (hb : series_converges b) : is_cau_seq abs a :=
begin
  cases hb with T hT,
  intros ε hε,
  sorry
end

theorem summable_of_series_absolute_convergence_real {f : ℕ → ℝ}
  (h : series_converges_absolutely f) : summable f :=
summable_of_absolute_convergence_real h
