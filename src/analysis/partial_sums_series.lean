import topology.algebra.ring.basic
import algebra.big_operators.basic
import order.filter.at_top_bot
import analysis.specific_limits.normed
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
  have : finset.range (n + 1) = insert n (finset.range n),
  { ext a,
    rw finset.mem_insert,
    rw finset.mem_range,
    rw finset.mem_range,
    rw ←le_iff_eq_or_lt,
    exact nat.lt_succ_iff },
  rw this,
  apply finset.sum_insert,
  exact finset.not_mem_range_self
end

def series_sums_to {R : Type u} [add_comm_monoid R] [topological_space R] (f : ℕ → R) (a : R) :=
filter.tendsto (partial_sum f) filter.at_top (𝓝 a)

def series_converges {R : Type u} [add_comm_monoid R] [topological_space R] (f : ℕ → R) :=
∃ a : R, series_sums_to f a

def series_converges_absolutely {R : Type u} [add_comm_monoid R] [topological_space R] [has_abs R] (f : ℕ → R) :=
series_converges (λ x, |f x|)


section

variables {R : Type u} [ring R] [topological_space R] [topological_ring R]
lemma zeros_sum_to_zero : series_sums_to (λ _ : ℕ, 0) 0 :=
begin
  unfold series_sums_to,
  sorry
end

end

theorem summable_of_series_absolute_convergence_real {f : ℕ → ℝ}
  (h : series_converges_absolutely f) : summable f :=
summable_of_absolute_convergence_real h
