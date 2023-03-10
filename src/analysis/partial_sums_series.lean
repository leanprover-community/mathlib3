import topology.algebra.ring.basic
import algebra.big_operators.basic
import order.filter.at_top_bot
import tactic

open_locale big_operators topology

universe u

/--
`partial_sum f n` is the sum `f 0 + f 1 + f 2 + ... + f (n - 1)`. Note that this does not include
the term `f n`.
-/
def partial_sum {R : Type u} [add_comm_monoid R] (f : ℕ → R) (n : ℕ) :=
∑ i in finset.range n, f i

def series_sums_to {R : Type u} [add_comm_monoid R] [topological_space R] (f : ℕ → R) (a : R) :=
filter.tendsto (partial_sum f) filter.at_top (𝓝 a)

def series_converges {R : Type u} [add_comm_monoid R] [topological_space R] (f : ℕ → R) :=
∃ a : R, series_sums_to f a

def series_converges_absolutely {R : Type u} [add_comm_monoid R] [topological_space R] [has_abs R] (f : ℕ → R) :=
series_converges (λ x, |f x|)

variables {R : Type u} [ring R] [topological_space R] [topological_ring R]
