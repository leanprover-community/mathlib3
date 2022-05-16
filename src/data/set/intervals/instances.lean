import data.set.intervals.basic
import algebra.order.ring
import algebra.group_power.order

open set

def prob_pow_Icc {α : Type*} [ordered_semiring α] (p : Icc (0:α) 1) (n : ℕ) : (Icc (0:α) 1) :=
⟨p^n, ⟨pow_nonneg p.2.1 n, pow_le_one n p.2.1 p.2.2⟩⟩

instance {α : Type*} [ordered_semiring α] : has_pow (Icc (0:α) 1) ℕ := ⟨prob_pow_Icc⟩



-- Yaël Dillies: What you really should do is provide `comm_monoid_with_zero (Icc 0 1)`. Then you'll get powers for free.  You can also do
-- `comm_semigroup_with_zero (Ico 0 1)`,
-- `comm_monoid (Ioc 0 1)`,
-- `comm_semigroup (Ioo 0 1)`,
-- `comm_monoid_with_zero (Icc (-1) 1)`,
-- `comm_monoid_with_zero (Ioc (-1) 1`,
-- `comm_semigroup_with_zero (Ioo (-1) 1)`,
-- and also provide `has_distrib_neg` instances where applicable.
