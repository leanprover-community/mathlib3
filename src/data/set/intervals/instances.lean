import data.set.intervals.basic
import algebra.order.ring
import algebra.group_power.order

open set

def prob_pow_Icc {α : Type*} [ordered_semiring α] (p : Icc (0:α) 1) (n : ℕ) : (Icc (0:α) 1) :=
⟨p^n, ⟨pow_nonneg p.2.1 n, pow_le_one n p.2.1 p.2.2⟩⟩

instance {α : Type*} [ordered_semiring α] : has_pow (Icc (0:α) 1) ℕ := ⟨prob_pow_Icc⟩
