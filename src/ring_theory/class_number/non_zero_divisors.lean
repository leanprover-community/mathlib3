import ring_theory.non_zero_divisors

section ne_zero

variables {R : Type*} [monoid_with_zero R] [nontrivial R]

lemma non_zero_divisors.ne_zero_of_mem
  {y : R} (hy : y ∈ non_zero_divisors R) : y ≠ 0 :=
λ h, one_ne_zero (show (1 : R) = 0, from hy _ (by rw [h, one_mul]))

lemma non_zero_divisors.ne_zero
  (y : non_zero_divisors R) : (y : R) ≠ 0 :=
non_zero_divisors.ne_zero_of_mem y.2

end ne_zero
