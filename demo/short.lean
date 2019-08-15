import .setup

open nat

theorem infinitude_of_primes (N : ℕ) : ∃ p ≥ N, prime p :=
begin
  use min_fac (fact N + 1),
  split,
  { by_contradiction h, simp at h,
    back, },
  back
end
