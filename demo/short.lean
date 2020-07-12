import .setup

open nat

theorem infinitude_of_primes (N : ℕ) : ∃ p ≥ N, prime p :=
begin
  use min_fac (fact N + 1),
  split,
  { by_contradiction,
    back, },
  back
end
