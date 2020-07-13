import data.nat.prime
import tactic.linarith

open nat

theorem infinitude_of_primes : ∀ N, ∃ p ≥ N, prime p :=
begin
  intro N,
  let M := fact N + 1,
  let p := min_fac M,

  have pp : prime p := begin show_term { /- suggest -/ refine min_fac_prime _, have : fact N > 0 := by library_search, linarith, }, end,

  use p,
  split,
  { by_contradiction,
    have h₂ : p ∣ fact N := begin /- suggest -/ refine pp.dvd_fact.mpr _, library_search, end,
    have h₁ : p ∣ M := by library_search,
    have h : p ∣ 1 := by library_search,
    by library_search, },
  { assumption, },
end
