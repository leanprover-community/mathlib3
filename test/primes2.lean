import data.nat.prime
import tactic.auto

open nat

theorem infinitude_of_primes : ∀ N, ∃ p ≥ N, prime p :=
begin
  intro N,
  let M := fact N + 1,
  let p := min_fac M,
  have pp : prime p, auto,
  refine ⟨ p, _, pp ⟩,
  by_contradiction,
  simp at a,
  have h₁ : p ∣ M, auto,
  have h₂ : p ∣ fact N, auto,
  have h : p ∣ 1, auto,
  auto,
end
