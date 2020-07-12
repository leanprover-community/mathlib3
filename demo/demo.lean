import .setup

open nat

theorem infinitude_of_primes : ∀ N, ∃ p ≥ N, prime p :=
begin
  intro N,
  let M := fact N + 1,
  let p := min_fac M,

  have pp : prime p := by,

  use p,
  split,
  { by_contradiction,
    have h₁ : p ∣ M := sorry,
    have h₂ : p ∣ fact N := sorry,
    have h : p ∣ 1 := sorry,
    sorry, },
  { assumption, },
end
