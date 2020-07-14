import data.nat.prime
import tactic.linarith

open nat

theorem infinitude_of_primes : ∀ N, ∃ p ≥ N, prime p :=
begin
  intro N,

  let M := fact N + 1,
  let p := min_fac M,

  have pp : prime p :=
  begin
    refine min_fac_prime _,
    have : fact N > 0 := fact_pos N,
    linarith,
  end,

  use p,
  split,
  { by_contradiction,
    have h₁ : p ∣ fact N + 1 := min_fac_dvd M,
    have h₂ : p ∣ fact N := (prime.dvd_fact pp).mpr (le_of_not_ge a),
    have h : p ∣ 1 := (nat.dvd_add_right h₂).mp h₁,
    exact prime.not_dvd_one pp h, },
  { exact pp, },
end
