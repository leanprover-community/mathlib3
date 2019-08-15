import .setup

open nat

theorem infinitude_of_primes : ∀ N, ∃ p ≥ N, prime p :=
begin
  intro N,
  let M := fact N + 1,
  let p := min_fac M,

  have pp : prime p := min_fac_prime (ne_of_gt (succ_lt_succ (fact_pos N))),

  use p,
  split,
  { by_contradiction,
    simp at a,
    have h₁ : p ∣ M := min_fac_dvd M,
    have h₂ : p ∣ fact N := dvd_fact (prime.pos pp) (le_of_lt a),
    have h : p ∣ 1 := (nat.dvd_add_iff_right h₂).mpr h₁,
    exact prime.not_dvd_one pp h },
  { assumption }
end
