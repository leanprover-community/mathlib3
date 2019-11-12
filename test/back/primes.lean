import tactic.back
import data.nat.prime

open nat

attribute [back] ne_of_gt le_of_lt nat.dvd_add_iff_right prime.pos prime.not_dvd_one
-- attribute [back!] succ_lt_succ fact_pos min_fac_prime min_fac_dvd
attribute [back] succ_lt_succ fact_pos min_fac_prime min_fac_dvd
attribute [back] dvd_fact

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
    exact prime.not_dvd_one pp h, },
  { assumption }
end

example : ∀ N, ∃ p ≥ N, prime p :=
begin
  intro N,
  let M := fact N + 1,
  let p := min_fac M,

  have pp : prime p := by back,

  use p,
  split,
  { by_contradiction,
    simp at a,
    have h₁ : p ∣ M, by back,
    have h₂ : p ∣ fact N, by back,
    -- have h : p ∣ 1 := (nat.dvd_add_iff_right h₂).mpr h₁,
    have h : p ∣ 1, by back, -- This one makes us take a trip to struggletown
    back },
  { assumption }
end

example (N : ℕ) : ∃ p ≥ N, prime p :=
begin
  use min_fac (fact N + 1),
  split,
  { by_contradiction h, simp at h,
    -- apply prime.not_dvd_one,
    -- back
  },
  back
end
