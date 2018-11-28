import data.nat.prime
import tactic.back

open nat

-- We check that `back` fails if it makes no progress.
example : true :=
begin
  success_if_fail { back },
  trivial
end

-- Verify that `back` uses `congr_arg`.
example (f : ℕ → ℕ) (x y : ℕ) (p : x = y) : f x = f y :=
begin
  success_if_fail { back [-congr_arg] },
  back
end

section primes

-- These are all lemmas which it is sufficiently safe to `apply`
-- that they can be automatically applied by backwards_reasoning.
attribute [back!] succ_lt_succ fact_pos min_fac_prime min_fac_dvd
attribute [back] dvd_fact

theorem infinitude_of_primes (N : ℕ) : ∃ p ≥ N, prime p :=
begin
  let M := fact N + 1,
  let p := min_fac M,
  have pp : prime p, { back [ne_of_gt] },
  -- Adding a `?`, i.e. as `back? [ne_of_gt]`, reports the expression back built:
  -- exact min_fac_prime (ne_of_gt (succ_lt_succ (fact_pos N)))
  existsi p,
  split,
  {
    by_contradiction,
    simp at a,
    -- We can restrict the search depth:
    have h₁ : p ∣ M, { back 2 },
    have h₂ : p ∣ fact N, { back [le_of_lt, prime.pos], },
    have h : p ∣ 1, { back [nat.dvd_add_iff_right] },
    back [prime.not_dvd_one],
  },
  assumption,
end

-- Now try tagging lots of relevant lemmas with `back` (i.e. as "finishing" lemmas),
-- and let `back` work autonomously.
local attribute [back] ne_of_gt le_of_lt nat.dvd_add_iff_right prime.pos prime.not_dvd_one

theorem infinitude_of_primes' (N : ℕ) : ∃ p ≥ N, prime p :=
begin
  let M := fact N + 1,
  let p := min_fac M,
  have pp : prime p, { back },
  existsi p,
  split,
  {
    by_contradiction,
    simp at a,
    have h₁ : p ∣ M, { back },
    have h₂ : p ∣ fact N, { back },
    have h : p ∣ 1, { back },
    back,
  },
  back,
end

end primes

section mono

example {a b c d e : nat} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ e) :
a + c * e + a + c + 0 ≤ b + d * e + b + d + e :=
add_le_add (add_le_add (add_le_add (add_le_add h1 (mul_le_mul_of_nonneg_right h2 h3)) h1 ) h2) h3

example {a b c d e : nat} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ e) :
a + c * e + a + c + 0 ≤ b + d * e + b + d + e :=
by back [add_le_add, mul_le_mul_of_nonneg_right]

@[user_attribute]
meta def mono_rules : user_attribute :=
{ name := `mono_rules,
  descr := "lemmas usable to prove monotonicity" }
attribute [mono_rules] add_le_add mul_le_mul_of_nonneg_right

example {a b c d e : nat} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ e) :
a + c * e + a + c + 0 ≤ b + d * e + b + d + e :=
by back with !mono_rules

end mono

section dvd

meta def dvd : user_attribute := {
  name := `dvd,
  descr := "A lemma that concludes a ∣ b."
}

run_cmd attribute.register ``dvd

-- Every lemma imported so far that concludes `a ∣ b`.
local attribute [dvd]
  dvd.intro dvd.intro_left dvd_add dvd_add_iff_left dvd_add_iff_right dvd_mul_left
  dvd_mul_of_dvd_left dvd_mul_of_dvd_right dvd_mul_right dvd_neg_iff_dvd dvd_neg_of_dvd dvd_of_dvd_neg
  dvd_of_mul_left_dvd dvd_of_mul_right_dvd dvd_of_neg_dvd dvd_refl dvd_sub dvd_trans dvd_zero list.dvd_prod
  mul_dvd_mul mul_dvd_mul_left mul_dvd_mul_right nat.div_dvd_of_dvd nat.dvd_add_iff_left
  nat.dvd_add_iff_right nat.dvd_div_of_mul_dvd nat.dvd_fact nat.dvd_mod_iff
  nat.dvd_of_mul_dvd_mul_left nat.dvd_of_mul_dvd_mul_right nat.dvd_of_pow_dvd nat.dvd_one
  nat.dvd_sub nat.fact_dvd_fact nat.mul_dvd_mul_iff_left nat.mul_dvd_mul_iff_right nat.mul_dvd_of_dvd_div
  nat.pow_dvd_of_le_of_pow_dvd nat.pow_dvd_pow nat.pow_dvd_pow_of_dvd neg_dvd_iff_dvd neg_dvd_of_dvd one_dvd
-- These two cause trouble, however:
--  nat.dvd_iff_mod_eq_zero nat.dvd_of_mod_eq_zero

example {a b c : ℕ} (h₁ : a ∣ c) (h₂ : a ∣ b + c) : a ∣ b :=
begin
  back [nat.dvd_add_iff_left],
end

example {a b c : ℕ} (h₁ : a ∣ c) (h₂ : a ∣ b + c) : a ∣ b :=
begin
  back with dvd,
end

end dvd
