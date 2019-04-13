import data.nat.prime
import tactic.back

open nat
open tactic

-- Check that `back` fails if there are no goals.
example : true :=
begin
  trivial,
  success_if_fail { back },
end

-- Check that `back` fails if it makes no progress.
example : true :=
begin
  success_if_fail { back },
  trivial
end

example {P : Prop} (h : P) : P :=
by back?

example {P Q : Prop} (h₁ : P) (h₂ : Q) : P :=
by back?

example {P Q : Prop} (h₁ : P) (h₂ : Q) : Q :=
by back?

example {P Q : Prop} (h₁ : P) (h₂ : P → Q) : Q :=
by back?

example {P Q R : Prop} (h₁ : P) (h₂ : P → Q) (h₃ : R → Q) : Q :=
by back?

example {P Q R : Prop} (h₁ : R) (h₂ : P → Q) (h₃ : R → Q) : Q :=
by back?

-- Verify that `back` uses `congr_arg`.
example (f : ℕ → ℕ) (x y : ℕ) (p : x = y) : f x = f y :=
begin
  success_if_fail { back [-congr_arg] },
  back?,
end

example : ℕ → ℕ := λ n, by success_if_fail { back }; back [*]

section primes

-- These are all lemmas which it is sufficiently safe to `apply`
-- that they can be automatically applied by backwards_reasoning.
attribute [back!] succ_lt_succ fact_pos min_fac_prime min_fac_dvd
attribute [back] dvd_fact

-- check that lemmas marked with ! are applied as many times as possible
example : 2 < 3 :=
begin
  back?,
  guard_target (0 < 1),
  exact zero_lt_one
end

theorem infinitude_of_primes (N : ℕ) : ∃ p ≥ N, prime p :=
begin
  let M := fact N + 1,
  let p := min_fac M,
  have pp : prime p, { back? [ne_of_gt], },
  -- Adding a `?`, i.e. as `back? [ne_of_gt]`, reports the expression back built:
  -- exact min_fac_prime (ne_of_gt (succ_lt_succ (fact_pos N)))
  use p,
  split,
  {
    by_contradiction,
    simp at a,
    -- We can restrict the search depth:
    have h₁ : p ∣ M, { back 2 },
    have h₂ : p ∣ fact N, { back? [le_of_lt, prime.pos], },
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
  have pp : prime p, { back?, },
  use p,
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

set_option profiler true

theorem infinitude_of_primes'' (N : ℕ) : ∃ p ≥ N, prime p :=
begin
  let p := min_fac (fact N + 1),
  have pp : prime p, back?,
  use p,
  -- Goal is `∃ (H : p ≥ N), prime pp`
  split; try { assumption },
  -- Goal is `p ≥ N`.
  by_contradiction h, simp at h,
  back?,
end

theorem infinitude_of_primes''' (N : ℕ) : ∃ p ≥ N, prime p :=
begin
  use min_fac (fact N + 1),
  split,
  { by_contradiction h, simp at h,
    back?, },
  back
end

end primes

section mono

example {a b c d e : nat} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ e) :
a + c * e + a + c + 0 ≤ b + d * e + b + d + e :=
add_le_add (add_le_add (add_le_add (add_le_add h1 (mul_le_mul_of_nonneg_right h2 h3)) h1 ) h2) h3

example {a b c d e : nat} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ e) :
a + c * e + a + c + 0 ≤ b + d * e + b + d + e :=
by back? [add_le_add, mul_le_mul_of_nonneg_right]
-- says `exact add_le_add (add_le_add (add_le_add (add_le_add h1 (mul_le_mul_of_nonneg_right h2 h3)) h1) h2) h3`

@[user_attribute]
meta def mono_rules : user_attribute :=
{ name := `mono_rules,
  descr := "lemmas usable to prove monotonicity" }
attribute [mono_rules] add_le_add mul_le_mul_of_nonneg_right

example {a b c d e : nat} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ e) :
a + c * e + a + c + 0 ≤ b + d * e + b + d + e :=
by back? with !mono_rules

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
  nat.dvd_iff_mod_eq_zero nat.dvd_of_mod_eq_zero

example {a b c : ℕ} (h₁ : a ∣ c) (h₂ : a ∣ b + c) : a ∣ b :=
begin
  back? [nat.dvd_add_iff_left],
end

example {a b c : ℕ} (h₁ : a ∣ c) (h₂ : a ∣ b + c) : a ∣ b :=
begin
  back? with dvd,
end

example {a b c : ℕ} (h₁ : a ∣ c) (h₂ : a ∣ b + c) : a ∣ b :=
begin
  library_search, -- says `exact (nat.dvd_add_iff_left h₁).mpr h₂`
end

end dvd

section infinitude_of_prime_by_library_search

-- set_option trace.back true

example (N : ℕ) : (∃ p ≥ N, prime p) ∨ true :=
begin
  let M := fact N + 1,
  let p := min_fac M,
  have pp : prime p, { apply min_fac_prime, apply ne_of_gt, library_search, },
  right, trivial
end

-- works with timeLimit = 1,000,000
-- example (N : ℕ) : (∃ p ≥ N, prime p) ∨ true :=
-- begin
--   let M := fact N + 1,
--   let p := min_fac M,
--   have pp : prime p, { apply min_fac_prime, library_search, },
--   right, trivial
-- end

end infinitude_of_prime_by_library_search

section nat

example {a b : ℕ} : a ≤ a + b :=
by library_search -- exact le_add_right a b

example (n m k : ℕ) : n * (m - k) = n * m - n * k :=
by library_search -- exact nat.mul_sub_left_distrib n m k

-- set_option trace.back true

lemma div_dvd_of_dvd {a b : ℕ} (h : b ∣ a) : (a / b) ∣ a :=
-- The mathlib proof is: `⟨b, (nat.div_mul_cancel h).symm⟩`
by library_search [-div_dvd_of_dvd]
-- We get: `dvd.intro b (nat.div_mul_cancel h)`

lemma div_pos {a b : ℕ} (hba : b ≤ a) (hb : 0 < b) : 0 < a / b :=
by library_search

example {a b : ℕ} (hba : b ≤ a) (hb : b ≠ 0) : 0 < a / b :=
by library_search

-- set_option trace.back_lemmas true
lemma one_le_of_lt {n m : ℕ} (h : n < m) : 1 ≤ m :=
by library_search [-one_le_of_lt]
-- a human proof:
-- lt_of_le_of_lt (nat.zero_le _) h

-- 2nd library_search result:
-- lattice.distrib_lattice.le_trans 1 (succ n) m (succ_pos n) h
-- 1st library_search result:
-- lattice.distrib_lattice.le_trans 1 (succ n) m (lattice.le_of_inf_eq min_fac_one) h

-- It would be nice to just use `nat.le_trans` here!

lemma le_pred_of_lt {n m : ℕ} (h : m < n) : m ≤ n - 1 :=
by library_search [-le_pred_of_lt] -- says: `exact nat.le_sub_right_of_add_le h`

example {α : Type} (x y : α) : x = y ↔ y = x :=
by library_search -- says: `exact eq_comm`

example (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
by library_search -- says: `exact add_pos_left ha b`

example (a b : ℕ) : 0 < a → 0 < b → 0 < a + b :=
by library_search -- says: `exact add_pos`

example : ∀ P : Prop, ¬(P ↔ ¬P) :=
by library_search -- says: `λ (a : Prop), (iff_not_self a).mp`

-- set_option trace.back_lemmas true
-- set_option trace.back false

example (a b : ℕ) (h : a ∣ b) (w : b > 0) : a ≤ b :=
by library_search

example (a b : ℕ) (h : a ∣ b) (w : b ≥ 1) : a ≤ b :=
by library_search

example (a b : ℕ) (h : a ∣ b) (w : b ≠ 0) : a ≤ b :=
by library_search

example {a b : ℕ} (w : b ≥ 1) : a ≤ a * b :=
by library_search

example {b : ℕ} (w : b > 0) : b ≥ 1 :=
by library_search

example {b : ℕ} (w : b ≠ 0) : b ≥ 1 :=
by library_search

-- Nope:
-- example (a b c : ℕ) (h : b ≤ c) (w : b ≥ 1) : a / c ≤ a / b :=
-- by library_search

-- example (a b c : ℕ) (h : b ≤ c) (w : b ≠ 0) : a / c ≤ a / b :=
-- by library_search

-- example {E : Type} (e : equiv E E) : function.surjective e :=
-- by library_search


-- FIXME why are these failing?
-- -- Works with timeLimit = 1,000,000
-- example {a b : ℕ} (w : b > 0) : a ≤ a * b :=
-- by library_search

-- -- Doesn't work:
-- example {a b : ℕ} (w : b ≠ 0) : a ≤ a * b :=
-- by library_search


-- An example to try, from James:
-- c : ℕ,
-- lH : c > succ n,
-- snec : succ n ≠ c,
-- onec : 1 ≠ c
-- ⊢ c ∣ succ n ↔ c = 1 ∨ c = succ n

-- Doesn't work
-- example (m n : ℕ) (h : 2*m ≤ n) : m ≤ n/2 := by library_search

end nat
