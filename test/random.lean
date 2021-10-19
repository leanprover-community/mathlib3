import system.random.basic
import data.nat.prime
import data.zmod.basic

/-- fermat's primality test -/
def primality_test (p : ℕ) : rand bool :=
if h : 2 ≤ p-1 then do
  n ← rand.random_r 2 (p-1) h,
  -- we do arithmetic with `zmod n` so that modulo and multiplication are interleaved
  return $ (n : zmod p)^(p-1) = 1
else return (p = 2)

/-- `iterated_primality_test_aux p h n` generating `n` candidate witnesses that `p` is a
composite number and concludes that `p` is prime if none of them is a valid witness  -/
def iterated_primality_test_aux (p : ℕ) : ℕ → rand bool
| 0 := pure tt
| (n+1) := do
  b ← primality_test p,
  if b
    then iterated_primality_test_aux n
    else pure ff

def iterated_primality_test (p : ℕ) : rand bool :=
iterated_primality_test_aux p 10

/-- `find_prime_aux p h n` generates a candidate prime number, tests
it as well as the 19 odd numbers following it. If none of them is
(probably) prime, try again `n-1` times. -/
def find_prime_aux (p : ℕ) (h : 1 ≤ p / 2) : ℕ → rand (option ℕ)
| 0 := pure none
| (n+1) := do
  k ← rand.random_r 1 (p / 2) h,
  let xs := (list.range' k 20).map (λ i, 2*i+1),
  some r ← option_t.run $
    xs.mfirst (λ n, option_t.mk $ mcond (iterated_primality_test n) (pure (some n)) (pure none))
    | find_prime_aux n,
  pure r

def find_prime (p : ℕ) : rand (option ℕ) :=
if h : 1 ≤ p / 2 then
  find_prime_aux p h 20
else pure none

open tactic

/- `ps` should be `[97, 101, 103, 107, 109, 113]` but
it uses a pseudo primality test and some composite numbers
also sneak in -/
run_cmd do
  let xs := list.range' 90 30,
  ps ← tactic.run_rand (xs.mfilter iterated_primality_test),
  when (ps ≠ [97, 101, 103, 107, 109, 113])
    (trace!"The random primality test also included some composite numbers: {ps}")

/- `ps` should be `[97, 101, 103, 107, 109, 113]`. This
test is deterministic because we pick the random seed -/
run_cmd do
  let xs := list.range' 90 30,
  let ps : list ℕ := (xs.mfilter iterated_primality_test).eval ⟨ mk_std_gen 10 ⟩,
  guard (ps = [97, 101, 103, 107, 109, 113]) <|> fail "wrong list of prime numbers"

/- this finds a random probably-prime number -/
run_cmd do
  some p ← tactic.run_rand (find_prime 100000) | trace "no prime found, gave up",
  when (¬ nat.prime p) (trace!"The number {p} fooled Fermat's test")
