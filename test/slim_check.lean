
import system.random.basic data.nat.prime

instance fin.has_one' {n} [fact (0 < n)] : has_one (fin n) :=
⟨ fin.of_nat' 1 ⟩

instance fin.has_pow' {n} [fact (0 < n)] : has_pow (fin n) ℕ :=
⟨ monoid.pow ⟩

/-- fermat's primality test -/
def primality_test (p : ℕ) (h : fact (0 < p)) : rand bool :=
if h : 2 ≤ p-1 then do
  n ← rand.random_r 2 (p-1), -- `random_r` requires a proof of `2 ≤ p-1` but it is dischared using `assumption`
  return $ (fin.of_nat' n : fin p)^(p-1) = 1 -- we do arithmetic with `fin n` so that modulo and multiplication are interleaved
else return (p = 2)

/-- `iterated_primality_test_aux p h n` generating `n` candidate witnesses that `p` is a
composite number and concludes that `p` is prime if none of them is a valid witness  -/
def iterated_primality_test_aux (p : ℕ) (h : fact (0 < p)) : ℕ → rand bool
| 0 := pure tt
| (n+1) := do
  b ← primality_test p h,
  if b
    then iterated_primality_test_aux n
    else pure ff

def iterated_primality_test (p : ℕ) : rand bool :=
if h : 0 < p
  then iterated_primality_test_aux p h 10
  else pure ff

/-- `find_prime_aux p h n` generates `n` candidate prime numbers,
tests each and 20 of their successors with `iterated_primality_test`
and return the first one that can pass the primality test. -/
def find_prime_aux (p : ℕ) (h : 1 ≤ p / 2) : ℕ → rand (option ℕ)
| 0 := pure none
| (n+1) := do
  k ← rand.random_r 1 (p / 2),
  let xs := (list.range' k 20).map (λ i, 2*i+1),
  some r ← option_t.run $ xs.mfirst (λ n, option_t.mk $ mcond (iterated_primality_test n) (pure (some n)) (pure none))
    | find_prime_aux n,
  pure r

def find_prime (p : ℕ) : rand (option ℕ) :=
if h : 1 ≤ p / 2 then
  find_prime_aux p h 20
else pure none

open tactic

/- this should print `[97, 101, 103, 107, 109, 113]` but
it uses a pseudo primality test and some composite numbers
also sneak in -/
run_cmd do
  let xs := list.range' 90 30,
  ps ← tactic.run_rand (xs.mfilter iterated_primality_test),
  trace ps

/- this should print `[97, 101, 103, 107, 109, 113]`. This
test is deterministic because we pick the random seed -/
run_cmd do
  let xs := list.range' 90 30,
  let ps : list ℕ := (xs.mfilter iterated_primality_test).eval ⟨ mk_std_gen 10 ⟩,
  guard (ps = [97, 101, 103, 107, 109, 113]) <|> fail "wrong list of prime numbers",
  trace ps

/- this finds a random probably-prime number -/
run_cmd do
  some p ← tactic.run_rand (find_prime 1000000) | trace "no prime found, gave up",
  trace p,
  if nat.prime p
    then trace "true prime"
    else trace "this number fooled Fermat's test"
