/-
how does one use slim check to disprove a propostion

-/
import tactic.slim_check
import data.list.sort
import data.nat.parity
import .util
namespace tutorial

-- how does one use slim check to test a properties

/-
## Using `slim_check` to test a sorting programming

We can use `slim_check` to test a property on the fly with the `conjecture`
keyword:
-/

conjecture : ∀ x y z : ℕ, x + y ≤ z

/-
It will find assignments to variables `x`, `y`, `z` that contradicts the
proposition:

```
===================
Found problems!

x := 1
y := 0
z := 0
-------------------
```

`slim_check` can also be used as a proof tactic:
-/

example : ∀ x y : ℕ, x ≤ x + y :=
by slim_check

/-
When the statement is true, or when `slim_check` can't find counter-examples,
it will behave like `admit`: it doesn't print an error but nor is it a
valid proof.

We can use `slim_check` to write a sorting function. Let us start with a
bad first approximation:
-/

open list

def sort : list ℕ → list ℕ
| [] := []
| (x :: xs) := filter (< x) xs ++ x :: filter (≥ x) xs

/-
This version is similar to quicksort but it does not recurse on sublists
after partitioning. And sure enough, it does not guarantee the right ordering:
-/

example : ∀ xs : list ℕ, sorted (≤) (sort xs) :=
by slim_check

/-
`slim_check` finds the following counter-example:

```
===================
Found problems!

xs := [0, 1, 0]
-------------------
state:
⊢ ∀ (xs : list ℕ), sorted has_le.le (sort xs)
```

We may want to see why sorting fails on this example
-/

#eval sort [0,1,0]

/-
```
[0, 1, 0]
```

`sort` proceeds by considering `0 :: [1, 0]` and partitioning
`[1, 0]` into `[]` and `[1, 0]`. Let us be minimalistic and
recurse on the second partition. It will fix this particular
instance but the function will still be wrong.
-/

def sort₂ : list ℕ → list ℕ
| [] := []
| (x :: xs) :=
  have (filter (≥ x) xs).sizeof <  1 + (x + xs.sizeof),
    from sorry, -- let us omit the proof of termination
  filter (< x) xs ++ x :: sort₂ (filter (≥ x) xs)

example : ∀ xs : list ℕ, sorted (≤) (sort₂ xs) :=
by slim_check

/-
```
===================
Found problems!

xs := [3, 1, 0]
-------------------
state:
⊢ ∀ (xs : list ℕ), sorted has_le.le (sort₂ xs)
```

Again, we run the example:
-/

#eval sort₂ [3, 1, 0]

/-
```
[1, 0, 3]
```

`sort₂` considers the list as `3 :: [1, 0]`, partitions the tail into
`[1, 0]` and `[]`. Sorting `[]` yields `[]` and the final output is
`[1, 0, 3]`. We need to recurse on the first half too.

We fix this oversight and introduce a new mistake by changing `≥` to `>`.

-/
def sort₃ : list ℕ → list ℕ
| [] := []
| (x :: xs) :=
  have (filter (> x) xs).sizeof <  1 + (x + xs.sizeof), from sorry,
  have (filter (< x) xs).sizeof <  1 + (x + xs.sizeof), from sorry,
  sort₃ (filter (< x) xs) ++ x :: sort₃ (filter (> x) xs)

example : ∀ xs : list ℕ, sorted (≤) (sort₃ xs) :=
by slim_check

/-
`slim_check` can no longer find counter-examples but we should also ensure
that the result of sorting yields a permutation of the input.
-/

example : ∀ xs : list ℕ, perm xs (sort₃ xs) :=
by slim_check

/-
```
===================
Found problems!

xs := [0, 0]
-------------------
state:
⊢ ∀ (xs : list ℕ), xs ~ sort₃ xs
```
-/

#eval sort₃ [0, 0]

/-
```
[0]
```

The calls to `filter` retain `(> x)` and `(< x)` which meas that only one
`0` remains. We fix this issue by changing the `<` to `≤`.
-/

def sort₄ : list ℕ → list ℕ
| [] := []
| (x :: xs) :=
  have (filter (≤ x) xs).sizeof <  1 + (x + xs.sizeof), from sorry,
  have (filter (> x) xs).sizeof <  1 + (x + xs.sizeof), from sorry,
  sort₄ (filter (≤ x) xs) ++ x :: sort₄ (filter (> x) xs)

example : ∀ xs : list ℕ, sorted (≤) (sort₄ xs) :=
by slim_check

example : ∀ xs : list ℕ, perm xs (sort₄ xs) :=
by slim_check

/-
And now both tests succeed. We can also use `slim_check` to check termination:
-/

def sort₅ : list ℕ → list ℕ
| [] := []
| (x :: xs) :=
  have (filter (≤ x) xs).sizeof <  (x + xs.sizeof), by slim_check,
  have (filter (> x) xs).sizeof <  1 + (x + xs.sizeof), from sorry,
  sort₄ (filter (≤ x) xs) ++ sort₄ (filter (> x) xs)

/-
We introduced a bug in the termination condition and `slim_check`
found it:

```
===================
Found problems!

x := 0
xs := [0]
-------------------
state:
sort₅ : list ℕ → list ℕ,
x : ℕ,
xs : list ℕ
⊢ list.sizeof (filter (λ (_x : ℕ), _x ≤ x) xs) < x + list.sizeof xs
```
-/

open nat

/-
## `slim_check` and custom generators

Let's say that we want to test our understanding of prime numbers
and wonder if every prime number is even:
-/

example : ∀ n, prime n → even n :=
by slim_check

/-
Of course not, says `slim_check`:

```
===================
Found problems!

n := 5
-------------------
state:
⊢ ∀ (n : ℕ), prime n → even n
```

Could it be that all prime numbers are odd then?
-/

example : ∀ n, prime n → ¬ even n :=
by slim_check

/-
No!

```
===================
Found problems!

n := 2
-------------------
state:
⊢ ∀ (n : ℕ), prime n → ¬even n
```

What if we need `slim_check` to find a large prime number? Let's
consider the following property:
-/
example : ∀ n, prime n → n < 100000000 :=
by slim_check

/-
`slim_check` gives up. It uses a parameter, `max_size`, which defaults at `100`
to determine how big the last examples are. The first examples will be small and
increase in size until it reaches `max_size`. We can try larger examples by
providing a larger value of `max_size`.
-/

example : ∀ n, prime n → n < 100000000 :=
by slim_check { max_size := 1000 }

/-
Now `slim_check` finds an example:

```
===================
Found problems!

n := 125276477
-------------------
state:
⊢ ∀ (n : ℕ), prime n → n < 100000000
```

Let's try and look for larger examples:
-/

example : ∀ n, prime n → n < 10000000000000 :=
by slim_check { max_size := 100000 }



/-
Why? It finds prime numbers by generating
natural numbers randomly, testing if they are prime and discarding them
if they are not.
-/

def check_next_prime (n m : ℕ) : decidable (n ≤ n+m ∧ prime (n+m)) :=
@and.decidable _ _ (is_true $ le_add_right _ _) _

def next_prime (n : ℕ) : subtype prime :=
have ∃ p, n ≤ n+p ∧ prime (n+p),
     from exists_imp_exists' (λ p, p - n)
       (λ m (h : n ≤ m ∧ prime m),
         show n ≤ n + (m - n) ∧ prime (n + (m - n)),
         by simp [nat.add_sub_cancel' h.1,h])
       (exists_infinite_primes n),
let x := nat.find this in
⟨n+x,and.elim_right $ nat.find_spec this⟩

-- def next_prime (n : ℕ) : subtype prime :=
-- have ∃ p, n ≤ p ∧ prime p, from exists_infinite_primes _,
-- ⟨ nat.find this, and.elim_right $ nat.find_spec this ⟩

def prime.arbitrary : slim_check.arbitrary (subtype prime) :=
{ arby := do
       { n ← slim_check.arbitrary.arby ℕ,
         pure $ next_prime n},
  shrink := λ _, lazy_list.nil }

section
local attribute [instance] prime.arbitrary

example : ∀ n, prime n → ¬ even n :=
by slim_check

-- example : ∀ n, prime n → n < 1000000 :=
-- by slim_check { max_size := 100 }

-- example : ∀ n, prime n → n < 1000000000 :=
-- by slim_check { max_size := 1000 }

-- example : ∀ n, prime n → n < 1000000000000 :=
-- by slim_check { max_size := 10000 }

-- example : ∀ n, prime n → n < 1000000000000 :=
-- by slim_check { max_size := 50000 }

-- example : ∀ n, prime n → n < 1000000000000 :=
-- by slim_check { max_size := 100000 }
example : ∀ n, prime n → n < 10000000000000 :=
by slim_check { max_size := 100000 }


end

def mcheck_next_prime (n m : ℕ) : rand (decidable (n ≤ n+m ∧ prime (n+m))) :=
do h ← fermat_test (n+m),
   pure $ @and.decidable _ _ (is_true $ le_add_right _ _) h

def mnext_prime (n : ℕ) : rand (subtype prime) :=
have ∃ p, n ≤ n+p ∧ prime (n+p),
     from exists_imp_exists' (λ p, p - n)
       (λ m (h : n ≤ m ∧ prime m),
         show n ≤ n + (m - n) ∧ prime (n + (m - n)),
         by simp [nat.add_sub_cancel' h.1,h])
       (exists_infinite_primes n),
do ⟨x,h⟩ ← nat.mfind (mcheck_next_prime n) this,
   pure ⟨n+x,h.1.2⟩

section

def prime.arbitrary₂ : slim_check.arbitrary (subtype prime) :=
{ arby := do
       { n ← slim_check.arbitrary.arby ℕ,
         monad_lift $ mnext_prime n},
  shrink := λ _, lazy_list.nil }

local attribute [instance] prime.arbitrary₂

example : ∀ n, prime n → ¬ even n :=
by slim_check

-- example : ∀ n, prime n → n < 1000000000000 :=
-- by slim_check { max_size := 5000 }

-- example : ∀ n, prime n → n < 1000000000000 :=
-- by slim_check { max_size := 10000 }

example : ∀ n, prime n → n < 1000000000000 :=
by slim_check { max_size := 50000 }

sample subtype prime

end
-- numbers
-- prime numbers
-- smarter generators for prime numbers
-- future work: `arbitrary (sigma group)`


end tutorial
