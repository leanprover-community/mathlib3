/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.nat.basic
import tactic

/-!
# Strong recursion

A strong recursion principle based on `fin`.
The benefit of `(Π (m:fin n), X m)` over `Π (m:ℕ) (h:m < n), X m`
is that with `fin` the bound on `m` is bundled,
and this can be used in later proofs and constructions.

## Example

For example, one can use this to give a definition of the Bernoulli numbers
that closely follows the recursive definition found at
https://en.wikipedia.org/wiki/Bernoulli_number#Recursive_definition
It is:
$$ B_n = 1 - \sum_{k < n} \binom{n}{k} \frac{B_k}{n - k + 1} $$

```lean
example : ℕ → ℚ :=
strong_recursion $ λ n bernoulli,
1 - finset.univ.sum (λ k : fin n, (n.choose k) * bernoulli k / (n - k + 1))
```

This example shows the benefit of using `fin n` in the implementation,
because it allows us to use `finset.univ.sum` which enables the recursive call `bernoulli k`.
If, on the other hand, we had used `Π (m:ℕ) (h:m < n), X m` and `(finset.range n).sum`,
then the recursive call to `bernoulli k` would get stuck,
because it would come with a proof obligation `k < n`
which isn't provided by `(finset.range n).sum`.

-/

namespace nat
universe variable u
variables {X : ℕ → Sort u} (f : Π n, (Π (m:fin n), X m) → X n)

/-- An auxilliary definition for `nat.strong_recursion`.
This is a dependent type version of the following algorithm:
Given a recipe to turn function `fin n → X` into terms of type `X`,
return a function that takes bounded natural numbers to terms of type `X`. -/
protected def strong_recursion_aux :
  Π n m, m < n → X m
| 0     := λ _ h, absurd h (not_lt_zero _)
| (n+1) := λ m h,
(lt_or_eq_of_le (le_of_lt_succ h)).by_cases
  (strong_recursion_aux n m)
  (λ e, f _ (λ k, strong_recursion_aux n _ $ lt_of_lt_of_le k.2 $ le_of_eq e))

#check nat.strong_recursion_aux

/-- A strong recursion principle for the natural numbers.
It allows one to recursively define a function on ℕ
by showing how to extend a function on `fin n := {k // k < n}` to `n`. -/
def strong_recursion (n : ℕ) : X n :=
nat.strong_recursion_aux f (n+1) n $ n.lt_succ_self

@[simp] lemma strong_recursion_aux_lt (m n : ℕ) (h : m < n) :
  nat.strong_recursion_aux f n m h = strong_recursion f m :=
begin
  obtain ⟨k, rfl⟩ : ∃ k, n = m + 1 + k :=
  by simpa [add_right_comm] using nat.exists_eq_add_of_lt h,
  induction k with k ih, { refl },
  have hm : m < m + 1 + k, by linarith,
  rw ← ih hm,
  exact dif_pos hm,
end

lemma strong_recursion_apply (n : ℕ) :
  strong_recursion f n = f n (λ i, strong_recursion f i) :=
begin
  show dite (n < n) _ _ = _,
  rw [dif_neg (lt_irrefl n)],
  show dite (n = n) _ _ = _,
  rw [dif_pos rfl],
  refine congr_arg (f n) _,
  funext k,
  apply strong_recursion_aux_lt,
end

-- Example: Fibonacci
example : ℕ → ℚ :=
strong_recursion $ λ n fib,
match n, fib with
| 0 := λ _, 0
| 1 := λ _, 1
| (k+2) := λ fib, fib k + fib (k+1)
end

/-
requires `import data.fintype`

-- Example: Bernoulli
example : ℕ → ℚ :=
strong_recursion $ λ n bernoulli,
1 - finset.univ.sum (λ k : fin n, (n.choose k) * bernoulli k / (n - k + 1))
-/

end nat
