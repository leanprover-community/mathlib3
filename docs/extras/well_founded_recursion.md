# The equation compiler and using_well_founded #

To define functions and proofs recursively you can use the equation compiler, if you have a well founded relation on that type

For example the definition of gcd on naturals uses well founded recursion

```lean
def gcd : nat → nat → nat
| 0        y := y
| (succ x) y := have y % succ x < succ x, from mod_lt _ $ succ_pos _,
                gcd (y % succ x) (succ x)
```

Because < is a well founded relation on naturals, and because `y % succ x < succ x` this recursive function is well_founded.

Whenever you use the equation compiler there will be a default well founded relation on the type being recursed on and the equation compiler will automatically attempt to prove the function is well founded.

If the equation compiler fails, there are two main reasons for this. The first is that it has failed to prove the required inequality. The second is that it is not using the correct well founded relation.

### Proving required inequality ###

If we modify the gcd example above, by removing the `have`, we get an error.

```lean
def gcd : nat → nat → nat
| 0        y := y
| (succ x) y := gcd (y % succ x) (succ x)
```
```
failed to prove recursive application is decreasing, well founded relation
  @has_well_founded.r (Σ' (a : ℕ), ℕ)
    (@psigma.has_well_founded ℕ (λ (a : ℕ), ℕ) (@has_well_founded_of_has_sizeof ℕ nat.has_sizeof)
       (λ (a : ℕ), @has_well_founded_of_has_sizeof ℕ nat.has_sizeof))
Possible solutions:
  - Use 'using_well_founded' keyword in the end of your definition to specify tactics for synthesizing well founded relations and decreasing proofs.
  - The default decreasing tactic uses the 'assumption' tactic, thus hints (aka local proofs) can be provided using 'have'-expressions.
The nested exception contains the failure state for the decreasing tactic.
nested exception message:
failed
state:
gcd : (Σ' (a : ℕ), ℕ) → ℕ,
x y : ℕ
⊢ y % succ x < succ x
```

The error message has given us a goal, `y % succ x < succ x`. Including a proof of this goal as part of our definition using `have` removes the error.

```lean
def gcd : nat → nat → nat
| 0        y := y
| (succ x) y := have y % succ x < succ x, from mod_lt _ $ succ_pos _,
                gcd (y % succ x) (succ x)
```

Note that the `have` must not be in tactics mode, i.e. inside any `begin` `end`. If you are in tactics mode, there is the option of putting the `have` statement inside the exact statement, as in the following example.

```lean
def gcd : nat → nat → nat
| 0        y := y
| (succ x) y :=
begin
  exact have y % succ x < succ x := mod_lt _ (succ_pos _),
  gcd (y % succ x) (succ x)
end
```

### order of arguments ###

Sometimes the default relation the equation compiler uses is not the correct one. For example swapping the order of x and y in the above example causes a failure

```lean
def gcd : nat → nat → nat
| y 0        := y
| y (succ x) := have y % succ x < succ x, from mod_lt _ $ succ_pos _,
                gcd (succ x) (y % succ x)
```

Now the error message is asking us to prove `succ x < y`. This is because by default the equation compiler tries to recurse on the first argument. More precisely, the relation that the equation compiler tries to use in this example is on the type of pairs of natural numbers `Σ' (a : ℕ), ℕ`, and it uses a lexicographical relation where the pair `⟨a, b⟩ ≺ ⟨c, d⟩` iff `a < c ∨ (a = c ∧ b < d)` This situation can be resolved, either by changing the order of the arguments or by specifying a `rel_tac` as decribed later in this doc.

Sometimes moving an argument outside of the equation compiler, can help the equation compiler prove a recursion is well_founded. For example the following proof from `data.nat.prime` fails.

```lean
lemma prod_factors : ∀ (n), 0 < n → list.prod (factors n) = n
| 0       h := (lt_irrefl _).elim h
| 1       h := rfl
| n@(k+2) h :=
  let m := min_fac n in have n / m < n := factors_lemma,
  show list.prod (m :: factors (n / m)) = n, from
  have h₁ : 0 < n / m :=
    nat.pos_of_ne_zero $ λ h,
    have n = 0 * m := (nat.div_eq_iff_eq_mul_left (min_fac_pos _) (min_fac_dvd _)).1 h,
    by rw zero_mul at this; exact (show k + 2 ≠ 0, from dec_trivial) this,
  by rw [list.prod_cons, prod_factors _ h₁, nat.mul_div_cancel' (min_fac_dvd _)]
```

But moving the `h` into a lambda after the `:=` makes it work

```lean
lemma prod_factors : ∀ (n), 0 < n → list.prod (factors n) = n
| 0       := λ h, (lt_irrefl _).elim h
| 1       := λ h, rfl
| n@(k+2) := λ h,
  let m := min_fac n in have n / m < n := factors_lemma,
  show list.prod (m :: factors (n / m)) = n, from
  have h₁ : 0 < n / m :=
    nat.pos_of_ne_zero $ λ h,
    have n = 0 * m := (nat.div_eq_iff_eq_mul_left (min_fac_pos _) (min_fac_dvd _)).1 h,
    by rw zero_mul at this; exact (show k + 2 ≠ 0, from dec_trivial) this,
  by rw [list.prod_cons, prod_factors _ h₁, nat.mul_div_cancel' (min_fac_dvd _)]
```

This is because for some reason, in the first example, the equation compiler tries to use the always false relation.

Conjecture : this is because the type of `h` depends on `n` and the equation compiler can only synthesize useful relations on non dependent products

### using_well_founded rel_tac ###

Sometimes you need to change the well founded relation to prove that a recursion is well founded. To do this you need a `has_well_founded` instance. This is a structure with two fields, a relation and a proof that this relation is well founded. The easiest way to define a well founded relation is using a function to the natural numbers. For example on multisets the relation `λ s t, card s < card t` is a well founded relation.

The following proof in `data.multiset` uses this relation.

```lean
@[elab_as_eliminator] lemma strong_induction_on {p : multiset α → Sort*} :
  ∀ (s : multiset α), (∀ s, (∀t < s, p t) → p s) → p s
| s := λ ih, ih s $ λ t h,
  have card t < card s, from card_lt_of_lt h,
  strong_induction_on t ih
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf card⟩]}
```

The final line tells the equation compiler to use this relation. It is not necessary to fully understand the final line to be able to use well_founded tactics. The most important part is `⟨_, measure_wf card⟩` This is the well_founded instance. `measure_wf` is a proof that any relation generated from a function to the natural numbers, i.e. for a function `f : α → ℕ`, the relation `λ x y, f x < f y`. The underscore is a placeholder for the relation, as it can be inferred from the type of the proof. Note that the well founded relation must be on a `psigma` type corresponding to the product of the types of the arguments after the vertical bar, if there are multiple arguments after the vertical bar.

In the gcd example the `psigma` type is `Σ' (a : ℕ), ℕ`. In order to solve the problem in the example where the order of the arguments was flipped, you could define a well founded relation on `Σ' (a : ℕ), ℕ` using the function `psigma.snd`, the function giving the second element of the pair, and then the error disappears.

```lean
def gcd : nat → nat → nat
| y 0        := y
| y (succ x) := have y % succ x < succ x, from mod_lt _ $ succ_pos _,
                gcd (succ x) (y % succ x)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf psigma.snd⟩]}
```
