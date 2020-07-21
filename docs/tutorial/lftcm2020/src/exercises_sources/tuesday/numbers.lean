import tactic
import data.real.basic
import data.padics
import data.int.gcd

/-!

## Exercises about numbers and casts

-/

/-!

## First exercises

These first examples are just to get you comfortable with
`norm_num`, `norm_cast`, and friends.

-/


example : 12345 < 67890 :=
begin
  sorry
end

example {α : Type} [linear_ordered_field α] : 123 + 45 < 67890/3 :=
begin
  sorry
end

example : nat.prime 17 :=
begin
  sorry
end

-- prove either this or its negation!
example : 7/3 > 2 :=
begin
  sorry
end


example (x : ℝ) (hx : x < 50*50) : x < 25*100 :=
begin
  sorry
end

example (x : ℤ) (hx : (x : ℝ) < 25*100) : x < 25*100 :=
begin
  sorry
end

example (x : ℤ) (hx : (x : ℝ) < 2500) : x < 25*100 :=
begin
  sorry
end

example (p q r : ℕ) (h : r < p - q) (hpq : q ≤ p) : (r : ℝ) < p - q :=
begin
  sorry
end

example (p q r : ℕ) (hr : r < p + 2 - p) : (r : ℤ) < 5 :=
begin
  sorry
end


/-!

## Exercise 2

This comes from the development of the p-adic numbers.
`norm_cast` is very useful here, since we need to talk about values in
ℕ, ℤ, ℚ, ℚ_p, and ℤ_p.

We've done some work to get you started. You might look for the lemmas:
-/

open padic_val_rat

#check fpow_le_of_le
#check fpow_nonneg_of_nonneg
#check padic_val_rat_of_int


example {p n : ℕ} (hp : p.prime) {z : ℤ} (hd : ↑(p^n) ∣ z) : padic_norm p z ≤ ↑p ^ (-n : ℤ) :=
begin
  -- This lemma will be useful later in the proof.
  -- Ignore the "inst" argument; just use `apply aux_lemma` when you need it!
  -- Note that we haven't finished it. Fill in that final sorry.
  have aux_lemma : ∀ inst, (n : ℤ) ≤ (multiplicity ↑p z).get inst,
  { intro,
    norm_cast,
    rw [← enat.coe_le_coe, enat.coe_get],
    apply multiplicity.le_multiplicity_of_pow_dvd,
    sorry },

  unfold padic_norm, split_ifs with hz hz,
  { sorry },
  { sorry }
end





/-!

## Exercise 3

This seems like a very natural way to write the theorem
"If `a` and `b` are coprime, then there are coefficients `u` and `v` such that `u*a + v*b = 1`."

But I've made a mistake! What did I do wrong? Correct the statement of the theorem and prove it.

I've started you off with a lemma that will be useful.
You might find the `specialize` tactic to be handy as well:
if you have `h : ∀ (x y : T), R x y` and `a, b : T` in the context, then
`specialize h a b` will change the type of `h` to `R a b`.

-/

example (a b : ℕ) (h : nat.coprime a b) : ∃ u v, u*a+v*b = 1 :=
begin
  have := nat.gcd_eq_gcd_ab,
  sorry
end






/-!

## Exercise 4

We did an example together that was similar to this.

This one takes a bit more arithmetic work.
To save you some time, here are some lemmas that may be useful!
(You may not need all of them, depending on how you approach it.)

Remember you can also use `library_search` to try to find useful lemmas.

A hint: you might find it helpful to do this once you've introduced `n`.
```
have n_pos: 0 < n,
{ ... }
```

-/

#check sub_le_iff_le_add
#check add_le_add_iff_left
#check div_le_iff
#check mul_one_div_cancel
#check mul_le_mul_left


notation `|`x`|` := abs x

def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε



example : seq_limit (λ n : ℕ, (n+1)/n) 1 :=
begin
  sorry
end
