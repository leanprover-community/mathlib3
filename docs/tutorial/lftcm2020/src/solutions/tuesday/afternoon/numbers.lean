import tactic
import data.real.basic
import data.int.gcd
import data.padics

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
  norm_num
end

example {α : Type} [linear_ordered_field α] : 123 + 45 < 67890/3 :=
begin
  norm_num
end

example : nat.prime 17 :=
begin
  norm_num
end

-- prove either this or its negation!
example : ¬ 7/3 > 2 :=
begin
  norm_num
end

example (x : ℝ) (hx : x < 50*50) : x < 25*100 :=
begin
  norm_num at hx ⊢,
  assumption
end

example (x : ℤ) (hx : (x : ℝ) < 25*100) : x < 25*100 :=
begin
  assumption_mod_cast
end

example (x : ℤ) (hx : (x : ℝ) < 2500) : x < 25*100 :=
begin
  norm_num,
  assumption_mod_cast
end

example (p q r : ℕ) (h : r < p - q) (hpq : q ≤ p) : (r : ℝ) < p - q :=
begin
  exact_mod_cast h,
end

example (p q r : ℕ) (hr : r < p + 2 - p) : (r : ℤ) < 5 :=
begin
  have : p ≤ p + 2, by linarith,
  zify [this] at hr,
  linarith
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
  -- this lemma will be useful later in the proof.
  -- ignore the "inst" argument; just use `apply aux_lemma` when you need it!
  have aux_lemma : ∀ inst, (n : ℤ) ≤ (multiplicity ↑p z).get inst,
  { intro,
    norm_cast,
    rw [← enat.coe_le_coe, enat.coe_get],
    apply multiplicity.le_multiplicity_of_pow_dvd,
    assumption_mod_cast },

  unfold padic_norm, split_ifs with hz hz,
  { apply fpow_nonneg_of_nonneg,
    exact_mod_cast le_of_lt hp.pos },
  { apply fpow_le_of_le,
    exact_mod_cast le_of_lt hp.one_lt,
    apply neg_le_neg,
    rw padic_val_rat_of_int _ hp.ne_one _,
    { apply aux_lemma },
    { assumption_mod_cast } }
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

If you want to peek at the definition of coprime, you can use
`unfold nat.coprime at h`.

-/


-- notice that I've changed the existential to be over ℤ!
example (p q : ℕ) (h : nat.coprime p q) : ∃ u v : ℤ, u*p+v*q = 1 :=
begin
  have := nat.gcd_eq_gcd_ab,
  specialize this p q,
  unfold nat.coprime at h,
  rw h at this,
  norm_cast at this,
  use [p.gcd_a q, p.gcd_b q],
  rw this,
  ring
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
  -- we start like before
  intros ε ε_pos,
  dsimp,

  -- the witness to the existential must be a nat: use `nat_ceil` instead of `ceil`!
  use nat_ceil (1/ε),
  intros n hn,

  -- this proof is used a few times below, so we separate it as an assumption
  have n_pos : 0 < n,
    -- I've written the proofs of the calc block separately, but you could inline them
  { calc 0 < nat_ceil (1/ε) : _
       ... ≤ n : _,
    { rw lt_nat_ceil, simp, assumption },
    { assumption } },

  -- this chain of rewrites generates some side conditions that we get rid of below
  rw [abs_of_nonneg, sub_le_iff_le_add, div_le_iff, add_mul, one_mul,
      add_comm _ (n : ℝ), add_le_add_iff_left],

  -- this calc proof finishes the "main goal"
  { calc 1 = ε * (1/ε) : _
       ... ≤ ε * nat_ceil (1/ε) : _
       ... ≤ ε * n : _,
    { symmetry, apply mul_one_div_cancel, linarith },
    { rw mul_le_mul_left ε_pos, apply le_nat_ceil },
    { rw mul_le_mul_left ε_pos, exact_mod_cast hn } },

  -- we try to discharge the side conditions with as little work as possible
  { assumption_mod_cast },
  { field_simp,
    apply one_le_div_of_le; norm_cast; linarith }
end
