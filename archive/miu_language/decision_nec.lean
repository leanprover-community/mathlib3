/-
Copyright (c) 2020 Gihan Marasingha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gihan Marasingha
-/
import .basic
import data.nat.modeq
import tactic.ring

/-!
# Decision procedure - necessary condition

We introduce a condition `decstr` and show that if a string `en` is `derivable`, then `decstr en`
holds.

Using this, we give a negative answer to the question: is `"MU"` derivable?
-/

namespace miu

open miu_atom

/-!
### Numerical condition on the `I` count

Suppose `st : miustr`. Then `count I st` is the number of `I`s in `st. We'll show, if
`derivable st`, then `count I st` must be 1 or 2 modulo 3. To do this, it suffices to show that if
the `en : miustr` is derived from `st`, then `count I en` moudulo 3 is either equal to or is twice
`count I st`, modulo 3.
-/


open nat
open list

/--
Given `st en : miustr`, the relation `count_equiv_or_equiv_two_mul_mod3 st en` holds if `st` and
`en` either have equal `count I`, modulo 3, or `count I en` is twice `count I st`, modulo 3.
 -/
def count_equiv_or_equiv_two_mul_mod3 (st en : miustr) : Prop :=
  let a := (count I st) in
  let b := (count I en) in
  b ≡ a [MOD 3] ∨ b ≡ 2*a [MOD 3]

example : count_equiv_or_equiv_two_mul_mod3 "II" "MIUI" :=
  or.inl rfl

example : count_equiv_or_equiv_two_mul_mod3 "IUIM" "MI" :=
  or.inr rfl

/-!
We show the `count I`, mod 3, stays the same or is multiplied by 2 under the rules of inference.
-/

open nat

/-!
Now we show that the `count I` of a derivable string is 1 or 2 modulo 3.
-/



/-!
We start with a general result about natural numbers.
-/

lemma inherit_mod3 {a b : ℕ} (h1 : a % 3 = 1 ∨ a % 3 = 2)
  (h2 : b % 3 = a % 3 ∨  b % 3 = (2 * a % 3)) :
    b % 3 = 1 ∨ b % 3 = 2 :=
begin
  cases h2, {
    rw h2, exact h1,
  }, {
    cases h1, {
      right, simpa [h2,mul_mod,h1],
    }, {
      left, simpa [h2,mul_mod,h1],
    }
  }
end


/--
`count_equiv_one_or_two_mod3_of_derivable` shows any derivable string must have an `count I` that
is 1 or 2 modulo 3.
-/
theorem count_equiv_one_or_two_mod3_of_derivable (en : miustr): derivable en →
  (count I en) % 3 = 1 ∨ (count I en) % 3 = 2:=
begin
  intro h,
  induction h,
    left,
    apply mod_def,
    any_goals {apply inherit_mod3 h_ih},
      left, simp only [count_append], refl,
      right, simp [count,count_append], ring,
      left, simp [count_append,count I,refl], ring,
      left, simp [count_append,count I,refl],
end

/--
Using the above theorem, we solve the MU puzzle, showing that `"MU"` is not derivable.
-/
theorem not_derivable_mu : ¬(derivable "MU") :=
begin
  intro h,
  cases (count_equiv_one_or_two_mod3_of_derivable _ h);
    contradiction,
end


/-!
### Condition on `M`

That solves the MU puzzle, but we'll proceed by demonstrating the other necessary condition for a
string to be derivable, namely that the string must start with an M and contain no M in its tail.
-/


/--
`goodm xs` holds if `xs : miustr` begins with `M` and contains no `M` in its tail.
-/
def goodm (xs : miustr) : Prop :=
  ∃ ys : miustr, xs = (M::ys) ∧ ¬(M ∈ ys)

/-!
Example usage
-/

lemma goodmi : goodm [M,I] :=
begin
  constructor,
    swap,
  exact [I],
  split, refl, rw mem_singleton, trivial,
end

/-!
We'll show, for each `i` from 1 to 4, that if `en` follows by rule `i` from `st` and if
`goodm st` holds, then so does `goodm en`.
-/

open list

lemma goodm_of_rule1 (xs : miustr) (h₁ : derivable (xs ++ [I])) (h₂ : goodm (xs ++ [I]))
  : goodm (xs ++ [I,U]) :=
begin
  rcases h₂ with ⟨ys, k₁, k₂⟩,
  use ys ++ [U],
  split, {
    rw [←(cons_append _ _ _), ←k₁],
    simp only [append_assoc,singleton_append],
  },
  simp [k₂],
end


lemma goodm_of_rule2 (xs : miustr) (h₁ : derivable (M :: xs))
  (h₂ : goodm (M :: xs)) : goodm (M :: xs ++ xs) :=
begin
  rcases h₂ with ⟨ys, k₁, k₂⟩,
  use (ys ++ ys),
  split, {
    rw (cons_inj _).mp k₁,
    refl,
  },
  simp [k₂],
end


lemma goodm_of_rule3  (as bs : miustr) (h₁ : derivable (as ++ [I,I,I] ++ bs))
  (h₂ : goodm (as ++ [I,I,I] ++ bs)) : goodm (as ++ U :: bs) :=
begin
  rcases h₂ with ⟨ys, p₁, p₂⟩,
  change as ++ [I,I,I] ++ bs with (as ++ [I,I,I]) ++ bs at p₁,
  have h : ∃ zs, as = M :: zs,
    induction as with x xs hxs, { -- base case
      exfalso,
      have : I = M,
        exact head_eq_of_cons_eq p₁,
      contradiction,
    }, {
      use xs,
      rw head_eq_of_cons_eq p₁,
    },
  cases h with zs h,
  use (zs++[U]++bs),
  split, {
    simp [h],
  }, {
    rw h at p₁,
    rw ←((cons_inj M).mp p₁) at p₂,
    simp [append_eq_has_append] at p₂,
    simp [mem_append] at *,
    exact p₂,
  },
end

/-!
 The proof of the next lemma is very similar to the previous proof!
-/

lemma goodm_of_rule4  (as bs : miustr) (h₁ : derivable (as ++ [U,U] ++ bs))
  (h₂ : goodm (as ++ [U,U] ++ bs)) : goodm (as ++ bs) :=
begin
  rcases h₂ with ⟨ys, p₁, p₂⟩,
  change as ++ [U,U] ++ bs with (as ++ [U,U]) ++ bs at p₁,
  have h : ∃ zs, as = M :: zs,
    induction as with x xs hxs, { -- base case
      exfalso,
      have : U = M,
        exact head_eq_of_cons_eq p₁,
      contradiction,
    }, {
      use xs,
      rw head_eq_of_cons_eq p₁,
    },
  cases h with zs h,
  use (zs++bs),
  split, {
    rw h, refl,
  }, {
    rw h at p₁,
    rw ←((cons_inj M).mp p₁) at p₂,
    simp [append_eq_has_append] at p₂,
    simp [mem_append] at *,
    exact p₂,
  }
end


/-!
Any derivable string must begin with `M` and contain no `M` in its tail.
-/


theorem goodm_of_derivable (en : miustr): derivable en →
  goodm en:=
begin
  intro h,
  induction h,
    exact goodmi,
  apply goodm_of_rule1; assumption,
  apply goodm_of_rule2; assumption,
  apply goodm_of_rule3; assumption,
  apply goodm_of_rule4; assumption,
end

/-!
We put togther our two conditions to give one condition `decstr`. Once we've proved sufficiency of
this condition, we'll have proved that checking the condition is a decision procedure.
-/

/--
`decstr en` is the condition that `count I en` is 1 or 2 modulo 3, that `en` starts with `M`, and
that `en` contains no `M` in its tail.
-/
def decstr (en : miustr) :=
  goodm en ∧ ((count I en) % 3 = 1 ∨ (count I en) % 3 = 2)

/--
Suppose `en : miustr`. If `en` is `derivable`, then the condition `decstr en` holds.
-/
theorem decstr_of_der (en : miustr) : derivable en → decstr en :=
begin
  intro h,
  split,
    exact goodm_of_derivable en h,
    exact count_equiv_one_or_two_mod3_of_derivable en h
end

end miu
