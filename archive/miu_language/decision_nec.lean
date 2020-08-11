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

Let `icount st` denote the number of `I`s in `st : miustr`. We'll show that the `icount` of a
derivable string must be 1 or 2 moduloe 3. To do this, it suffices to show that if the `miustr`
`en` is derived from `st`, then `icount en` moudulo 3 is either equal to or is twice `icount st`
modulo 3.
-/

/--
`icount` is the number of `I`s in an `miustr`
-/
def icount : miustr → ℕ
| [] := 0
| (I::cs) := 1 + icount cs
| (_::cs) := icount cs

/--
`icount` is additive with respect to `append`
-/
lemma icountappend (a b : miustr) :
  icount (a ++ b) = icount a + icount b :=
begin
  induction a with x hx hxs, -- treat a as x :: xs in the inductive step
    simp [icount], -- trivial base case
    cases x; -- the same proof applies whether x = 'M', 'I', or 'U'
      simp [icount, hxs, add_assoc],
end

open nat

/--
Given `st en : miustr`, the relation `nice_imod3 st en` holds if `st` and `en` either
have equal `icount`, modulo 3, or `icount en` is twice `icount st`, modulo 3.`
 -/
def nice_imod3 (st en : miustr) : Prop :=
  let a := (icount st) in
  let b := (icount en) in
  b ≡ a [MOD 3] ∨ b ≡ 2*a [MOD 3]

example : nice_imod3 "II" "MIUI" :=
begin
  left, refl, -- icount "MIUI" ≡ icount "II" [MOD 3]
end

example : nice_imod3 "IUIM" "MI" :=
begin
  right, refl, --icount "MI" ≡ 2*(icount "IUIUM") [MOD 3]
end


/-  We show the icount, mod 3, stays the same or is multiplied by 2 under the rules of inference -/

open nat

/- Now we show that the icount of a derivable string is 1 or 2 modulo 3-/

-- We start with a general result about natural numbers.

lemma inheritmod3 {a b : ℕ} (h1 : a % 3 = 1 ∨ a % 3 = 2)
  (h2 : b % 3 = a % 3 ∨  b % 3 = (2 * a % 3)) :
    b % 3 = 1 ∨ b % 3 = 2 :=
begin
  cases h2, {
    rw h2,
    exact h1,
  }, {
    cases h1, {
      right,
      simp [h2,mul_mod,h1],
      refl,
    }, {
      left,
      simp [h2,mul_mod,h1],
      refl,
    }
  }
end


/--
`inctder` shows any derivable string must have an `icount` that is 1 or 2 modulo 3.
-/
theorem icntder (en : miustr): derivable en →
  (icount en) % 3 = 1 ∨ (icount en) % 3 = 2:=
begin
  intro h,
  induction h,
    left,
    apply mod_def,
    any_goals {apply inheritmod3 h_ih},
      left, simp only [icountappend], refl,
      right, simp only [icount,icountappend],ring,
      left, simp [icountappend,icount,refl], ring,
      left, simp [icountappend,icount,refl],
end

/--
Using the above theorem, we solve the MU puzzle, showing that `"MU"` is not derivable.
-/
theorem notmu : ¬(derivable "MU") :=
begin
  intro h,
  cases (icntder _ h);
    contradiction,
end


/-
### Condition on `M`

That solves the MU puzzle, but we'll proceed by demonstrating the other necessary condition for a
string to be derivable, namely that the string must start with an M and contain no M in its tail.
-/


/--
`goodm xs` holds if `xs : miustr` begins with `M` and contains no `M` in its tail.
-/
def goodm (xs : miustr) : Prop :=
  ∃ ys : miustr, xs = (M::ys) ∧ ¬(M ∈ ys)

/- Example usage -/

lemma goodmi : goodm [M,I] :=
begin
  split,
    swap,
  exact [I],
  simp,
end

/-
We'll show, for each `i` from 1 to 4, that if `en` follows by rule `i` from `st` and if
`goodm st` holds, then so does `goodm en`.
-/


open list

lemma goodmrule1 (xs : miustr) (h₁ : derivable (xs ++ [I])) (h₂ : goodm (xs ++ [I]))
  : goodm (xs ++ [I,U]) :=
begin
  rcases h₂ with ⟨ys, k₁, k₂⟩,
  use ys ++ [U],
  split,
    rw [←(cons_append _ _ _), ←k₁], simp,
  simp [k₂],
end


lemma goodmrule2 (xs : miustr) (h₁ : derivable (M :: xs))
  (h₂ : goodm (M :: xs)) : goodm (M :: xs ++ xs) :=
begin
  rcases h₂ with ⟨ys, k₁, k₂⟩,
  use (ys ++ ys),
  split,
    rw (cons_inj _).mp k₁,
    refl,
  simp [k₂],
end


lemma goodmrule3  (as bs : miustr) (h₁ : derivable (as ++ [I,I,I] ++ bs))
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


-- The proof of the next lemma is very similar to the previous proof!

lemma goodmrule4  (as bs : miustr) (h₁ : derivable (as ++ [U,U] ++ bs))
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


/--
Any derivable string must begin with `M` and contain no `M` in its tail.
-/


theorem goodmder (en : miustr): derivable en →
  goodm en:=
begin
  intro h,
  induction h,
    exact goodmi,
  apply goodmrule1; assumption,
  apply goodmrule2; assumption,
  apply goodmrule3; assumption,
  apply goodmrule4; assumption,
end

/-
We put togther our two conditions to give one condition `decstr`. Once we've proved sufficiency of
this condition, we'll have proved that checking the condition is a decision procedure.
-/

/--
`decstr en` is the condition that `icount en` is 1 or 2 modulo 3, that `en` starts with `M`, and
that `en` contains no `M` in its tail.
-/
def decstr (en : miustr) :=
  goodm en ∧ ((icount en) % 3 = 1 ∨ (icount en) % 3 = 2)

/--
Suppose `en : miustr`. If `en` is `derivable`, then the condition `decstr en` holds.
-/
theorem decstr_of_der (en : miustr) : derivable en → decstr en :=
begin
  intro h,
  split,
    exact goodmder en h,
    exact icntder en h
end

end miu
