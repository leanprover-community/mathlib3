/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import data.int.basic
/-! # Least upper bound and greatest lower bound properties for integers

In this file we prove that a bounded above nonempty set of integers has the greatest element, and a
counterpart of this statement for the least element.

## Main definitions

* `int.least_of_bdd`: if `P : ℤ → Prop` is a decidable predicate, `b` is a lower bound of the set
  `{m | P m}`, and there exists `m : ℤ` such that `P m` (this time, no witness is required), then
  `int.least_of_bdd` returns the least number `m` such that `P m`, together with proofs of `P m` and
  of the minimality. This definition is computable and does not rely on the axiom of choice.
* `int.greatest_of_bdd`: a similar definition with all inequalities reversed.

## Main statements

* `int.exists_least_of_bdd`: if `P : ℤ → Prop` is a predicate such that the set `{m : P m}` is
  bounded below and nonempty, then this set has the least element. This lemma uses classical logic
  to avoid assumption `[decidable_pred P]`. See `int.least_of_bdd` for a constructive counterpart.

* `int.coe_least_of_bdd_eq`: `(int.least_of_bdd b Hb Hinh : ℤ)` does not depend on `b`.

* `int.exists_greatest_of_bdd`, `int.coe_greatest_of_bdd_eq`: versions of the above lemmas with all
  inequalities reversed.

## Tags

integer numbers, least element, greatest element
-/

namespace int

/-- A computable version of `exists_least_of_bdd`: given a decidable predicate on the
integers, with an explicit lower bound and a proof that it is somewhere true, return
the least value for which the predicate is true. -/
def least_of_bdd {P : ℤ → Prop} [decidable_pred P]
  (b : ℤ) (Hb : ∀ z : ℤ, P z → b ≤ z) (Hinh : ∃ z : ℤ, P z) :
  {lb : ℤ // P lb ∧ (∀ z : ℤ, P z → lb ≤ z)} :=
have EX : ∃ n : ℕ, P (b + n), from
  let ⟨elt, Helt⟩ := Hinh in
  match elt, le.dest (Hb _ Helt), Helt with
  | ._, ⟨n, rfl⟩, Hn := ⟨n, Hn⟩
  end,
⟨b + (nat.find EX : ℤ), nat.find_spec EX, λ z h,
  match z, le.dest (Hb _ h), h with
  | ._, ⟨n, rfl⟩, h := add_le_add_left
    (int.coe_nat_le.2 $ nat.find_min' _ h) _
  end⟩

/-- If `P : ℤ → Prop` is a predicate such that the set `{m : P m}` is bounded below and nonempty,
then this set has the least element. This lemma uses classical logic to avoid assumption
`[decidable_pred P]`. See `int.least_of_bdd` for a constructive counterpart. -/
theorem exists_least_of_bdd {P : ℤ → Prop}
  (Hbdd : ∃ b : ℤ, ∀ z : ℤ, P z → b ≤ z) (Hinh : ∃ z : ℤ, P z) :
  ∃ lb : ℤ, P lb ∧ (∀ z : ℤ, P z → lb ≤ z) :=
by classical; exact let ⟨b, Hb⟩ := Hbdd, ⟨lb, H⟩ := least_of_bdd b Hb Hinh in ⟨lb, H⟩

lemma coe_least_of_bdd_eq {P : ℤ → Prop} [decidable_pred P]
  {b b' : ℤ} (Hb : ∀ z : ℤ, P z → b ≤ z) (Hb' : ∀ z : ℤ, P z → b' ≤ z) (Hinh : ∃ z : ℤ, P z) :
  (least_of_bdd b Hb Hinh : ℤ) = least_of_bdd b' Hb' Hinh :=
begin
  rcases least_of_bdd b Hb Hinh with ⟨n, hn, h2n⟩,
  rcases least_of_bdd b' Hb' Hinh with ⟨n', hn', h2n'⟩,
  exact le_antisymm (h2n _ hn') (h2n' _ hn),
end

/-- A computable version of `exists_greatest_of_bdd`: given a decidable predicate on the
integers, with an explicit upper bound and a proof that it is somewhere true, return
the greatest value for which the predicate is true. -/
def greatest_of_bdd {P : ℤ → Prop} [decidable_pred P]
  (b : ℤ) (Hb : ∀ z : ℤ, P z → z ≤ b) (Hinh : ∃ z : ℤ, P z) :
  {ub : ℤ // P ub ∧ (∀ z : ℤ, P z → z ≤ ub)} :=
have Hbdd' : ∀ (z : ℤ), P (-z) → -b ≤ z, from λ z h, neg_le.1 (Hb _ h),
have Hinh' : ∃ z : ℤ, P (-z), from
let ⟨elt, Helt⟩ := Hinh in ⟨-elt, by rw [neg_neg]; exact Helt⟩,
let ⟨lb, Plb, al⟩ := least_of_bdd (-b) Hbdd' Hinh' in
⟨-lb, Plb, λ z h, le_neg.1 $ al _ $ by rwa neg_neg⟩

/-- If `P : ℤ → Prop` is a predicate such that the set `{m : P m}` is bounded above and nonempty,
then this set has the greatest element. This lemma uses classical logic to avoid assumption
`[decidable_pred P]`. See `int.greatest_of_bdd` for a constructive counterpart. -/
theorem exists_greatest_of_bdd {P : ℤ → Prop}
  (Hbdd : ∃ b : ℤ, ∀ z : ℤ, P z → z ≤ b) (Hinh : ∃ z : ℤ, P z) :
  ∃ ub : ℤ, P ub ∧ (∀ z : ℤ, P z → z ≤ ub) :=
by classical; exact let ⟨b, Hb⟩ := Hbdd, ⟨lb, H⟩ := greatest_of_bdd b Hb Hinh in ⟨lb, H⟩

lemma coe_greatest_of_bdd_eq {P : ℤ → Prop} [decidable_pred P]
  {b b' : ℤ} (Hb : ∀ z : ℤ, P z → z ≤ b) (Hb' : ∀ z : ℤ, P z → z ≤ b') (Hinh : ∃ z : ℤ, P z) :
  (greatest_of_bdd b Hb Hinh : ℤ) = greatest_of_bdd b' Hb' Hinh :=
begin
  rcases greatest_of_bdd b Hb Hinh with ⟨n, hn, h2n⟩,
  rcases greatest_of_bdd b' Hb' Hinh with ⟨n', hn', h2n'⟩,
  exact le_antisymm (h2n' _ hn) (h2n _ hn'),
end

end int
