/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import order.conditionally_complete_lattice

/-!
## `ℤ` forms a conditionally complete linear order

The integers form a conditionally complete linear order.
-/

open int
open_locale classical
noncomputable theory

/-! ### Least upper bound property for integers -/

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

instance : conditionally_complete_linear_order ℤ :=
{ Sup := λ s, if h : s.nonempty ∧ bdd_above s then
    greatest_of_bdd (classical.some h.2) (classical.some_spec h.2) h.1 else 0,
  Inf := λ s, if h : s.nonempty ∧ bdd_below s then
    least_of_bdd (classical.some h.2) (classical.some_spec h.2) h.1 else 0,
  le_cSup := begin
    intros s n hs hns,
    have : s.nonempty ∧ bdd_above s := ⟨⟨n, hns⟩, hs⟩,
    rw [dif_pos this],
    exact (greatest_of_bdd _ _ _).2.2 n hns
  end,
  cSup_le := begin
    intros s n hs hns,
    have : s.nonempty ∧ bdd_above s := ⟨hs, ⟨n, hns⟩⟩,
    rw [dif_pos this],
    exact hns (greatest_of_bdd _ (classical.some_spec this.2) _).2.1
  end,
  cInf_le := begin
    intros s n hs hns,
    have : s.nonempty ∧ bdd_below s := ⟨⟨n, hns⟩, hs⟩,
    rw [dif_pos this],
    exact (least_of_bdd _ _ _).2.2 n hns
  end,
  le_cInf := begin
    intros s n hs hns,
    have : s.nonempty ∧ bdd_below s := ⟨hs, ⟨n, hns⟩⟩,
    rw [dif_pos this],
    exact hns (least_of_bdd _ (classical.some_spec this.2) _).2.1
  end,
  .. int.linear_order, ..lattice_of_linear_order }

namespace int

lemma cSup_eq_greatest_of_bdd {s : set ℤ} [decidable_pred (∈ s)]
  (b : ℤ) (Hb : ∀ z ∈ s, z ≤ b) (Hinh : ∃ z : ℤ, z ∈ s) :
  Sup s = greatest_of_bdd b Hb Hinh :=
begin
  convert dif_pos _ using 1,
  { convert coe_greatest_of_bdd_eq _ (classical.some_spec (⟨b, Hb⟩ : bdd_above s)) _ },
  { exact ⟨Hinh, b, Hb⟩, }
end

@[simp]
lemma cSup_empty : Sup (∅ : set ℤ) = 0 := dif_neg (by simp)

lemma cSup_of_not_bdd_above {s : set ℤ} (h : ¬ bdd_above s) : Sup s = 0 := dif_neg (by simp [h])

lemma cInf_eq_least_of_bdd {s : set ℤ} [decidable_pred (∈ s)]
  (b : ℤ) (Hb : ∀ z ∈ s, b ≤ z) (Hinh : ∃ z : ℤ, z ∈ s) :
  Inf s = least_of_bdd b Hb Hinh :=
begin
  convert dif_pos _ using 1,
  { convert coe_least_of_bdd_eq _ (classical.some_spec (⟨b, Hb⟩ : bdd_below s)) _ },
  { exact ⟨Hinh, b, Hb⟩, }
end

@[simp]
lemma cInf_empty : Inf (∅ : set ℤ) = 0 := dif_neg (by simp)

lemma cInf_of_not_bdd_below {s : set ℤ} (h : ¬ bdd_below s) : Inf s = 0 := dif_neg (by simp [h])

lemma cSup_mem {s : set ℤ} (h1 : s.nonempty) (h2 : bdd_above s) : Sup s ∈ s :=
begin
  convert (greatest_of_bdd _ (classical.some_spec h2) h1).2.1,
  exact dif_pos ⟨h1, h2⟩,
end

lemma cInf_mem {s : set ℤ} (h1 : s.nonempty) (h2 : bdd_below s) : Inf s ∈ s :=
begin
  convert (least_of_bdd _ (classical.some_spec h2) h1).2.1,
  exact dif_pos ⟨h1, h2⟩,
end

end int
