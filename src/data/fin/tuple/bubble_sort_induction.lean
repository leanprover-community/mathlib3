/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import data.fin.tuple.sort
import data.fintype.perm
import order.well_founded

/-!
# "Bubble sort" induction

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We implement the following induction principle `tuple.bubble_sort_induction`
on tuples with values in a linear order `α`.

Let `f : fin n → α` and let `P` be a predicate on `fin n → α`. Then we can show that
`f ∘ sort f` satisfies `P` if `f` satisfies `P`, and whenever some `g : fin n → α`
satisfies `P` and `g i > g j` for some `i < j`, then `g ∘ swap i j` also satisfies `P`.

We deduce it from a stronger variant `tuple.bubble_sort_induction'`, which
requires the assumption only for `g` that are permutations of `f`.

The latter is proved by well-founded induction via `well_founded.induction_bot'`
with respect to the lexicographic ordering on the finite set of all permutations of `f`.
-/

namespace tuple

/-- *Bubble sort induction*: Prove that the sorted version of `f` has some property `P`
if `f` satsifies `P` and `P` is preserved on permutations of `f` when swapping two
antitone values. -/
lemma bubble_sort_induction' {n : ℕ} {α : Type*} [linear_order α] {f : fin n → α}
  {P : (fin n → α) → Prop} (hf : P f)
  (h : ∀ (σ : equiv.perm (fin n)) (i j : fin n),
              i < j → (f ∘ σ) j < (f ∘ σ) i → P (f ∘ σ) → P (f ∘ σ ∘ equiv.swap i j)) :
  P (f ∘ sort f) :=
begin
  letI := @preorder.lift _ (lex (fin n → α)) _ (λ σ : equiv.perm (fin n), to_lex (f ∘ σ)),
  refine @well_founded.induction_bot' _ _ _
    (@finite.preorder.well_founded_lt (equiv.perm (fin n)) _ _)
    (equiv.refl _) (sort f) P (λ σ, f ∘ σ) (λ σ hσ hfσ, _) hf,
  obtain ⟨i, j, hij₁, hij₂⟩ := antitone_pair_of_not_sorted' hσ,
  exact ⟨σ * equiv.swap i j, pi.lex_desc hij₁ hij₂, h σ i j hij₁ hij₂ hfσ⟩,
end

/-- *Bubble sort induction*: Prove that the sorted version of `f` has some property `P`
if `f` satsifies `P` and `P` is preserved when swapping two antitone values. -/
lemma bubble_sort_induction {n : ℕ} {α : Type*} [linear_order α] {f : fin n → α}
  {P : (fin n → α) → Prop} (hf : P f)
  (h : ∀ (g : fin n → α) (i j : fin n), i < j → g j < g i → P g → P (g ∘ equiv.swap i j)) :
  P (f ∘ sort f) :=
bubble_sort_induction' hf (λ σ, h _)

end tuple
