/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import data.nat.basic

/-!
# `nat.upto`

`nat.upto p`, with `p` a predicate on `ℕ`, is a subtype of elements `n : ℕ` such that no value
(strictly) below `n` satisfies `p`.

This type has the property that `>` is well-founded when `∃ i, p i`, which allows us to implement
searches on `ℕ`, starting at `0` and with an unknown upper-bound.

It is similar to the well founded relation constructed to define `nat.find` with
the difference that, in `nat.upto p`, `p` does not need to be decidable. In fact,
`nat.find` could be slightly altered to factor decidability out of its
well founded relation and would then fulfill the same purpose as this file.
-/

namespace nat

/-- The subtype of natural numbers `i` which have the property that
no `j` less than `i` satisfies `p`. This is an initial segment of the
natural numbers, up to and including the first value satisfying `p`.

We will be particularly interested in the case where there exists a value
satisfying `p`, because in this case the `>` relation is well-founded.  -/
@[reducible]
def upto (p : ℕ → Prop) : Type := {i : ℕ // ∀ j < i, ¬ p j}

namespace upto

variable {p : ℕ → Prop}

/-- Lift the "greater than" relation on natural numbers to `nat.upto`. -/
protected def gt (p) (x y : upto p) : Prop := x.1 > y.1

instance : has_lt (upto p) := ⟨λ x y, x.1 < y.1⟩

/-- The "greater than" relation on `upto p` is well founded if (and only if) there exists a value
satisfying `p`. -/
protected lemma wf : (∃ x, p x) → well_founded (upto.gt p)
| ⟨x, h⟩ := begin
  suffices : upto.gt p = measure (λ y : nat.upto p, x - y.val),
  { rw this, apply measure_wf },
  ext ⟨a, ha⟩ ⟨b, _⟩,
  dsimp [measure, inv_image, upto.gt],
  rw sub_lt_sub_iff_left_of_le,
  exact le_of_not_lt (λ h', ha _ h' h),
end

/-- Zero is always a member of `nat.upto p` because it has no predecessors. -/
def zero : nat.upto p := ⟨0, λ j h, false.elim (nat.not_lt_zero _ h)⟩

/-- The successor of `n` is in `nat.upto p` provided that `n` doesn't satisfy `p`. -/
def succ (x : nat.upto p) (h : ¬ p x.val) : nat.upto p :=
⟨x.val.succ, λ j h', begin
  rcases nat.lt_succ_iff_lt_or_eq.1 h' with h' | rfl;
  [exact x.2 _ h', exact h]
end⟩

end upto
end nat
