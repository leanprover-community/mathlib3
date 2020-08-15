/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import data.nat.basic

/-!
# `nat.up`

`nat.up p`, with `p` a predicate on `ℕ`, is a subtype of `ℕ` that contains value
`n` if no value below `n` (excluding `n`) satisfies `p`.

This allows us to prove `>` is well-founded when `∃ i, p i`. This helps implement
searches on `ℕ`, starting at `0` and with an unknown upper-bound.

-/

namespace nat

@[reducible]
def up (p : ℕ → Prop) : Type := { i : ℕ // (∀ j < i, ¬ p j) }

namespace up

variable {p : ℕ → Prop}

protected def lt (p) : up p → up p → Prop := λ x y, x.1 > y.1

instance : has_lt (up p) :=
{ lt := λ x y, x.1 > y.1 }

protected def wf : Exists p → well_founded (up.lt p)
| ⟨x,h⟩ :=
have h : (<) = measure (λ y : nat.up p, x - y.val),
  by { ext, dsimp [measure,inv_image],
       rw nat.sub_lt_sub_left_iff, refl,
       by_contradiction h', revert h,
       apply x_1.property _ (lt_of_not_ge h'), },
cast (congr_arg _ h.symm) (measure_wf _)

def zero : nat.up p := ⟨ 0, λ j h, false.elim (nat.not_lt_zero _ h) ⟩

def succ (x : nat.up p) (h : ¬ p x.val) : nat.up p :=
⟨x.val.succ, by { intros j h', rw nat.lt_succ_iff_lt_or_eq at h',
                  cases h', apply x.property _ h', subst j, apply h } ⟩

end up
end nat
