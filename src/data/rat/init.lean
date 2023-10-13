/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import tactic.ext
import logic.basic

/-!
# The definition of the Rational Numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Summary

We define a rational number `q` as a structure `{ num, denom, pos, cop }`, where
- `num` is the numerator of `q`,
- `denom` is the denominator of `q`,
- `pos` is a proof that `denom > 0`, and
- `cop` is a proof `num` and `denom` are coprime.

Basic constructions and results are set up in `data.rat.defs`.
As we transition to Lean 4, these two files can probably be merged again,
as so much of the needed material will be in Std4 anyway.

For now, this split allows us to give the definitions of division rings and fields
without significant theory imports.

The definition of the field structure on `ℚ` will be done in `data.rat.basic` once the
`field` class has been defined.

## Main Definitions

- `rat` is the structure encoding `ℚ`.

## Notations

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom
-/

/-- `rat`, or `ℚ`, is the type of rational numbers. It is defined
  as the set of pairs ⟨n, d⟩ of integers such that `d` is positive and `n` and
  `d` are coprime. This representation is preferred to the quotient
  because without periodic reduction, the numerator and denominator can grow
  exponentially (for example, adding 1/2 to itself repeatedly). -/
structure rat := mk' ::
(num : ℤ)
(denom : ℕ)
(pos : 0 < denom)
(cop : num.nat_abs.coprime denom)
notation `ℚ` := rat

namespace rat

/-- String representation of a rational numbers, used in `has_repr`, `has_to_string`, and
`has_to_format` instances. -/
protected def repr : ℚ → string
| ⟨n, d, _, _⟩ := if d = 1 then _root_.repr n else
  _root_.repr n ++ "/" ++ _root_.repr d

instance : has_repr ℚ := ⟨rat.repr⟩
instance : has_to_string ℚ := ⟨rat.repr⟩
meta instance : has_to_format ℚ := ⟨coe ∘ rat.repr⟩

lemma ext_iff {p q : ℚ} : p = q ↔ p.num = q.num ∧ p.denom = q.denom :=
by { cases p, cases q, simp }

@[ext] lemma ext {p q : ℚ} (hn : p.num = q.num) (hd : p.denom = q.denom) : p = q :=
rat.ext_iff.mpr ⟨hn, hd⟩

end rat
