/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Oliver Nash
-/
import tactic.doc_commands
import tactic.abel

-- TODO this should be moved to `algebra/group_power.lean`.
section
variables {R : Type*} [ring R]

lemma bit0_mul {n r : R} : bit0 n * r = gsmul 2 (n * r) :=
by { dsimp [bit0], rw [add_mul, add_gsmul, one_gsmul], }

lemma mul_bit0 {n r : R} : r * bit0 n = gsmul 2 (r * n) :=
by { dsimp [bit0], rw [mul_add, add_gsmul, one_gsmul], }

lemma bit1_mul {n r : R} : bit1 n * r = gsmul 2 (n * r) + r :=
by { dsimp [bit1], rw [add_mul, bit0_mul, one_mul], }

lemma mul_bit1 {n r : R} : r * bit1 n = gsmul 2 (r * n) + r :=
by { dsimp [bit1], rw [mul_add, mul_bit0, mul_one], }

end

namespace tactic
namespace interactive

/-- A tactic for simplifying identities in not-necessarily-commutative rings.

An example:
```lean
example {R : Type*} [ring R] (a b c : R) : a * (b + c + c - b) = 2*a*c :=
by noncomm_ring
```
-/
meta def noncomm_ring :=
`[simp only [add_mul, mul_add, sub_eq_add_neg,
             mul_assoc,
             -- We expand powers to numerals.
             pow_bit0, pow_bit1, pow_one,
             -- We replace multiplication by numerals with `gsmul`.
             bit0_mul, mul_bit0, bit1_mul, mul_bit1, one_mul, mul_one, zero_mul, mul_zero,
             -- We pull `gsmul n` out the front so `abel` can see them.
             ←mul_gsmul_assoc, ←mul_gsmul_left,
             -- we pull out negations.
             neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm];
  abel]

add_tactic_doc
{ name       := "noncomm_ring",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.noncomm_ring],
  tags       := ["arithmetic", "simplification", "decision procedure"] }

end interactive
end tactic
