/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Oliver Nash
-/
import tactic.abel

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
`[simp only [-- Expand everything out.
             add_mul, mul_add, sub_eq_add_neg,
             -- Right associate all products.
             mul_assoc,
             -- Expand powers to numerals.
             pow_bit0, pow_bit1, pow_one,
             -- Replace multiplication by numerals with `gsmul`.
             bit0_mul, mul_bit0, bit1_mul, mul_bit1, one_mul, mul_one, zero_mul, mul_zero,
             -- Pull `gsmul n` out the front so `abel` can see them.
             ←mul_gsmul_assoc, ←mul_gsmul_left,
             -- Pull out negations.
             neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm] {fail_if_unchanged := ff};
  abel]

add_tactic_doc
{ name       := "noncomm_ring",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.noncomm_ring],
  tags       := ["arithmetic", "simplification", "decision procedure"] }

end interactive
end tactic
