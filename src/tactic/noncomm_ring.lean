/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Oliver Nash
-/
import tactic.abel

namespace tactic
namespace interactive

/--
Try to simplify expressions in a not-necessarily-commutative ring.
This does not achieve a normal form for such expressions.
-/
meta def noncomm_ring_simp :=
`[simp only [-- Expand everything out.
             add_mul, mul_add, sub_eq_add_neg,
             -- Right associate all products.
             mul_assoc,
             -- Expand powers to numerals.
             pow_bit0, pow_bit1, pow_one,
             -- Replace multiplication by numerals with `zsmul`.
             bit0_mul, mul_bit0, bit1_mul, mul_bit1, one_mul, mul_one, zero_mul, mul_zero,
             -- Pull `zsmul n` out the front so `abel` can see them.
             mul_smul_comm, smul_mul_assoc,
             -- Pull out negations.
             neg_mul, mul_neg] {fail_if_unchanged := ff}]

/--
A tactic for solving identities in not-necessarily-commutative rings.
It is not a complete decision procedure.

An example:
```lean
example {R : Type*} [ring R] (a b c : R) : a * (b + c + c - b) = 2*a*c :=
by noncomm_ring
```
-/
meta def noncomm_ring1 :=
noncomm_ring_simp >> (done <|> `[abel1])

/--
A tactic for simplifying expressions in not-necessarily-commutative rings.
Unlike `ring_nf`, there is not a normal form for expressions,
so it may fail to solve some identities.

An example:
```lean
example {R : Type*} [ring R] (a b c : R) : a * (b + c + c - b) = 2*a*c :=
by noncomm_ring
```
-/
meta def noncomm_ring_nf :=
noncomm_ring_simp >> (done <|> `[abel_nf])

/--
A tactic for solving identities and simplifying expressions in not-necessarily-commutative rings.
Unlike `ring`, there is not a normal form for expressions,
and in particular not all identites can be solved.
-/
meta def noncomm_ring :=
noncomm_ring_simp >> (done <|> `[abel1] <|> (`[abel_nf] >> trace "Try this: noncomm_ring_nf"))

add_tactic_doc
{ name       := "noncomm_ring",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.noncomm_ring],
  tags       := ["arithmetic", "simplification", "decision procedure"] }

end interactive
end tactic
