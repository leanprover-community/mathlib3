/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import tactic.doc_commands
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
`[simp only [add_mul, mul_add, sub_eq_add_neg, mul_two, two_mul, pow_two, mul_assoc,
             neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm];
  abel]

add_tactic_doc
{ name       := "noncomm_ring",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.noncomm_ring],
  tags       := ["arithmetic", "simplification", "decision procedure"] }

end interactive
end tactic
