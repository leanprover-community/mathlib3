/-
Copyright (c) 2020 Kyle Miller All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kyle Miller.
-/

import data.multiset.basic
import data.vector
import tactic.tidy

/-!
# Symmetric powers

This file defines symmetric powers of a type.  The nth symmetric power
consists of homogeneous n-tuples modulo permutations by the symmetric
group.

The special case of 2-tuples is called the symmetric square, which is
addressed in more detail in `data.sym2`.

TODO: This was created as supporting material for `data.sym2`; it
needs a fleshed-out interface.

## Tags

symmetric powers

-/

/--
The nth symmetric power is n-tuples up to permutation.  We define it
as a subtype of `multiset` since these are well developed in the
library.  We also give a definition `sym.sym'` in terms of vectors, and we
show these are equivalent in `sym.sym_equiv_sym'`.
-/
def sym (α : Type*) (n : ℕ) := {s : multiset α // s.card = n}

/--
This is the `list.perm` setoid lifted to `vector`.
-/
def vector.perm.is_setoid (α : Type*) (n : ℕ) : setoid (vector α n) :=
{ r := λ a b, list.perm a.1 b.1,
  iseqv := by { rcases list.perm.eqv α with ⟨hr, hs, ht⟩, tidy, } }

local attribute [instance] vector.perm.is_setoid

namespace sym

/--
Another definition of the nth symmetric power, using vectors modulo permutations. (See `sym`.)
-/
def sym' (α : Type*) (n : ℕ) := quotient (vector.perm.is_setoid α n)

/--
Multisets of cardinality n are equivalent to length-n vectors up to permutations.
-/
def sym_equiv_sym' (α : Type*) (n : ℕ) : sym α n ≃ sym' α n :=
equiv.subtype_quotient_equiv_quotient_subtype _ _ (λ _, by refl) (λ _ _, by refl)

section inhabited
-- Instances to make the linter happy

variables (α : Type*)

instance inhabited_sym [inhabited α] (n : ℕ) : inhabited (sym α n) :=
⟨⟨multiset.repeat (default α) n, multiset.card_repeat _ _⟩⟩

instance inhabited_sym' [inhabited α] (n : ℕ) : inhabited (sym' α n) :=
⟨quotient.mk' (vector.repeat (default α) n)⟩

end inhabited

end sym
