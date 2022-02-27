/-
Copyright (c) 2022 Rishikesh Vaishnav. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rishikesh Vaishnav
-/
import data.set

/-!
# Pi types over sets
Generalization of `set.restrict` to pi types.

## Main definitions
* `set.pi_restrict f s` : restrict the domain of `f` to the set `s`;
-/
namespace set

/-- Restrict domain of a pi type `f` to a set `s`. Same as `subtype.restrict` but this
takes the restricting set before the pi type. Generalization of `set.restrict` to pi types. -/
def pi_restrict {α : Type*} {β : α → Type*} (s : set α) (g : Π i, β i) :
  Π i : s, β i := λ (i : s), g i

end set
