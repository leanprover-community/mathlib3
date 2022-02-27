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

/-- Take the image of a set of pi types on restriction to a subtype of inputs. -/
@[reducible]
def pi_restrict_image {α : Type*} {β : α → Type*} (s : set α) (g : set (Π i, β i)) :
  set (Π i : s, β i) := pi_restrict s '' g

/-- Take the pre-image of a set of pi types restricted to a subtype of inputs. -/
@[reducible]
def pi_restrict_preimage {α : Type*} {β : α → Type*} (s : set α) (g : set (Π i : s, β i)) :
  set (Π i : α, β i) := pi_restrict s ⁻¹' g

end set
