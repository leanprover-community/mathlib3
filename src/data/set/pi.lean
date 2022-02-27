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
def pi_restrict {α : Type*} {β : α → Type*} (mv : set α) := λ (g : Π i, β i) (i : mv), g i

@[reducible]
def pi_restrict_image {α : Type*} {β : α → Type*} (mv : set α) :=
  λ (g : set (Π i, β i)), pi_restrict mv '' g

@[reducible]
def pi_restrict_preimage {α : Type*} {β : α → Type*} (mv : set α) :=
  λ (g : set (Π i : mv, β i)), pi_restrict mv ⁻¹' g

end set
