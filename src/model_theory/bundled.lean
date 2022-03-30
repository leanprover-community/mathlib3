/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import model_theory.semantics
import category_theory.concrete_category.bundled
/-!
# Bundled First-Order Structures
This file bundles types together with their first-order structure.

## Main Definitions
* `first_order.language.equiv_setoid` is the isomorphism equivalence relation on bundled structures.

## TODO
* Define bundled models of a given theory.
* Define category structures on bundled structures and models.

-/

universes u v w

variables {L : first_order.language.{u v}}

@[protected] instance category_theory.bundled.Structure
  {L : first_order.language.{u v}} (M : category_theory.bundled.{w} L.Structure) :
  L.Structure M :=
M.str

namespace first_order
namespace language
open_locale first_order

/-- The equivalence relation on bundled `L.Structure`s indicating that they are isomorphic. -/
instance equiv_setoid : setoid (category_theory.bundled L.Structure) :=
{ r := λ M N, nonempty (M ≃[L] N),
  iseqv := ⟨λ M, ⟨equiv.refl L M⟩, λ M N, nonempty.map equiv.symm,
    λ M N P, nonempty.map2 (λ MN NP, NP.comp MN)⟩ }

end language
end first_order
