/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.abelian.basic

/-!
# Pseudoabelian categories

In this file, we define the notion of pseudoabelian category (also known as Karoubian categories).

## Main constructions and definitions

- `is_pseudoabelian C` expresses that `C` is pseudoabelian, i.e. all idempotents endomorphisms
in `C` have a kernel.
- `is_pseudoabelian_of_abelian` expresses that abelian categories are pseudoabelian.

## References
* [Stacks: Karoubian categories] https://stacks.math.columbia.edu/tag/09SF

-/

open category_theory.category
open category_theory.limits

namespace category_theory

variables (C : Type*) [category C] [preadditive C]

/-- A preadditive category is pseudoabelian iff all idempotent endomorphisms have a kernel. -/
class is_pseudoabelian : Prop :=
(has_kernel_of_idem : ∀ (X : C) (p : X ⟶ X), p ≫ p = p → has_kernel p)

/-- An abelian category is pseudoabelian. -/
@[priority 100]
instance is_pseudoabelian_of_abelian (D : Type*) [category D] [abelian D] :
  is_pseudoabelian D :=
{ has_kernel_of_idem := λ X p hp, infer_instance }

end category_theory
