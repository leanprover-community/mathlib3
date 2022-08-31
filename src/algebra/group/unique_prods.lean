/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.finset.prod

/-!
#  Unique products and related notions
-/

/--  Let `G` be a Type with multiplication, let `A B : finset G` be finite subsets and
let `a0 b0 : G` be two elements.  `unique_mul A B a0 b0` asserts `a0 * b0` can be written in at
most one way as a product of an element of `A` and an element of `B`. -/
@[to_additive "Let `G` be a Type with addition, let `A B : finset G` be finite subsets and
let `a0 b0 : G` be two elements.  `unique_add A B a0 b0` asserts `a0 * b0` can be written in at
most one way as a sum of an element from `A` and an element from `B`."]
def unique_mul {G} [has_mul G] (A B : finset G) (a0 b0 : G) : Prop :=
∀ ⦃a b⦄, a ∈ A → b ∈ B → a * b = a0 * b0 → a = a0 ∧ b = b0

/--  Let `G` be a Type with addition.  `unique_sums G` asserts that any two non-empty
finite subsets of `A` have the `unique_add` property, with respect to some element of their
sum `A + B`. -/
class unique_sums (G) [has_add G] : Prop :=
( adds : ∀ {A B : finset G} (hA : A.nonempty) (hB : B.nonempty),
  ∃ (a0 ∈ A) (b0 ∈ B), unique_add A B a0 b0)

/--  Let `G` be a Type with multiplication.  `unique_prods G` asserts that any two non-empty
finite subsets of `G` have the `unique_mul` property, with respect to some element of their
product `A * B`. -/
class unique_prods (G) [has_mul G] : Prop :=
( muls : ∀ {A B : finset G} (hA : A.nonempty) (hB : B.nonempty),
  ∃ (a0 ∈ A) (b0 ∈ B), unique_mul A B a0 b0 )

attribute [to_additive] unique_prods

namespace multiplicative

instance {M} [has_add M] [unique_sums M] : unique_prods (multiplicative M) :=
{ muls := λ A B hA hB, let A' : finset M := A in have hA': A'.nonempty := hA, by
    { obtain ⟨a0, hA0, b0, hB0, J⟩ := unique_sums.adds hA' hB,
      exact ⟨of_add a0, hA0, of_add b0, hB0, λ a b aA bB H, J aA bB H⟩ } }

end multiplicative
