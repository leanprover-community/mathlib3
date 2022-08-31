/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.finset.lattice

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

--  please, golf my proof and my name!
@[to_additive] lemma eq_and_eq_of_le_of_le_of_mul_eq {A} [has_mul A] [linear_order A]
  [covariant_class A A (*) (≤)] [covariant_class A A (function.swap (*)) (<)]
  [contravariant_class A A (*) (≤)]
  {a b a0 b0 : A} (ha : a0 ≤ a) (hb : b0 ≤ b) (ab : a * b = a0 * b0) :
  a = a0 ∧ b = b0 :=
begin
  rcases trichotomous_of (<) a a0 with h | rfl | h,
  { exact (lt_irrefl _ (h.trans_le ha)).elim },
  { refine ⟨rfl, _⟩,
    rcases trichotomous_of (<) b b0 with h | rfl | h,
    { exact (lt_irrefl _ (h.trans_le hb)).elim },
    { refl },
    { exact le_antisymm (le_of_mul_le_mul_left' ab.le) ‹_› } },
  { exact (lt_irrefl _ ((mul_lt_mul_of_lt_of_le h hb).trans_le ab.le)).elim }
end

/--  This instance is asserting that `A` has an operation and a linear order and the operation
is "very monotone". -/
@[to_additive ] instance covariants.to_unique_prods {A} [has_mul A] [linear_order A]
  [covariant_class A A (*) (≤)] [covariant_class A A (function.swap (*)) (<)]
  [contravariant_class A A (*) (≤)] : unique_prods A :=
{ muls := λ A B hA hB, ⟨_, A.min'_mem ‹_›, _, B.min'_mem ‹_›, λ a b ha hb ab,
    eq_and_eq_of_le_of_le_of_mul_eq (finset.min'_le _ _ ‹_›) (finset.min'_le _ _ ‹_›) ‹_›⟩ }
.
/--  Here you can see several examples of Types that have `unique_sums/prods`. -/
example : unique_sums ℕ   := by apply_instance
example : unique_sums ℕ+  := by apply_instance
example : unique_sums ℤ   := by apply_instance
example : unique_prods ℕ+ := by apply_instance

/--  And also a Type that does not have `unique_prods`. -/
example : ¬ unique_prods ℕ :=
begin
  rintros ⟨h⟩,
  refine not_not.mpr (h (finset.singleton_nonempty 0) (finset.insert_nonempty 0 {1})) _,
  suffices : (∃ (x : ℕ), (x = 0 ∨ x = 1) ∧ ¬x = 0) ∧ ∃ (x : ℕ), (x = 0 ∨ x = 1) ∧ ¬x = 1,
  { simpa [unique_mul] },
  exact ⟨⟨1, by simp⟩, ⟨0, by simp⟩⟩,
end
