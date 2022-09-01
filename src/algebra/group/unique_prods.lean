/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.finset.lattice
import data.real.basic
import data.zmod.basic
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

namespace unique_mul
variables {G : Type*} [has_mul G] {A B : finset G} {a0 b0 : G}

@[to_additive]
lemma subsingleton (A B : finset G) (a0 b0 : G) (h : unique_mul A B a0 b0) :
  subsingleton { ab : G × G // ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 * ab.2 = a0 * b0 } :=
⟨λ ⟨⟨a, b⟩, ha, hb, ab⟩ ⟨⟨a', b'⟩, ha', hb', ab'⟩, subtype.ext $ prod.ext
  ((h ha hb ab).1.trans (h ha' hb' ab').1.symm) $ (h ha hb ab).2.trans (h ha' hb' ab').2.symm⟩

@[to_additive]
lemma exists_unique_iff (aA : a0 ∈ A) (bB : b0 ∈ B) :
  unique_mul A B a0 b0 ↔ ∃! ab ∈ A ×ˢ B, ab.1 * ab.2 = a0 * b0 :=
⟨λ _, ⟨(a0, b0), ⟨finset.mem_product.mpr ⟨aA, bB⟩, rfl, by simp⟩, by simpa⟩, λ h, begin
  rcases h with ⟨⟨a, b⟩, -, J⟩,
  refine λ x y xA yB H, _,
  replace J : ∀ {r s : G}, r ∈ A → s ∈ B → r * s = a0 * b0 → r = a ∧ s = b, by simpa using J,
  rcases J xA yB H with ⟨rfl, rfl⟩,
  rcases J aA bB rfl with ⟨rfl, rfl⟩,
  exact ⟨rfl, rfl⟩,
end⟩

@[to_additive]
lemma exists_exists_unique (aA : a0 ∈ A) (bB : b0 ∈ B) (u : unique_mul A B a0 b0) :
  ∃ g : G, ∃! ab ∈ A ×ˢ B, ab.1 * ab.2 = g :=
⟨a0 * b0, (exists_unique_iff aA bB).mp u⟩

@[to_additive]
lemma of_exists_unique {g : G} (h : ∃! ab ∈ A ×ˢ B, ab.1 * ab.2 = g) :
  ∃ a0 b0 : G, a0 ∈ A ∧ b0 ∈ B ∧ unique_mul A B a0 b0 :=
begin
  have h' := h,
  rcases h' with ⟨⟨a,b⟩, ⟨hab, rfl, -⟩, -⟩,
  cases finset.mem_product.mp hab with ha hb,
  exact ⟨a, b, ha, hb, (exists_unique_iff ha hb).mpr h⟩,
end

@[to_additive]
lemma of_exists_exists_unique (h : ∃ g : G, ∃! ab ∈ A ×ˢ B, ab.1 * ab.2 = g) :
  ∃ a0 b0 : G, a0 ∈ A ∧ b0 ∈ B ∧ unique_mul A B a0 b0 :=
of_exists_unique h.some_spec

end unique_mul

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

--  please, golf me and rename me!
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

/--  This instance asserts that if `A` has a multiplication, a linear order, and multiplication
is 'very monotone', then `A` also has `unique_prods`. -/
@[priority 100,  -- see Note [lower instance priority]
to_additive "This instance asserts that if `A` has an addition, a linear order, and addition
is 'very monotone', then `A` also has `unique_sums`."]
instance covariants.to_unique_prods {A} [has_mul A] [linear_order A]
  [covariant_class A A (*) (≤)] [covariant_class A A (function.swap (*)) (<)]
  [contravariant_class A A (*) (≤)] : unique_prods A :=
{ muls := λ A B hA hB, ⟨_, A.min'_mem ‹_›, _, B.min'_mem ‹_›, λ a b ha hb ab,
    eq_and_eq_of_le_of_le_of_mul_eq (finset.min'_le _ _ ‹_›) (finset.min'_le _ _ ‹_›) ‹_›⟩ }

/--  Here you can see several examples of Types that have `unique_sums/prods`. -/
example : unique_sums ℕ   := by apply_instance
example : unique_sums ℕ+  := by apply_instance
example : unique_sums ℤ   := by apply_instance
example : unique_sums ℚ   := by apply_instance
example : unique_sums ℝ   := by apply_instance
example : unique_prods ℕ+ := by apply_instance

/--  A Type that does not have `unique_prods`. -/
example : ¬ unique_prods ℕ :=
begin
  rintros ⟨h⟩,
  refine not_not.mpr (h (finset.singleton_nonempty 0) (finset.insert_nonempty 0 {1})) _,
  suffices : (∃ (x : ℕ), (x = 0 ∨ x = 1) ∧ ¬x = 0) ∧ ∃ (x : ℕ), (x = 0 ∨ x = 1) ∧ ¬x = 1,
  { simpa [unique_mul] },
  exact ⟨⟨1, by simp⟩, ⟨0, by simp⟩⟩,
end

/--  A Type that does not have `unique_sums`. -/
example (n : ℕ) (n2 : 2 ≤ n): ¬ unique_sums (zmod n) :=
begin
  haveI : fintype (zmod n) := @zmod.fintype n ⟨(zero_lt_two.trans_le n2).ne'⟩,
  haveI : nontrivial (zmod n) := char_p.nontrivial_of_char_ne_one (one_lt_two.trans_le n2).ne',
  rintros ⟨h⟩,
  refine not_not.mpr (h finset.univ_nonempty finset.univ_nonempty) _,
  suffices : ∀ (x y : zmod n), ∃ (x' y' : zmod n), x' + y' = x + y ∧ (x' = x → ¬y' = y),
  { simpa [unique_add] },
  exact λ x y, ⟨x - 1, y + 1, sub_add_add_cancel _ _ _, by simp⟩,
end
