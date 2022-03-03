/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.covariant_and_contravariant
import algebra.group_with_zero.defs

/-!
# Multiplication by ·positive· elements is monotonic

Let `α` be a type with `<` and `0`.  We use the type `{x : α // 0 < x}` of positive elements of `α`
to prove results about monotonicity of multiplication.  We also introduce the local notation `α>0`
for the subtype `{x : α // 0 < x}`:

*  the notation `α>0` to stands for `{x : α // 0 < x}`.

If the type `α` also has a multiplication, then we combine this with (`contravariant_`)
`covariant_class`es to assume that multiplication by positive elements is (strictly) monotone on a
`mul_zero_class`, `monoid_with_zero`,...
More specifically, we use extensively the following typeclasses:

* monotone left
* * `covariant_class α>0 α (λ x y, x * y) (≤)`, abbreviated `pos_mul_mono α`,
    expressing that multiplication by positive elements on the left is monotone;
* * `covariant_class α>0 α (λ x y, x * y) (<)`, abbreviated `pos_mul_strict_mono α`,
    expressing that multiplication by positive elements on the left is strictly monotone;
* monotone right
* * `covariant_class α>0 α (λ x y, y * x) (≤)`, abbreviated `mul_pos_mono α`,
    expressing that multiplication by positive elements on the right is monotone;
* * `covariant_class α>0 α (λ x y, y * x) (<)`, abbreviated `mul_pos_strict_mono α`,
    expressing that multiplication by positive elements on the right is strictly monotone.
* reverse monotone left
* * `contravariant_class α>0 α (λ x y, x * y) (≤)`, abbreviated `pos_mul_mono_rev α`,
    expressing that multiplication by positive elements on the left is reverse monotone;
* * `contravariant_class α>0 α (λ x y, x * y) (<)`, abbreviated `pos_mul_reflect_lt α`,
    expressing that multiplication by positive elements on the left is strictly reverse monotone;
* reverse reverse monotone right
* * `contravariant_class α>0 α (λ x y, y * x) (≤)`, abbreviated `mul_pos_mono_rev α`,
    expressing that multiplication by positive elements on the right is reverse monotone;
* * `contravariant_class α>0 α (λ x y, y * x) (<)`, abbreviated `mul_pos_reflect_lt α`,
    expressing that multiplication by positive elements on the right is strictly reverse monotone.

##  Formalization comments

We use `α>0 = {x : α // 0 < x}` with a strict inequality since in most cases what happens with `0`
is clear.  This creates a few bumps in the first couple of proofs, where we have to split cases on
whether an element is `0` or not, but goes smoothly after that.  A further advantage is that we
only introduce notation for the positive elements and we do not need also the non-negative ones.
-/

/- I am changing the file `algebra/order/monoid_lemmas` incrementally, with the idea of
reproducing almost all of the proofs in `algebra/order/ring` with weaker assumptions. -/

universe u
variable {α : Type u}

/-  Notation for positive elements
https://
leanprover.zulipchat.com/#narrow/stream/113488-general/topic/notation.20for.20positive.20elements
-/
local notation `α>0` := {x : α // 0 < x}

namespace zero_lt

section abbreviations_strict_mono
variables (X : Type u) [has_mul X] [has_zero X] [has_lt X]

/--  `zero_lt.pos_mul_strict_mono α` is an abbreviation for
`covariant_class α>0 α (λ x y, x * y) (<)`,
expressing that multiplication by positive elements on the left is strictly monotone. -/
abbreviation pos_mul_strict_mono : Prop :=
covariant_class {x : X // 0 < x} X (λ x y, x * y) (<)

/--  `zero_lt.mul_pos_strict_mono α` is an abbreviation for
`covariant_class α>0 α (λ x y, y * x) (<)`,
expressing that multiplication by positive elements on the right is strictly monotone. -/
abbreviation mul_pos_strict_mono : Prop :=
covariant_class {x : X // 0 < x} X (λ x y, y * x) (<)

/--  `zero_lt.pos_mul_reflect_lt α` is an abbreviation for
`contravariant_class α>0 α (λ x y, x * y) (<)`,
expressing that multiplication by positive elements on the left is strictly reverse monotone. -/
abbreviation pos_mul_reflect_lt : Prop :=
contravariant_class {x : X // 0 < x} X (λ x y, x * y) (<)

/--  `zero_lt.mul_pos_reflect_lt α` is an abbreviation for
`contravariant_class α>0 α (λ x y, y * x) (<)`,
expressing that multiplication by positive elements on the right is strictly reverse monotone. -/
abbreviation mul_pos_reflect_lt : Prop :=
contravariant_class {x : X // 0 < x} X (λ x y, y * x) (<)

end abbreviations_strict_mono

section abbreviations_mono
variables (X : Type*) [has_mul X] [has_zero X] [preorder X]

/--  `zero_lt.pos_mul_mono α` is an abbreviation for
`covariant_class α>0 α (λ x y, x * y) (≤)`,
expressing that multiplication by positive elements on the left is monotone. -/
abbreviation pos_mul_mono : Prop :=
covariant_class {x : X // 0 < x} X (λ x y, x * y) (≤)

/--  `zero_lt.mul_pos_mono α` is an abbreviation for
`covariant_class α>0 α (λ x y, y * x) (≤)`,
expressing that multiplication by positive elements on the right is monotone. -/
abbreviation mul_pos_mono : Prop :=
covariant_class {x : X // 0 < x} X (λ x y, y * x) (≤)

/--  `zero_lt.pos_mul_mono_rev α` is an abbreviation for
`contravariant_class α>0 α (λ x y, x * y) (≤)`,
expressing that multiplication by positive elements on the left is reverse monotone. -/
abbreviation pos_mul_mono_rev : Prop :=
contravariant_class {x : X // 0 < x} X (λ x y, x * y) (≤)

/--  `zero_lt.mul_pos_mono_rev α` is an abbreviation for
`contravariant_class α>0 α (λ x y, y * x) (≤)`,
expressing that multiplication by positive elements on the right is reverse monotone. -/
abbreviation mul_pos_mono_rev : Prop :=
contravariant_class {x : X // 0 < x} X (λ x y, y * x) (≤)

end abbreviations_mono

section has_mul_zero_lt
variables [has_mul α] [has_zero α] [has_lt α]

lemma mul_lt_mul_left' [pos_mul_strict_mono α] {a b c : α} (bc : b < c) (a0 : 0 < a) :
  a * b < a * c :=
@covariant_class.elim α>0 α (λ x y, x * y) (<) _ ⟨a, a0⟩ _ _ bc

lemma mul_lt_mul_right' [mul_pos_strict_mono α]
  {a b c : α} (bc : b < c) (a0 : 0 < a) :
  b * a < c * a :=
@covariant_class.elim α>0 α (λ x y, y * x) (<) _ ⟨a, a0⟩ _ _ bc

-- proven with `a0 : 0 ≤ a` as `lt_of_mul_lt_mul_left''`
lemma lt_of_mul_lt_mul_left' [pos_mul_reflect_lt α]
  {a b c : α} (bc : a * b < a * c) (a0 : 0 < a) :
  b < c :=
@contravariant_class.elim α>0 α (λ x y, x * y) (<) _ ⟨a, a0⟩ _ _ bc

-- proven with `a0 : 0 ≤ a` as `lt_of_mul_lt_mul_right''`
lemma lt_of_mul_lt_mul_right' [mul_pos_reflect_lt α]
  {a b c : α} (bc : b * a < c * a) (a0 : 0 < a) :
  b < c :=
@contravariant_class.elim α>0 α (λ x y, y * x) (<) _ ⟨a, a0⟩ _ _ bc

@[simp]
lemma mul_lt_mul_iff_left [pos_mul_strict_mono α] [pos_mul_reflect_lt α]
  {a b c : α} (a0 : 0 < a) :
  a * b < a * c ↔ b < c :=
@rel_iff_cov α>0 α (λ x y, x * y) (<) _ _ ⟨a, a0⟩ _ _

@[simp]
lemma mul_lt_mul_iff_right [mul_pos_strict_mono α] [mul_pos_reflect_lt α]
  {a b c : α} (a0 : 0 < a) :
  b * a < c * a ↔ b < c :=
@rel_iff_cov α>0 α (λ x y, y * x) (<) _ _ ⟨a, a0⟩ _ _

end has_mul_zero_lt

section has_mul_zero_le
variables [has_mul α] [has_zero α] [preorder α]

lemma mul_le_mul_left' [pos_mul_mono α] {a b c : α} (bc : b ≤ c) (a0 : 0 < a) :
  a * b ≤ a * c :=
@covariant_class.elim α>0 α (λ x y, x * y) (≤) _ ⟨a, a0⟩ _ _ bc

lemma mul_le_mul_right' [mul_pos_mono α]
  {a b c : α} (bc : b ≤ c) (a0 : 0 < a) :
  b * a ≤ c * a :=
@covariant_class.elim α>0 α (λ x y, y * x) (≤) _ ⟨a, a0⟩ _ _ bc

lemma le_of_mul_le_mul_left' [pos_mul_mono_rev α]
  {a b c : α} (bc : a * b ≤ a * c) (a0 : 0 < a) :
  b ≤ c :=
@contravariant_class.elim α>0 α (λ x y, x * y) (≤) _ ⟨a, a0⟩ _ _ bc

lemma le_of_mul_le_mul_right' [mul_pos_mono_rev α]
  {a b c : α} (bc : b * a ≤ c * a) (a0 : 0 < a) :
  b ≤ c :=
@contravariant_class.elim α>0 α (λ x y, y * x) (≤) _ ⟨a, a0⟩ _ _ bc

@[simp]
lemma mul_le_mul_iff_left [pos_mul_mono α] [pos_mul_mono_rev α]
  {a b c : α} (a0 : 0 < a) :
  a * b ≤ a * c ↔ b ≤ c :=
@rel_iff_cov α>0 α (λ x y, x * y) (≤) _ _ ⟨a, a0⟩ _ _

@[simp]
lemma mul_le_mul_iff_right [mul_pos_mono α] [mul_pos_mono_rev α]
  {a b c : α} (a0 : 0 < a) :
  b * a ≤ c * a ↔ b ≤ c :=
@rel_iff_cov α>0 α (λ x y, y * x) (≤) _ _ ⟨a, a0⟩ _ _

end has_mul_zero_le

section mul_zero_class_partial_order
variables [mul_zero_class α] [partial_order α]

lemma lt_of_mul_lt_mul_left'' [pos_mul_reflect_lt α]
  {a b c : α} (bc : a * b < a * c) (a0 : 0 ≤ a) :
  b < c :=
begin
  by_cases a₀ : a = 0,
  { exact (lt_irrefl (0 : α) (by simpa only [a₀, zero_mul] using bc)).elim },
  { exact lt_of_mul_lt_mul_left' bc ((ne.symm a₀).le_iff_lt.mp a0) }
end

lemma lt_of_mul_lt_mul_right'' [mul_pos_reflect_lt α]
  {a b c : α} (bc : b * a < c * a) (a0 : 0 ≤ a) :
  b < c :=
begin
  by_cases a₀ : a = 0,
  { exact (lt_irrefl (0 : α) (by simpa only [a₀, mul_zero] using bc)).elim },
  { exact lt_of_mul_lt_mul_right' bc ((ne.symm a₀).le_iff_lt.mp a0) }
end

end mul_zero_class_partial_order
end zero_lt
