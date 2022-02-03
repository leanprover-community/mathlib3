/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.order.ring

/-!
# Multiplication by ·positive· elements is monotonic

Let `α` be a type with `<` and `0`.  We introduce notation for the subtype of positive elements of
`α`:

*  the notation `α⊹` stands for `{x : α // 0 < x}`.

If the type `α` also has a multiplication, then we also define the multiplications on the left and
on the right of an element of `α⊹` and an element of `α`:

*  `sx : α⊹ → α → α` is defined as `sx a b = a * b`, with `a` coerced to `α` by virtue of being in
  a subtype of `α`;
*  `dx : α⊹ → α → α` is defined as `dx a b = b * a`, with `a` coerced to `α` by virtue of being in
  a subtype of `α`.

We combine this with (`contravariant_`) `covariant_class`es to assume that multiplication by
positive elements is (strictly) monotone on a `mul_zero_class`, `monoid_with_zero`,...
More specifically, we use extensively the following typeclasses:

* monotone left
* * `covariant_class α⊹ α sx (≤)`, expressing that multiplication by positive elements on the left
    is monotone;
* * `covariant_class α⊹ α sx (<)`, expressing that multiplication by positive elements on the left
    is strictly monotone;
* monotone right
* * `covariant_class α⊹ α dx (≤)`, expressing that multiplication by positive elements on the right
    is monotone;
* * `covariant_class α⊹ α dx (<)`, expressing that multiplication by positive elements on the right
    is strictly monotone.
* reverse monotone left
* * `contravariant_class α⊹ α sx (≤)`, expressing that multiplication by positive elements on the
    left is reverse monotone;
* * `contravariant_class α⊹ α sx (<)`, expressing that multiplication by positive elements on the
    left is strictly reverse monotone;
* reverse monotone right
* * `contravariant_class α⊹ α dx (≤)`, expressing that multiplication by positive elements on the
    right is reverse monotone;
*  reverse strict monotone right
* * `contravariant_class α⊹ α dx (<)`, expressing that multiplication by positive elements on the
    right is strictly reverse monotone.

##  Formalization comments

We use `α⊹ = {x : α // 0 < x}` with a strict inequality since in most cases what happens with `0`
is clear.  This creates a few bumps in the first couple of proofs, where we have to split cases on
whether an element is `0` or not, but goes smoothly after that.  A further advantage is that we
only introduce notation for the positive elements and we do not need also the non-negative ones.
-/

/- I am changing the file `algebra/order/monoid_lemmas` incrementally, with the idea of
reproducing almost all of the proofs in `algebra/order/ring` with weaker assumptions. -/

namespace new

universe u
variable {α : Type u}

section pos_notation
variables [has_zero α] [has_lt α]

notation α`⊹`:1025 := {x : α // 0 < x}

end pos_notation

section cov_con
/--  `sx` is the multiplication of an element of the subtype `α⊹ = {x : α // 0 < x}` of positive
elements by an element of the type itself.  The element of the subtype appears on the left:
`sx a b = a * b`.

`dx` is the multiplication in the other order. -/
def sx {α} [has_mul α] [has_zero α] [has_lt α] : α⊹ → α → α :=
λ x y, x * y

/--  `dx` is the multiplication of an element of the subtype `α⊹ = {x : α // 0 < x}` of positive
elements by an element of the type itself.  The element of the subtype appears on the right:
`dx a b = b * a`.

`sx` is the multiplication in the other order. -/
def dx {α} [has_mul α] [has_zero α] [has_lt α] : α⊹ → α → α :=
λ x y, y * x

variables [mul_zero_class α] [partial_order α]
variables [covariant_class α⊹ α sx (≤)] {a b c : α}

lemma mul_le_mul_of_le_of_nonneg_left (ab : a ≤ b) (c0 : 0 ≤ c) : c * a ≤ c * b :=
begin
  by_cases cz : c = 0, { simp [cz] },
  let c₀ : α⊹ := ⟨c, c0.lt_of_ne (ne.symm cz)⟩,
  show sx c₀ a ≤ sx c₀ b, from covariant_class.elim c₀ ab
end

lemma mul_nonneg (a0 : 0 ≤ a) (b0 : 0 ≤ b) : 0 ≤ a * b :=
(mul_zero a).ge.trans (mul_le_mul_of_le_of_nonneg_left b0 a0)

end cov_con

section mul_zero_class
variables [mul_zero_class α]

section has_lt
variables [has_lt α]

@[simp]
lemma mul_lt_mul_iff_left [covariant_class α⊹ α sx (<)] [contravariant_class α⊹ α sx (<)]
  {a b c : α} (a0 : 0 < a) :
  a * b < a * c ↔ b < c :=
let a₀ : α⊹ := ⟨a, a0⟩ in by apply rel_iff_cov α⊹ α sx (<) a₀

@[simp]
lemma mul_lt_mul_iff_right
  [covariant_class α⊹ α dx (<)] [contravariant_class α⊹ α dx (<)]
  {a b c : α} (a0 : 0 < a) :
  b * a < c * a ↔ b < c :=
let a₀ : α⊹ := ⟨a, a0⟩ in rel_iff_cov α⊹ α dx (<) a₀

lemma mul_lt_mul_left' [covariant_class α⊹ α sx (<)]
  {a b c : α} (bc : b < c) (a0 : 0 < a) :
  a * b < a * c :=
let a₀ : α⊹ := ⟨a, a0⟩ in show sx a₀ b < sx a₀ c, from covariant_class.elim a₀ bc

-- proven with `a0 : 0 ≤ a` as `lt_of_mul_lt_mul_left''`
lemma lt_of_mul_lt_mul_left' [contravariant_class α⊹ α sx (<)]
  {a b c : α} (bc : a * b < a * c) (a0 : 0 < a) :
  b < c :=
let a₀ : α⊹ := ⟨a, a0⟩ in contravariant_class.elim a₀ (id bc : sx a₀ b < sx a₀ c)

lemma mul_lt_mul_right' [covariant_class α⊹ α dx (<)]
  {a b c : α} (bc : b < c) (a0 : 0 < a) :
  b * a < c * a :=
let a₀ : α⊹ := ⟨a, a0⟩ in show dx a₀ b < dx a₀ c, by exact covariant_class.elim a₀ bc

-- proven with `a0 : 0 ≤ a` as `lt_of_mul_lt_mul_right''`
lemma lt_of_mul_lt_mul_right' [contravariant_class α⊹ α dx (<)]
  {a b c : α} (bc : b * a < c * a) (a0 : 0 < a) :
  b < c :=
let a₀ : α⊹ := ⟨a, a0⟩ in contravariant_class.elim a₀ (id bc : dx a₀ b < dx a₀ c)

end has_lt

section partial_order
variables [partial_order α]

/- The prime on this lemma is present only on the multiplicative version.  The unprimed version
is taken by the analogous lemma for semiring, with an extra non-negativity assumption. -/
--@[to_additive add_le_add_left]
lemma mul_le_mul_left' [covariant_class α⊹ α sx (≤)] {a b c : α} (bc : b ≤ c) (a0 : 0 ≤ a) :
  a * b ≤ a * c :=
begin
  by_cases az : a = 0, { simp [az] },
  let a₀ : α⊹ := ⟨a, a0.lt_of_ne (ne.symm az)⟩,
  show sx a₀ b ≤ sx a₀ c, from covariant_class.elim a₀ bc
end

lemma le_of_mul_le_mul_left' [contravariant_class α⊹ α sx (≤)]
  {a b c : α} (a0 : 0 < a) (bc : a * b ≤ a * c) :
  b ≤ c :=
let a₀ : α⊹ := ⟨a, a0⟩ in contravariant_class.elim a₀ (id bc : sx a₀ b ≤ sx a₀ c)

/- The prime on this lemma is present only on the multiplicative version.  The unprimed version
is taken by the analogous lemma for semiring, with an extra non-negativity assumption. -/
lemma mul_le_mul_right' [covariant_class α⊹ α dx (≤)]
  {b c : α} (bc : b ≤ c) {a : α} (a0 : 0 ≤ a) :
  b * a ≤ c * a :=
begin
  by_cases ae0 : a = 0, { simp [ae0] },
  let a₀ : α⊹ := ⟨a, lt_of_le_not_le (a0) (λ h, ae0 (le_antisymm h a0))⟩,
  show dx a₀ b ≤ dx a₀ c, from covariant_class.elim a₀ bc
end

/-  The instance `covariant_class α⊹ α dx (≤)` follows from this one. -/
instance {α : Type u} [linear_ordered_semiring α] : covariant_class α⊹ α dx (≤) :=
{ elim := λ a b c bc, begin
    rcases eq_or_ne b c with rfl | hbc,
    { refl },
    { exact (ordered_semiring.mul_lt_mul_of_pos_right b c a.1 ((ne.le_iff_lt hbc).mp bc) a.2).le }
  end }

theorem mul_le_mul_right {α : Type u} [_inst_1 : linear_ordered_semiring α] {a b c : α} (c0 : 0 < c)
  (ab : a ≤ b) : a * c ≤ b * c :=
mul_le_mul_right' ab c0.le

lemma le_of_mul_le_mul_right' [contravariant_class α⊹ α dx (≤)]
  {a b c : α} (a0 : (<) 0 a) (bc : b * a ≤ c * a) :
  b ≤ c :=
let a₀ : α⊹ := ⟨a, a0⟩ in contravariant_class.elim a₀ (id bc : dx a₀ b ≤ dx a₀ c)

@[simp]
lemma mul_le_mul_iff_left [covariant_class α⊹ α sx (≤)] [contravariant_class α⊹ α sx (≤)]
  {a b c : α} (a0 : 0 < a) :
  a * b ≤ a * c ↔ b ≤ c :=
let a₀ : α⊹ := ⟨a, a0⟩ in by apply rel_iff_cov α⊹ α sx (≤) a₀

@[simp]
lemma mul_le_mul_iff_right [covariant_class α⊹ α dx (≤)] [contravariant_class α⊹ α dx (≤)]
  {a b c : α} (a0 : 0 < a) :
  b * a ≤ c * a ↔ b ≤ c :=
let a₀ : α⊹ := ⟨a, a0⟩ in rel_iff_cov α⊹ α dx (≤) a₀

lemma lt_of_mul_lt_mul_left'' [contravariant_class α⊹ α sx (<)]
  {a b c : α} (bc : a * b < a * c) (a0 : 0 ≤ a) :
  b < c :=
begin
  rcases eq_or_ne a 0 with rfl | a00,
  { exact (lt_irrefl (0 : α) (by simpa using bc)).elim },
  { exact lt_of_mul_lt_mul_left' bc ((ne.symm a00).le_iff_lt.mp a0) }
end

lemma lt_of_mul_lt_mul_right'' [contravariant_class α⊹ α dx (<)]
  {a b c : α} (bc : b * a < c * a) (a0 : 0 ≤ a) :
  b < c :=
begin
  rcases eq_or_ne a 0 with rfl | a00,
  { exact (lt_irrefl (0 : α) (by simpa using bc)).elim },
  { exact lt_of_mul_lt_mul_right' bc ((ne.symm a00).le_iff_lt.mp a0) }
end

end partial_order

end mul_zero_class

/-  This will likely go in the `algebra/order/ring` file. -/
section ordered_semiring
variables [ordered_semiring α] {a b c d : α}

instance ordered_semiring.to_covariant_class_left_lt :
  covariant_class α⊹ α sx (<) :=
{ elim := λ c a b ab, ordered_semiring.mul_lt_mul_of_pos_left a b c ab c.2 }

instance ordered_semiring.to_covariant_class_right_lt :
  covariant_class α⊹ α dx (<) :=
{ elim := λ c a b ab, ordered_semiring.mul_lt_mul_of_pos_right _ _ _ ab c.2 }

lemma cov_lt_to_le {α β : Type*} {μ : α → β → β} [partial_order β] [covariant_class α β μ (<)] :
  covariant_class α β μ (≤) :=
{ elim := λ c a b, covariant_le_of_covariant_lt α β μ covariant_class.elim _ }

end ordered_semiring

end new
