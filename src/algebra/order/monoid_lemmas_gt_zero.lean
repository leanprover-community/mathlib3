/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.covariant_and_contravariant

/-!
# Multiplication by ·positive· elements is monotonic

Let `α` be a type with `<` and `0`.  We introduce the type `gt_zero α = {x : α // 0 < x}` of
positive elements of `α`.  We also introduce a local notation for the subtype `gt_zero α`:

*  the notation `α>0` to stands for `gt_zero α`.

If the type `α` also has a multiplication, then we also define the multiplications on the left and
on the right of an element of `α>0` and an element of `α`:

*  `sx : α>0 → α → α` is defined as `sx a b = a * b`, with `a` coerced to `α` by virtue of being in
  a subtype of `α`;
*  `dx : α>0 → α → α` is defined as `dx a b = b * a`, with `a` coerced to `α` by virtue of being in
  a subtype of `α`.

We combine this with (`contravariant_`) `covariant_class`es to assume that multiplication by
positive elements is (strictly) monotone on a `mul_zero_class`, `monoid_with_zero`,...
More specifically, we use extensively the following typeclasses:

* monotone left
* * `covariant_class α>0 α sx (≤)`, expressing that multiplication by positive elements on the left
    is monotone;
* * `covariant_class α>0 α sx (<)`, expressing that multiplication by positive elements on the left
    is strictly monotone;
* monotone right
* * `covariant_class α>0 α dx (≤)`, expressing that multiplication by positive elements on the right
    is monotone;
* * `covariant_class α>0 α dx (<)`, expressing that multiplication by positive elements on the right
    is strictly monotone.
* reverse monotone left
* * `contravariant_class α>0 α sx (≤)`, expressing that multiplication by positive elements on the
    left is reverse monotone;
* * `contravariant_class α>0 α sx (<)`, expressing that multiplication by positive elements on the
    left is strictly reverse monotone;
* reverse reverse monotone right
* * `contravariant_class α>0 α dx (≤)`, expressing that multiplication by positive elements on the
    right is reverse monotone;
* * `contravariant_class α>0 α dx (<)`, expressing that multiplication by positive elements on the
    right is strictly reverse monotone.

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

/--  The type of positive elements in a type that has a `0` and a `<`. -/
@[reducible]
def gt_zero (α : Type u) [has_zero α] [has_lt α] := {x : α // 0 < x}

/-  Notation for positive elements
https://
leanprover.zulipchat.com/#narrow/stream/113488-general/topic/notation.20for.20positive.20elements
-/
local notation `α>0` := gt_zero α

namespace gt_zero

/--  `sx` is the multiplication of an element of the subtype `α>0 = {x : α // 0 < x}` of positive
elements by an element of the type itself.  The element of the subtype appears on the left:
`sx a b = a * b`.

`dx` is the multiplication in the other order. -/
def sx [has_zero α] [has_lt α] [has_mul α] : α>0 → α → α :=
λ x y, x * y

/--  `dx` is the multiplication of an element of the subtype `α>0 = {x : α // 0 < x}` of positive
elements by an element of the type itself.  The element of the subtype appears on the right:
`dx a b = b * a`.

`sx` is the multiplication in the other order. -/
def dx [has_zero α] [has_lt α] [has_mul α] : α>0 → α → α :=
λ x y, y * x

section has_mul_zero_lt
variables [has_mul α] [has_zero α] [has_lt α]

lemma mul_lt_mul_left' [covariant_class α>0 α sx (<)]
  {a b c : α} (bc : b < c) (a0 : 0 < a) :
  a * b < a * c :=
let a₀ : α>0 := ⟨a, a0⟩ in show sx a₀ b < sx a₀ c, from covariant_class.elim a₀ bc

lemma mul_lt_mul_right' [covariant_class α>0 α dx (<)]
  {a b c : α} (bc : b < c) (a0 : 0 < a) :
  b * a < c * a :=
let a₀ : α>0 := ⟨a, a0⟩ in show dx a₀ b < dx a₀ c, by exact covariant_class.elim a₀ bc

-- proven with `a0 : 0 ≤ a` as `lt_of_mul_lt_mul_left''`
lemma lt_of_mul_lt_mul_left' [contravariant_class α>0 α sx (<)]
  {a b c : α} (bc : a * b < a * c) (a0 : 0 < a) :
  b < c :=
let a₀ : α>0 := ⟨a, a0⟩ in contravariant_class.elim a₀ (id bc : sx a₀ b < sx a₀ c)

-- proven with `a0 : 0 ≤ a` as `lt_of_mul_lt_mul_right''`
lemma lt_of_mul_lt_mul_right' [contravariant_class α>0 α dx (<)]
  {a b c : α} (bc : b * a < c * a) (a0 : 0 < a) :
  b < c :=
let a₀ : α>0 := ⟨a, a0⟩ in contravariant_class.elim a₀ (id bc : dx a₀ b < dx a₀ c)

@[simp]
lemma mul_lt_mul_iff_left [covariant_class α>0 α sx (<)] [contravariant_class α>0 α sx (<)]
  {a b c : α} (a0 : 0 < a) :
  a * b < a * c ↔ b < c :=
let a₀ : α>0 := ⟨a, a0⟩ in by apply rel_iff_cov α>0 α sx (<) a₀

@[simp]
lemma mul_lt_mul_iff_right
  [covariant_class α>0 α dx (<)] [contravariant_class α>0 α dx (<)]
  {a b c : α} (a0 : 0 < a) :
  b * a < c * a ↔ b < c :=
let a₀ : α>0 := ⟨a, a0⟩ in rel_iff_cov α>0 α dx (<) a₀

end has_mul_zero_lt

end gt_zero
