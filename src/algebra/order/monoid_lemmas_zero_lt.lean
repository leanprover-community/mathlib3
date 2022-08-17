/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Yuyang Zhao
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

Some lemmas for `partial_order` also have a variant for `preorder`, where the `preorder` version has
stronger hypotheses.  In this case we put the `preorder` lemma in the `preorder` namespace.
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
variables (X : Type*) [has_mul X] [has_zero X] [has_lt X] [has_le X]

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

variables {a b c d : α}

section has_mul_zero
variables [has_mul α] [has_zero α]

section has_lt
variables [has_lt α]

lemma mul_lt_mul_left [pos_mul_strict_mono α]
  (a0 : 0 < a) (bc : b < c) :
  a * b < a * c :=
@covariant_class.elim α>0 α (λ x y, x * y) (<) _ ⟨a, a0⟩ _ _ bc

lemma mul_lt_mul_right [mul_pos_strict_mono α]
  (a0 : 0 < a) (bc : b < c) :
  b * a < c * a :=
@covariant_class.elim α>0 α (λ x y, y * x) (<) _ ⟨a, a0⟩ _ _ bc

-- proven with `a0 : 0 ≤ a` as `lt_of_mul_lt_mul_left`
lemma lt_of_mul_lt_mul_left' [pos_mul_reflect_lt α]
  (a0 : 0 < a) (bc : a * b < a * c) :
  b < c :=
@contravariant_class.elim α>0 α (λ x y, x * y) (<) _ ⟨a, a0⟩ _ _ bc

-- proven with `a0 : 0 ≤ a` as `lt_of_mul_lt_mul_right`
lemma lt_of_mul_lt_mul_right' [mul_pos_reflect_lt α]
  (a0 : 0 < a) (bc : b * a < c * a) :
  b < c :=
@contravariant_class.elim α>0 α (λ x y, y * x) (<) _ ⟨a, a0⟩ _ _ bc

@[simp]
lemma mul_lt_mul_iff_left [pos_mul_strict_mono α] [pos_mul_reflect_lt α]
  (a0 : 0 < a) :
  a * b < a * c ↔ b < c :=
@rel_iff_cov α>0 α (λ x y, x * y) (<) _ _ ⟨a, a0⟩ _ _

@[simp]
lemma mul_lt_mul_iff_right [mul_pos_strict_mono α] [mul_pos_reflect_lt α]
  (a0 : 0 < a) :
  b * a < c * a ↔ b < c :=
@rel_iff_cov α>0 α (λ x y, y * x) (<) _ _ ⟨a, a0⟩ _ _

end has_lt

section has_lt_le
variables [has_lt α] [has_le α]

-- proven with `a0 : 0 ≤ a` as `mul_le_mul_left`
lemma mul_le_mul_left' [pos_mul_mono α]
  (a0 : 0 < a) (bc : b ≤ c) :
  a * b ≤ a * c :=
@covariant_class.elim α>0 α (λ x y, x * y) (≤) _ ⟨a, a0⟩ _ _ bc

-- proven with `a0 : 0 ≤ a` as `mul_le_mul_right`
lemma mul_le_mul_right' [mul_pos_mono α]
  (a0 : 0 < a) (bc : b ≤ c) :
  b * a ≤ c * a :=
@covariant_class.elim α>0 α (λ x y, y * x) (≤) _ ⟨a, a0⟩ _ _ bc

lemma le_of_mul_le_mul_left' [pos_mul_mono_rev α]
  (a0 : 0 < a) (bc : a * b ≤ a * c) :
  b ≤ c :=
@contravariant_class.elim α>0 α (λ x y, x * y) (≤) _ ⟨a, a0⟩ _ _ bc

lemma le_of_mul_le_mul_right' [mul_pos_mono_rev α]
  (a0 : 0 < a) (bc : b * a ≤ c * a) :
  b ≤ c :=
@contravariant_class.elim α>0 α (λ x y, y * x) (≤) _ ⟨a, a0⟩ _ _ bc

@[simp]
lemma mul_le_mul_iff_left [pos_mul_mono α] [pos_mul_mono_rev α]
  (a0 : 0 < a) :
  a * b ≤ a * c ↔ b ≤ c :=
@rel_iff_cov α>0 α (λ x y, x * y) (≤) _ _ ⟨a, a0⟩ _ _

@[simp]
lemma mul_le_mul_iff_right [mul_pos_mono α] [mul_pos_mono_rev α]
  (a0 : 0 < a) :
  b * a ≤ c * a ↔ b ≤ c :=
@rel_iff_cov α>0 α (λ x y, y * x) (≤) _ _ ⟨a, a0⟩ _ _

end has_lt_le

section preorder
variables [preorder α]

-- proven with `a0 : 0 ≤ a` `d0 : 0 ≤ d` as `mul_le_mul_of_le_of_le`
lemma preorder.mul_le_mul_of_le_of_le [pos_mul_mono α] [mul_pos_mono α]
  (a0 : 0 < a) (d0 : 0 < d) (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
(mul_le_mul_left' a0 h₂).trans (mul_le_mul_right' d0 h₁)

-- proven with `b0 : 0 ≤ b` `c0 : 0 ≤ c` as `mul_le_mul_of_le_of_le'`
lemma preorder.mul_le_mul_of_le_of_le' [pos_mul_mono α] [mul_pos_mono α]
  (b0 : 0 < b) (c0 : 0 < c) (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
(mul_le_mul_right' c0 h₁).trans (mul_le_mul_left' b0 h₂)

-- proven with `d0 : 0 ≤ d` as `mul_lt_mul_of_le_of_lt`
lemma preorder.mul_lt_mul_of_le_of_lt [pos_mul_strict_mono α] [mul_pos_mono α]
  (a0 : 0 < a) (d0 : 0 < d) (h₁ : a ≤ b) (h₂ : c < d) : a * c < b * d :=
(mul_lt_mul_left a0 h₂).trans_le (mul_le_mul_right' d0 h₁)

-- proven with `c0 : 0 ≤ c` as `mul_lt_mul_of_le_of_lt'`
lemma preorder.mul_lt_mul_of_le_of_lt' [pos_mul_strict_mono α] [mul_pos_mono α]
  (b0 : 0 < b) (c0 : 0 < c) (h₁ : a ≤ b) (h₂ : c < d) : a * c < b * d :=
(mul_le_mul_right' c0 h₁).trans_lt (mul_lt_mul_left b0 h₂)

-- proven with `a0 : 0 ≤ a` as `mul_lt_mul_of_lt_of_le`
lemma preorder.mul_lt_mul_of_lt_of_le [pos_mul_mono α] [mul_pos_strict_mono α]
  (a0 : 0 < a) (d0 : 0 < d) (h₁ : a < b) (h₂ : c ≤ d) : a * c < b * d :=
(mul_le_mul_left' a0 h₂).trans_lt (mul_lt_mul_right d0 h₁)

-- proven with `b0 : 0 ≤ b` as `mul_lt_mul_of_lt_of_le'`
lemma preorder.mul_lt_mul_of_lt_of_le' [pos_mul_mono α] [mul_pos_strict_mono α]
  (b0 : 0 < b) (c0 : 0 < c) (h₁ : a < b) (h₂ : c ≤ d) : a * c < b * d :=
(mul_lt_mul_right c0 h₁).trans_le (mul_le_mul_left' b0 h₂)

/--  See `mul_lt_mul_of_le_of_lt`, `mul_lt_mul_of_le_of_lt'`, `mul_lt_mul_of_lt_of_le`, and
`mul_lt_mul_of_lt_of_le'` for `partial_order` version with weaker assumptions. -/
lemma mul_lt_mul_of_lt_of_lt [pos_mul_strict_mono α] [mul_pos_strict_mono α]
  (a0 : 0 < a) (d0 : 0 < d) (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
(mul_lt_mul_left a0 h₂).trans (mul_lt_mul_right d0 h₁)

/--  See `mul_lt_mul_of_le_of_lt`, `mul_lt_mul_of_le_of_lt'`, `mul_lt_mul_of_lt_of_le`, and
`mul_lt_mul_of_lt_of_le'` for `partial_order` version with weaker assumptions. -/
lemma mul_lt_mul_of_lt_of_lt' [pos_mul_strict_mono α] [mul_pos_strict_mono α]
  (b0 : 0 < b) (c0 : 0 < c) (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
(mul_lt_mul_right c0 h₁).trans (mul_lt_mul_left b0 h₂)

-- proven with `a0 : 0 ≤ a` as `mul_le_of_mul_le_left`
lemma preorder.mul_le_of_mul_le_left [pos_mul_mono α]
  (a0 : 0 < a) (h : a * b ≤ c) (hle : d ≤ b) :
  a * d ≤ c :=
(mul_le_mul_left' a0 hle).trans h

lemma mul_lt_of_mul_lt_left [pos_mul_mono α]
  (a0 : 0 < a) (h : a * b < c) (hle : d ≤ b) :
  a * d < c :=
(mul_le_mul_left' a0 hle).trans_lt h

-- proven with `b0 : 0 ≤ b` as `le_mul_of_le_mul_left`
lemma preorder.le_mul_of_le_mul_left [pos_mul_mono α]
  (b0 : 0 < b) (h : a ≤ b * c) (hle : c ≤ d) :
  a ≤ b * d :=
h.trans (mul_le_mul_left' b0 hle)

lemma lt_mul_of_lt_mul_left [pos_mul_mono α]
  (b0 : 0 < b) (h : a < b * c) (hle : c ≤ d) :
  a < b * d :=
h.trans_le (mul_le_mul_left' b0 hle)

-- proven with `b0 : 0 ≤ b` as `mul_le_of_mul_le_right`
lemma preorder.mul_le_of_mul_le_right [mul_pos_mono α]
  (b0 : 0 < b) (h : a * b ≤ c) (hle : d ≤ a) :
  d * b ≤ c :=
(mul_le_mul_right' b0 hle).trans h

lemma mul_lt_of_mul_lt_right [mul_pos_mono α]
  (b0 : 0 < b) (h : a * b < c) (hle : d ≤ a) :
  d * b < c :=
(mul_le_mul_right' b0 hle).trans_lt h

-- proven with `c0 : 0 ≤ c` as `le_mul_of_le_mul_right`
lemma preorder.le_mul_of_le_mul_right [mul_pos_mono α]
  (c0 : 0 < c) (h : a ≤ b * c) (hle : b ≤ d) :
  a ≤ d * c :=
h.trans (mul_le_mul_right' c0 hle)

lemma lt_mul_of_lt_mul_right [mul_pos_mono α]
  (c0 : 0 < c) (h : a < b * c) (hle : b ≤ d) :
  a < d * c :=
h.trans_le (mul_le_mul_right' c0 hle)

end preorder

section partial_order
variables [partial_order α]

@[priority 100] -- see Note [lower instance priority]
instance pos_mul_strict_mono.to_pos_mul_mono [pos_mul_strict_mono α] : pos_mul_mono α :=
⟨λ x a b h, h.eq_or_lt.elim (λ h', h' ▸ le_rfl) (λ h', (mul_lt_mul_left x.prop h').le)⟩

@[priority 100] -- see Note [lower instance priority]
instance mul_pos_strict_mono.to_mul_pos_mono [mul_pos_strict_mono α] : mul_pos_mono α :=
⟨λ x a b h, h.eq_or_lt.elim (λ h', h' ▸ le_rfl) (λ h', (mul_lt_mul_right x.prop h').le)⟩

@[priority 100] -- see Note [lower instance priority]
instance pos_mul_mono_rev.to_pos_mul_reflect_lt [pos_mul_mono_rev α] : pos_mul_reflect_lt α :=
⟨λ x a b h, lt_of_le_of_ne (le_of_mul_le_mul_left' x.prop h.le) (λ h', by simpa [h'] using h)⟩

@[priority 100] -- see Note [lower instance priority]
instance mul_pos_mono_rev.to_mul_pos_reflect_lt [mul_pos_mono_rev α] : mul_pos_reflect_lt α :=
⟨λ x a b h, lt_of_le_of_ne (le_of_mul_le_mul_right' x.prop h.le) (λ h', by simpa [h'] using h)⟩

end partial_order

section linear_order
variables [linear_order α]

@[priority 100] -- see Note [lower instance priority]
instance pos_mul_strict_mono.to_pos_mul_mono_rev [pos_mul_strict_mono α] : pos_mul_mono_rev α :=
⟨λ x a b h, le_of_not_lt $ λ h', h.not_lt (mul_lt_mul_left x.prop h')⟩

@[priority 100] -- see Note [lower instance priority]
instance mul_pos_strict_mono.to_mul_pos_mono_rev [mul_pos_strict_mono α] : mul_pos_mono_rev α :=
⟨λ x a b h, le_of_not_lt $ λ h', h.not_lt (mul_lt_mul_right x.prop h')⟩

lemma pos_mul_mono_rev.to_pos_mul_strict_mono [pos_mul_mono_rev α] : pos_mul_strict_mono α :=
⟨λ x a b h, lt_of_not_le $ λ h', h.not_le (le_of_mul_le_mul_left' x.prop h')⟩

lemma mul_pos_mono_rev.to_mul_pos_strict_mono [mul_pos_mono_rev α] : mul_pos_strict_mono α :=
⟨λ x a b h, lt_of_not_le $ λ h', h.not_le (le_of_mul_le_mul_right' x.prop h')⟩

lemma pos_mul_strict_mono_iff_pos_mul_mono_rev : pos_mul_strict_mono α ↔ pos_mul_mono_rev α :=
⟨@zero_lt.pos_mul_strict_mono.to_pos_mul_mono_rev _ _ _ _,
         @pos_mul_mono_rev.to_pos_mul_strict_mono _ _ _ _⟩

lemma mul_pos_strict_mono_iff_mul_pos_mono_rev : mul_pos_strict_mono α ↔ mul_pos_mono_rev α :=
⟨@zero_lt.mul_pos_strict_mono.to_mul_pos_mono_rev _ _ _ _,
         @mul_pos_mono_rev.to_mul_pos_strict_mono _ _ _ _⟩

lemma pos_mul_reflect_lt.to_pos_mul_mono [pos_mul_reflect_lt α] : pos_mul_mono α :=
⟨λ x a b h, le_of_not_lt $ λ h', h.not_lt (lt_of_mul_lt_mul_left' x.prop h')⟩

lemma mul_pos_reflect_lt.to_mul_pos_mono [mul_pos_reflect_lt α] : mul_pos_mono α :=
⟨λ x a b h, le_of_not_lt $ λ h', h.not_lt (lt_of_mul_lt_mul_right' x.prop h')⟩

lemma pos_mul_mono.to_pos_mul_reflect_lt [pos_mul_mono α] : pos_mul_reflect_lt α :=
⟨λ x a b h, lt_of_not_le $ λ h', h.not_le (mul_le_mul_left' x.prop h')⟩

lemma mul_pos_mono.to_mul_pos_reflect_lt [mul_pos_mono α] : mul_pos_reflect_lt α :=
⟨λ x a b h, lt_of_not_le $ λ h', h.not_le (mul_le_mul_right' x.prop h')⟩

lemma pos_mul_mono_iff_pos_mul_reflect_lt : pos_mul_mono α ↔ pos_mul_reflect_lt α :=
⟨@pos_mul_mono.to_pos_mul_reflect_lt _ _ _ _, @pos_mul_reflect_lt.to_pos_mul_mono _ _ _ _⟩

lemma mul_pos_mono_iff_mul_pos_reflect_lt : mul_pos_mono α ↔ mul_pos_reflect_lt α :=
⟨@mul_pos_mono.to_mul_pos_reflect_lt _ _ _ _, @mul_pos_reflect_lt.to_mul_pos_mono _ _ _ _⟩

end linear_order

end has_mul_zero

section mul_zero_class
variables [mul_zero_class α]

section preorder
variables [preorder α]

/-- Assumes left covariance. -/
lemma left.mul_pos [pos_mul_strict_mono α]
  (ha : 0 < a) (hb : 0 < b) :
  0 < a * b :=
have h : a * 0 < a * b, from mul_lt_mul_left ha hb,
by rwa [mul_zero] at h

alias left.mul_pos ← mul_pos

lemma mul_neg_of_pos_of_neg [pos_mul_strict_mono α]
  (ha : 0 < a) (hb : b < 0) :
  a * b < 0 :=
have h : a * b < a * 0, from mul_lt_mul_left ha hb,
by rwa [mul_zero] at h

/-- Assumes right covariance. -/
lemma right.mul_pos [mul_pos_strict_mono α]
  (ha : 0 < a) (hb : 0 < b) :
  0 < a * b :=
have h : 0 * b < a * b, from mul_lt_mul_right hb ha,
by rwa [zero_mul] at h

lemma mul_neg_of_neg_of_pos [mul_pos_strict_mono α]
  (ha : a < 0) (hb : 0 < b) :
  a * b < 0 :=
have h : a * b < 0 * b, from mul_lt_mul_right hb ha,
by rwa [zero_mul] at h

end preorder

section partial_order
variables [partial_order α]

lemma mul_le_mul_left [pos_mul_mono α]
  (a0 : 0 ≤ a) (bc : b ≤ c) :
  a * b ≤ a * c :=
a0.lt_or_eq.elim (λ h, mul_le_mul_left' h bc) (λ h, by simp only [← h, zero_mul])

lemma mul_le_mul_right [mul_pos_mono α]
  (a0 : 0 ≤ a) (bc : b ≤ c) :
  b * a ≤ c * a :=
a0.lt_or_eq.elim (λ h, mul_le_mul_right' h bc) (λ h, by simp only [← h, mul_zero])

/-- Assumes left covariance. -/
lemma left.mul_nonneg [pos_mul_mono α]
  (ha : 0 ≤ a) (hb : 0 ≤ b) :
  0 ≤ a * b :=
have h : a * 0 ≤ a * b, from mul_le_mul_left ha hb,
by rwa [mul_zero] at h

alias left.mul_nonneg ← mul_nonneg

lemma mul_nonpos_of_nonneg_of_nonpos [pos_mul_mono α]
  (ha : 0 ≤ a) (hb : b ≤ 0) :
  a * b ≤ 0 :=
have h : a * b ≤ a * 0, from mul_le_mul_left ha hb,
by rwa [mul_zero] at h

/-- Assumes right covariance. -/
lemma right.mul_nonneg [mul_pos_mono α]
  (ha : 0 ≤ a) (hb : 0 ≤ b) :
  0 ≤ a * b :=
have h : 0 * b ≤ a * b, from mul_le_mul_right hb ha,
by rwa [zero_mul] at h

lemma mul_nonpos_of_nonpos_of_nonneg [mul_pos_mono α]
  (ha : a ≤ 0) (hb : 0 ≤ b) :
  a * b ≤ 0 :=
have h : a * b ≤ 0 * b, from mul_le_mul_right hb ha,
by rwa [zero_mul] at h

lemma lt_of_mul_lt_mul_left [pos_mul_reflect_lt α]
  (a0 : 0 ≤ a) (bc : a * b < a * c) :
  b < c :=
begin
  by_cases a₀ : a = 0,
  { exact (lt_irrefl (0 : α) (by simpa only [a₀, zero_mul] using bc)).elim },
  { exact lt_of_mul_lt_mul_left' ((ne.symm a₀).le_iff_lt.mp a0) bc }
end

lemma pos_of_mul_pos_right [pos_mul_reflect_lt α] (a0 : 0 ≤ a) (h : 0 < a * b) :
  0 < b :=
lt_of_mul_lt_mul_left a0 ((mul_zero a).symm ▸ h : a * 0 < a * b)

lemma lt_of_mul_lt_mul_right [mul_pos_reflect_lt α]
  (a0 : 0 ≤ a) (bc : b * a < c * a) :
  b < c :=
begin
  by_cases a₀ : a = 0,
  { exact (lt_irrefl (0 : α) (by simpa only [a₀, mul_zero] using bc)).elim },
  { exact lt_of_mul_lt_mul_right' ((ne.symm a₀).le_iff_lt.mp a0) bc }
end

lemma pos_of_mul_pos_left [mul_pos_reflect_lt α] (b0 : 0 ≤ b) (h : 0 < a * b) :
  0 < a :=
lt_of_mul_lt_mul_right b0 ((zero_mul b).symm ▸ h : 0 * b < a * b)

lemma pos_iff_pos_of_mul_pos [pos_mul_reflect_lt α] [mul_pos_reflect_lt α] (hab : 0 < a * b) :
  0 < a ↔ 0 < b :=
⟨λ h, pos_of_mul_pos_right h.le hab, λ h, pos_of_mul_pos_left h.le hab⟩

lemma mul_le_mul_of_le_of_le [pos_mul_mono α] [mul_pos_mono α]
  (a0 : 0 ≤ a) (d0 : 0 ≤ d) (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
(mul_le_mul_left a0 h₂).trans $ mul_le_mul_right d0 h₁

lemma mul_le_mul_of_le_of_le' [pos_mul_mono α] [mul_pos_mono α]
  (b0 : 0 ≤ b) (c0 : 0 ≤ c) (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
(mul_le_mul_right c0 h₁).trans $ mul_le_mul_left b0 h₂

lemma mul_lt_mul_of_le_of_lt [pos_mul_strict_mono α] [mul_pos_mono α]
  (a0 : 0 < a) (d0 : 0 ≤ d) (h₁ : a ≤ b) (h₂ : c < d) : a * c < b * d :=
(mul_lt_mul_left a0 h₂).trans_le (mul_le_mul_right d0 h₁)

lemma mul_lt_mul_of_le_of_lt' [pos_mul_strict_mono α] [mul_pos_mono α]
  (b0 : 0 < b) (c0 : 0 ≤ c) (h₁ : a ≤ b) (h₂ : c < d) : a * c < b * d :=
(mul_le_mul_right c0 h₁).trans_lt (mul_lt_mul_left b0 h₂)

lemma mul_lt_mul_of_lt_of_le [pos_mul_mono α] [mul_pos_strict_mono α]
  (a0 : 0 ≤ a) (d0 : 0 < d) (h₁ : a < b) (h₂ : c ≤ d) : a * c < b * d :=
(mul_le_mul_left a0 h₂).trans_lt (mul_lt_mul_right d0 h₁)

lemma mul_lt_mul_of_lt_of_le' [pos_mul_mono α] [mul_pos_strict_mono α]
  (b0 : 0 ≤ b) (c0 : 0 < c) (h₁ : a < b) (h₂ : c ≤ d) : a * c < b * d :=
(mul_lt_mul_right c0 h₁).trans_le (mul_le_mul_left b0 h₂)

lemma mul_le_of_mul_le_left [pos_mul_mono α]
  (a0 : 0 ≤ a) (h : a * b ≤ c) (hle : d ≤ b) :
  a * d ≤ c :=
(mul_le_mul_left a0 hle).trans h

lemma le_mul_of_le_mul_left [pos_mul_mono α]
  (b0 : 0 ≤ b) (h : a ≤ b * c) (hle : c ≤ d) :
  a ≤ b * d :=
h.trans (mul_le_mul_left b0 hle)

lemma mul_le_of_mul_le_right [mul_pos_mono α]
  (b0 : 0 ≤ b) (h : a * b ≤ c) (hle : d ≤ a) :
  d * b ≤ c :=
(mul_le_mul_right b0 hle).trans h

lemma le_mul_of_le_mul_right [mul_pos_mono α]
  (c0 : 0 ≤ c) (h : a ≤ b * c) (hle : b ≤ d) :
  a ≤ d * c :=
h.trans (mul_le_mul_right c0 hle)

lemma mul_left_cancel_iff [pos_mul_mono_rev α]
  (a0 : 0 < a) :
  a * b = a * c ↔ b = c :=
⟨λ h, (le_of_mul_le_mul_left' a0 h.le).antisymm (le_of_mul_le_mul_left' a0 h.ge), congr_arg _⟩

lemma mul_right_cancel_iff [mul_pos_mono_rev α]
  (b0 : 0 < b) :
  a * b = c * b ↔ a = c :=
⟨λ h, (le_of_mul_le_mul_right' b0 h.le).antisymm (le_of_mul_le_mul_right' b0 h.ge), congr_arg _⟩

lemma mul_eq_mul_iff_eq_and_eq [pos_mul_strict_mono α] [mul_pos_strict_mono α]
  [pos_mul_mono_rev α] [mul_pos_mono_rev α]
  (a0 : 0 < a) (d0 : 0 < d) (hac : a ≤ b) (hbd : c ≤ d) :
  a * c = b * d ↔ a = b ∧ c = d :=
begin
  refine ⟨λ h, _, λ h, congr_arg2 (*) h.1 h.2⟩,
  rcases hac.eq_or_lt with rfl | hac,
  { exact ⟨rfl, (mul_left_cancel_iff a0).mp h⟩ },
  rcases eq_or_lt_of_le hbd with rfl | hbd,
  { exact ⟨(mul_right_cancel_iff d0).mp h, rfl⟩ },
  exact ((mul_lt_mul_of_lt_of_lt a0 d0 hac hbd).ne h).elim,
end

lemma mul_eq_mul_iff_eq_and_eq' [pos_mul_strict_mono α] [mul_pos_strict_mono α]
  [pos_mul_mono_rev α] [mul_pos_mono_rev α]
  (b0 : 0 < b) (c0 : 0 < c) (hac : a ≤ b) (hbd : c ≤ d) :
  a * c = b * d ↔ a = b ∧ c = d :=
begin
  refine ⟨λ h, _, λ h, congr_arg2 (*) h.1 h.2⟩,
  rcases hac.eq_or_lt with rfl | hac,
  { exact ⟨rfl, (mul_left_cancel_iff b0).mp h⟩ },
  rcases eq_or_lt_of_le hbd with rfl | hbd,
  { exact ⟨(mul_right_cancel_iff c0).mp h, rfl⟩ },
  exact ((mul_lt_mul_of_lt_of_lt' b0 c0 hac hbd).ne h).elim,
end

end partial_order

section linear_order
variables [linear_order α]

lemma pos_and_pos_or_neg_and_neg_of_mul_pos [pos_mul_mono α] [mul_pos_mono α]
  (hab : 0 < a * b) :
  (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0) :=
begin
  rcases lt_trichotomy 0 a with ha | rfl | ha,
  { refine or.inl ⟨ha, lt_imp_lt_of_le_imp_le (λ hb, _) hab⟩,
    exact mul_nonpos_of_nonneg_of_nonpos ha.le hb },
  { rw [zero_mul] at hab, exact hab.false.elim },
  { refine or.inr ⟨ha, lt_imp_lt_of_le_imp_le (λ hb, _) hab⟩,
    exact mul_nonpos_of_nonpos_of_nonneg ha.le hb }
end

lemma neg_of_mul_pos_right [pos_mul_mono α] [mul_pos_mono α]
  (ha : a ≤ 0) (h : 0 < a * b) :
  b < 0 :=
((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left $ λ h, h.1.not_le ha).2

lemma neg_of_mul_pos_left [pos_mul_mono α] [mul_pos_mono α]
  (ha : b ≤ 0) (h : 0 < a * b) :
  a < 0 :=
((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left $ λ h, h.2.not_le ha).1

lemma neg_iff_neg_of_mul_pos [pos_mul_mono α] [mul_pos_mono α]
  (hab : 0 < a * b) :
  a < 0 ↔ b < 0 :=
⟨λ h, neg_of_mul_pos_right h.le hab, λ h, neg_of_mul_pos_left h.le hab⟩

lemma left.neg_of_mul_neg_left [pos_mul_mono α]
  (a0 : 0 ≤ a) (h : a * b < 0) :
  b < 0 :=
lt_of_not_ge (λ b0 : b ≥ 0, (left.mul_nonneg a0 b0).not_lt h)

alias left.neg_of_mul_neg_left ← neg_of_mul_neg_left

lemma right.neg_of_mul_neg_left [mul_pos_mono α]
  (a0 : 0 ≤ a) (h : a * b < 0) :
  b < 0 :=
lt_of_not_ge (λ b0 : b ≥ 0, (right.mul_nonneg a0 b0).not_lt h)

lemma left.neg_of_mul_neg_right [pos_mul_mono α]
  (b0 : 0 ≤ b) (h : a * b < 0) : a < 0 :=
lt_of_not_ge (λ a0 : a ≥ 0, (left.mul_nonneg a0 b0).not_lt h)

alias left.neg_of_mul_neg_right ← neg_of_mul_neg_right

lemma right.neg_of_mul_neg_right [mul_pos_mono α]
  (b0 : 0 ≤ b) (h : a * b < 0) : a < 0 :=
lt_of_not_ge (λ a0 : a ≥ 0, (right.mul_nonneg a0 b0).not_lt h)

end linear_order

end mul_zero_class

section mul_one_class
variables [mul_one_class α] [has_zero α]

section preorder
variables [preorder α]

/-! Lemmas of the form `a ≤ a * b ↔ 1 ≤ b` and `a * b ≤ a ↔ b ≤ 1`,
which assume left covariance. -/

@[simp]
lemma le_mul_iff_one_le_right
  [pos_mul_mono α] [pos_mul_mono_rev α]
  (a0 : 0 < a) :
  a ≤ a * b ↔ 1 ≤ b :=
iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a0)

@[simp]
lemma lt_mul_iff_one_lt_right
  [pos_mul_strict_mono α] [pos_mul_reflect_lt α]
  (a0 : 0 < a) :
  a < a * b ↔ 1 < b :=
iff.trans (by rw [mul_one]) (mul_lt_mul_iff_left a0)

@[simp]
lemma mul_le_iff_le_one_right
  [pos_mul_mono α] [pos_mul_mono_rev α]
  (a0 : 0 < a) :
  a * b ≤ a ↔ b ≤ 1 :=
iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a0)

@[simp]
lemma mul_lt_iff_lt_one_right
  [pos_mul_strict_mono α] [pos_mul_reflect_lt α]
  (a0 : 0 < a) :
  a * b < a ↔ b < 1 :=
iff.trans (by rw [mul_one]) (mul_lt_mul_iff_left a0)

/-! Lemmas of the form `a ≤ b * a ↔ 1 ≤ b` and `a * b ≤ b ↔ a ≤ 1`,
which assume right covariance. -/

@[simp]
lemma le_mul_iff_one_le_left
  [mul_pos_mono α] [mul_pos_mono_rev α]
  (a0 : 0 < a) :
  a ≤ b * a ↔ 1 ≤ b :=
iff.trans (by rw [one_mul]) (mul_le_mul_iff_right a0)

@[simp]
lemma lt_mul_iff_one_lt_left
  [mul_pos_strict_mono α] [mul_pos_reflect_lt α]
  (a0 : 0 < a) :
  a < b * a ↔ 1 < b :=
iff.trans (by rw [one_mul]) (mul_lt_mul_iff_right a0)

@[simp]
lemma mul_le_iff_le_one_left
  [mul_pos_mono α] [mul_pos_mono_rev α]
  (b0 : 0 < b) :
  a * b ≤ b ↔ a ≤ 1 :=
iff.trans (by rw [one_mul]) (mul_le_mul_iff_right b0)

@[simp]
lemma mul_lt_iff_lt_one_left
  [mul_pos_strict_mono α] [mul_pos_reflect_lt α]
  (b0 : 0 < b) :
  a * b < b ↔ a < 1 :=
iff.trans (by rw [one_mul]) (mul_lt_mul_iff_right b0)

/-! Lemmas of the form `b ≤ c → a ≤ 1 → b * a ≤ c`. -/

-- proven with `b0 : 0 ≤ b` as `mul_le_of_le_of_le_one`
lemma preorder.mul_le_of_le_of_le_one [pos_mul_mono α]
  (b0 : 0 < b) (bc : b ≤ c) (ha : a ≤ 1) : b * a ≤ c :=
calc  b * a ≤ b * 1 : mul_le_mul_left' b0 ha
        ... = b     : mul_one b
        ... ≤ c     : bc

lemma mul_lt_of_le_of_lt_one [pos_mul_strict_mono α]
  (b0 : 0 < b) (bc : b ≤ c) (ha : a < 1) : b * a < c :=
calc  b * a < b * 1 : mul_lt_mul_left b0 ha
        ... = b     : mul_one b
        ... ≤ c     : bc

lemma mul_lt_of_lt_of_le_one [pos_mul_mono α]
  (b0 : 0 < b) (bc : b < c) (ha : a ≤ 1) : b * a < c :=
calc  b * a ≤ b * 1 : mul_le_mul_left' b0 ha
        ... = b     : mul_one b
        ... < c     : bc

lemma mul_lt_of_lt_of_lt_one [pos_mul_strict_mono α]
  (b0 : 0 < b) (bc : b < c) (ha : a < 1) : b * a < c :=
calc  b * a < b * 1 : mul_lt_mul_left b0 ha
        ... = b     : mul_one b
        ... < c     : bc

-- proven with `a0 : 0 ≤ a` as `left.mul_le_one_of_le_of_le`
/-- Assumes left covariance. -/
lemma preorder.left.mul_le_one_of_le_of_le [pos_mul_mono α]
  (a0 : 0 < a) (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 :=
preorder.mul_le_of_le_of_le_one a0 ha hb

/-- Assumes left covariance. -/
lemma left.mul_lt_one_of_le_of_lt [pos_mul_strict_mono α]
  (a0 : 0 < a) (ha : a ≤ 1) (hb : b < 1) : a * b < 1 :=
mul_lt_of_le_of_lt_one a0 ha hb

/-- Assumes left covariance. -/
lemma left.mul_lt_one_of_lt_of_le [pos_mul_mono α]
  (a0 : 0 < a) (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
mul_lt_of_lt_of_le_one a0 ha hb

/-- Assumes left covariance. -/
lemma left.mul_lt_one_of_lt_of_lt [pos_mul_strict_mono α]
  (a0 : 0 < a) (ha : a < 1) (hb : b < 1) : a * b < 1 :=
mul_lt_of_lt_of_lt_one a0 ha hb

alias preorder.left.mul_le_one_of_le_of_le ← preorder.mul_le_one_of_le_of_le
alias left.mul_lt_one_of_le_of_lt          ← mul_lt_one_of_le_of_lt
alias left.mul_lt_one_of_lt_of_le          ← mul_lt_one_of_lt_of_le
alias left.mul_lt_one_of_lt_of_lt          ← mul_lt_one_of_lt_of_lt

-- proven with `a0 : 0 ≤ a` and `c0 : 0 ≤ c` as `mul_le_of_le_of_le_one'`
lemma preorder.mul_le_of_le_of_le_one' [pos_mul_mono α] [mul_pos_mono α]
  (a0 : 0 < a) (c0 : 0 < c) (bc : b ≤ c) (ha : a ≤ 1) : b * a ≤ c :=
calc  b * a ≤ c * a : mul_le_mul_right' a0 bc
        ... ≤ c * 1 : mul_le_mul_left' c0 ha
        ... = c     : mul_one c

-- proven with `c0 : 0 ≤ c` as `mul_lt_of_lt_of_le_one'`
lemma preorder.mul_lt_of_lt_of_le_one' [pos_mul_mono α] [mul_pos_strict_mono α]
  (a0 : 0 < a) (c0 : 0 < c) (bc : b < c) (ha : a ≤ 1) : b * a < c :=
calc  b * a < c * a : mul_lt_mul_right a0 bc
        ... ≤ c * 1 : mul_le_mul_left' c0 ha
        ... = c     : mul_one c

-- proven with `a0 : 0 ≤ a` as `mul_lt_of_le_of_lt_one'`
lemma preorder.mul_lt_of_le_of_lt_one' [pos_mul_strict_mono α] [mul_pos_mono α]
  (a0 : 0 < a) (c0 : 0 < c) (bc : b ≤ c) (ha : a < 1) : b * a < c :=
calc  b * a ≤ c * a : mul_le_mul_right' a0 bc
        ... < c * 1 : mul_lt_mul_left c0 ha
        ... = c     : mul_one c

lemma mul_lt_of_lt_of_lt_one' [pos_mul_strict_mono α] [mul_pos_strict_mono α]
  (a0 : 0 < a) (c0 : 0 < c) (bc : b < c) (ha : a < 1) : b * a < c :=
calc  b * a < c * a : mul_lt_mul_right a0 bc
        ... < c * 1 : mul_lt_mul_left c0 ha
        ... = c     : mul_one c

/-! Lemmas of the form `b ≤ c → 1 ≤ a → b ≤ c * a`. -/

-- proven with `c0 : 0 ≤ c` as `le_mul_of_le_of_one_le`
lemma preorder.le_mul_of_le_of_one_le [pos_mul_mono α]
  (c0 : 0 < c) (bc : b ≤ c) (ha : 1 ≤ a) : b ≤ c * a :=
calc  b ≤ c     : bc
    ... = c * 1 : (mul_one c).symm
    ... ≤ c * a : mul_le_mul_left' c0 ha

lemma lt_mul_of_le_of_one_lt [pos_mul_strict_mono α]
  (c0 : 0 < c) (bc : b ≤ c) (ha : 1 < a) : b < c * a :=
calc  b ≤ c     : bc
    ... = c * 1 : (mul_one c).symm
    ... < c * a : mul_lt_mul_left c0 ha

lemma lt_mul_of_lt_of_one_le [pos_mul_mono α]
  (c0 : 0 < c) (bc : b < c) (ha : 1 ≤ a) : b < c * a :=
calc  b < c     : bc
    ... = c * 1 : (mul_one c).symm
    ... ≤ c * a : mul_le_mul_left' c0 ha

lemma lt_mul_of_lt_of_one_lt [pos_mul_strict_mono α]
  (c0 : 0 < c) (bc : b < c) (ha : 1 < a) : b < c * a :=
calc  b < c     : bc
    ... = c * 1 : (mul_one _).symm
    ... < c * a : mul_lt_mul_left c0 ha

-- proven with `a0 : 0 ≤ a` as `left.one_le_mul_of_le_of_le`
/-- Assumes left covariance. -/
lemma preorder.left.one_le_mul_of_le_of_le [pos_mul_mono α]
  (a0 : 0 < a) (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
preorder.le_mul_of_le_of_one_le a0 ha hb

/-- Assumes left covariance. -/
lemma left.one_lt_mul_of_le_of_lt [pos_mul_strict_mono α]
  (a0 : 0 < a) (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
lt_mul_of_le_of_one_lt a0 ha hb

/-- Assumes left covariance. -/
lemma left.one_lt_mul_of_lt_of_le [pos_mul_mono α]
  (a0 : 0 < a) (ha : 1 < a) (hb : 1 ≤ b) : 1 < a * b :=
lt_mul_of_lt_of_one_le a0 ha hb

/-- Assumes left covariance. -/
lemma left.one_lt_mul_of_lt_of_lt [pos_mul_strict_mono α]
  (a0 : 0 < a) (ha : 1 < a) (hb : 1 < b) : 1 < a * b :=
lt_mul_of_lt_of_one_lt a0 ha hb

alias preorder.left.one_le_mul_of_le_of_le ← preorder.one_le_mul_of_le_of_le
alias left.one_lt_mul_of_le_of_lt          ← one_lt_mul_of_le_of_lt
alias left.one_lt_mul_of_lt_of_le          ← one_lt_mul_of_lt_of_le
alias left.one_lt_mul_of_lt_of_lt          ← one_lt_mul_of_lt_of_lt

-- proven with `a0 : 0 ≤ a` and `b0 : 0 ≤ b` as `le_mul_of_le_of_one_le'`
lemma preorder.le_mul_of_le_of_one_le' [pos_mul_mono α] [mul_pos_mono α]
  (a0 : 0 < a) (b0 : 0 < b) (bc : b ≤ c) (ha : 1 ≤ a) : b ≤ c * a :=
calc  b = b * 1 : (mul_one b).symm
    ... ≤ b * a : mul_le_mul_left' b0 ha
    ... ≤ c * a : mul_le_mul_right' a0 bc

-- proven with `a0 : 0 ≤ a` as `lt_mul_of_le_of_one_lt'`
lemma preorder.lt_mul_of_le_of_one_lt' [pos_mul_strict_mono α] [mul_pos_mono α]
  (a0 : 0 < a) (b0 : 0 < b) (bc : b ≤ c) (ha : 1 < a) : b < c * a :=
calc  b = b * 1 : (mul_one b).symm
    ... < b * a : mul_lt_mul_left b0 ha
    ... ≤ c * a : mul_le_mul_right' a0 bc

-- proven with `b0 : 0 ≤ b` as `lt_mul_of_lt_of_one_le'`
lemma preorder.lt_mul_of_lt_of_one_le' [pos_mul_mono α] [mul_pos_strict_mono α]
  (a0 : 0 < a) (b0 : 0 < b) (bc : b < c) (ha : 1 ≤ a) : b < c * a :=
calc  b = b * 1 : (mul_one b).symm
    ... ≤ b * a : mul_le_mul_left' b0 ha
    ... < c * a : mul_lt_mul_right a0 bc

lemma lt_mul_of_lt_of_one_lt' [pos_mul_strict_mono α] [mul_pos_strict_mono α]
  (a0 : 0 < a) (b0 : 0 < b) (bc : b < c) (ha : 1 < a) : b < c * a :=
calc  b = b * 1 : (mul_one b).symm
    ... < b * a : mul_lt_mul_left b0 ha
    ... < c * a : mul_lt_mul_right a0 bc

/-! Lemmas of the form `a ≤ 1 → b ≤ c → a * b ≤ c`. -/

-- proven with `b0 : 0 ≤ b` as `mul_le_of_le_one_of_le`
lemma preorder.mul_le_of_le_one_of_le [mul_pos_mono α]
  (b0 : 0 < b) (ha : a ≤ 1) (bc : b ≤ c) : a * b ≤ c :=
calc  a * b ≤ 1 * b : mul_le_mul_right' b0 ha
        ... = b     : one_mul b
        ... ≤ c     : bc

lemma mul_lt_of_lt_one_of_le [mul_pos_strict_mono α]
  (b0 : 0 < b) (ha : a < 1) (bc : b ≤ c) : a * b < c :=
calc  a * b < 1 * b : mul_lt_mul_right b0 ha
        ... = b     : one_mul b
        ... ≤ c     : bc

lemma mul_lt_of_le_one_of_lt [mul_pos_mono α]
  (b0 : 0 < b) (ha : a ≤ 1) (hb : b < c) : a * b < c :=
calc  a * b ≤ 1 * b : mul_le_mul_right' b0 ha
        ... = b     : one_mul b
        ... < c     : hb

lemma mul_lt_of_lt_one_of_lt [mul_pos_strict_mono α]
  (b0 : 0 < b) (ha : a < 1) (bc : b < c) : a * b < c :=
calc  a * b < 1 * b : mul_lt_mul_right b0 ha
        ... = b     : one_mul b
        ... < c     : bc

-- proven with `b0 : 0 ≤ b` as `right.mul_le_one_of_le_of_le`
/-- Assumes right covariance. -/
lemma preorder.right.mul_le_one_of_le_of_le [mul_pos_mono α]
  (b0 : 0 < b) (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 :=
preorder.mul_le_of_le_one_of_le b0 ha hb

/-- Assumes right covariance. -/
lemma right.mul_lt_one_of_lt_of_le [mul_pos_strict_mono α]
  (b0 : 0 < b) (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
mul_lt_of_lt_one_of_le b0 ha hb

/-- Assumes right covariance. -/
lemma right.mul_lt_one_of_le_of_lt [mul_pos_mono α]
  (b0 : 0 < b) (ha : a ≤ 1) (hb : b < 1) : a * b < 1 :=
mul_lt_of_le_one_of_lt b0 ha hb

/-- Assumes right covariance. -/
lemma right.mul_lt_one_of_lt_of_lt [mul_pos_strict_mono α]
  (b0 : 0 < b) (ha : a < 1) (hb : b < 1) : a * b < 1 :=
mul_lt_of_lt_one_of_lt b0 ha hb

-- proven with `a0 : 0 ≤ a` and `c0 : 0 ≤ c` as `mul_le_of_le_one_of_le'`
lemma preorder.mul_le_of_le_one_of_le' [pos_mul_mono α] [mul_pos_mono α]
  (a0 : 0 < a) (c0 : 0 < c) (ha : a ≤ 1) (bc : b ≤ c) : a * b ≤ c :=
calc  a * b ≤ a * c : mul_le_mul_left' a0 bc
        ... ≤ 1 * c : mul_le_mul_right' c0 ha
        ... = c     : one_mul c

-- proven with `a0 : 0 ≤ a` as `mul_lt_of_lt_one_of_le'`
lemma preorder.mul_lt_of_lt_one_of_le' [pos_mul_mono α] [mul_pos_strict_mono α]
  (a0 : 0 < a) (c0 : 0 < c) (ha : a < 1) (bc : b ≤ c) : a * b < c :=
calc  a * b ≤ a * c : mul_le_mul_left' a0 bc
        ... < 1 * c : mul_lt_mul_right c0 ha
        ... = c     : one_mul c

-- proven with `c0 : 0 ≤ c` as `mul_lt_of_le_one_of_lt'`
lemma preorder.mul_lt_of_le_one_of_lt' [pos_mul_strict_mono α] [mul_pos_mono α]
  (a0 : 0 < a) (c0 : 0 < c) (ha : a ≤ 1) (bc : b < c) : a * b < c :=
calc  a * b < a * c : mul_lt_mul_left a0 bc
        ... ≤ 1 * c : mul_le_mul_right' c0 ha
        ... = c     : one_mul c

lemma mul_lt_of_lt_one_of_lt' [pos_mul_strict_mono α] [mul_pos_strict_mono α]
  (a0 : 0 < a) (c0 : 0 < c) (ha : a < 1) (bc : b < c) : a * b < c :=
calc  a * b < a * c : mul_lt_mul_left a0 bc
        ... < 1 * c : mul_lt_mul_right c0 ha
        ... = c     : one_mul c

/-! Lemmas of the form `1 ≤ a → b ≤ c → b ≤ a * c`. -/

-- proven with `c0 : 0 ≤ c` as `le_mul_of_one_le_of_le`
lemma preorder.le_mul_of_one_le_of_le [mul_pos_mono α]
  (c0 : 0 < c) (ha : 1 ≤ a) (bc : b ≤ c) : b ≤ a * c :=
calc  b ≤ c     : bc
    ... = 1 * c : (one_mul c).symm
    ... ≤ a * c : mul_le_mul_right' c0 ha

lemma lt_mul_of_one_lt_of_le [mul_pos_strict_mono α]
  (c0 : 0 < c) (ha : 1 < a) (bc : b ≤ c) : b < a * c :=
calc  b ≤ c     : bc
    ... = 1 * c : (one_mul c).symm
    ... < a * c : mul_lt_mul_right c0 ha

lemma lt_mul_of_one_le_of_lt [mul_pos_mono α]
  (c0 : 0 < c) (ha : 1 ≤ a) (bc : b < c) : b < a * c :=
calc  b < c     : bc
    ... = 1 * c : (one_mul c).symm
    ... ≤ a * c : mul_le_mul_right' c0 ha

lemma lt_mul_of_one_lt_of_lt [mul_pos_strict_mono α]
  (c0 : 0 < c) (ha : 1 < a) (bc : b < c) : b < a * c :=
calc  b < c     : bc
    ... = 1 * c : (one_mul c).symm
    ... < a * c : mul_lt_mul_right c0 ha

-- proven with `b0 : 0 ≤ b` as `right.one_le_mul_of_le_of_le`
/-- Assumes right covariance. -/
lemma preorder.right.one_le_mul_of_le_of_le [mul_pos_mono α]
  (b0 : 0 < b) (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
preorder.le_mul_of_one_le_of_le b0 ha hb

/-- Assumes right covariance. -/
lemma right.one_lt_mul_of_lt_of_le [mul_pos_strict_mono α]
  (b0 : 0 < b) (ha : 1 < a) (hb : 1 ≤ b) : 1 < a * b :=
lt_mul_of_one_lt_of_le b0 ha hb

/-- Assumes right covariance. -/
lemma right.one_lt_mul_of_le_of_lt [mul_pos_mono α]
  (b0 : 0 < b) (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
lt_mul_of_one_le_of_lt b0 ha hb

/-- Assumes right covariance. -/
lemma right.one_lt_mul_of_lt_of_lt [mul_pos_strict_mono α]
  (b0 : 0 < b) (ha : 1 < a) (hb : 1 < b) : 1 < a * b :=
lt_mul_of_one_lt_of_lt b0 ha hb

-- proven with `a0 : 0 ≤ a` and `b0 : 0 ≤ b` as `le_mul_of_one_le_of_le'`
lemma preorder.le_mul_of_one_le_of_le' [pos_mul_mono α] [mul_pos_mono α]
  (a0 : 0 < a) (b0 : 0 < b) (ha : 1 ≤ a) (bc : b ≤ c) : b ≤ a * c :=
calc  b = 1 * b : (one_mul b).symm
    ... ≤ a * b : mul_le_mul_right' b0 ha
    ... ≤ a * c : mul_le_mul_left' a0 bc

-- proven with `a0 : 0 ≤ a` as `lt_mul_of_one_lt_of_le'`
lemma preorder.lt_mul_of_one_lt_of_le' [pos_mul_mono α] [mul_pos_strict_mono α]
  (a0 : 0 < a) (b0 : 0 < b) (ha : 1 < a) (bc : b ≤ c) : b < a * c :=
calc  b = 1 * b : (one_mul b).symm
    ... < a * b : mul_lt_mul_right b0 ha
    ... ≤ a * c : mul_le_mul_left' a0 bc

-- proven with `b0 : 0 ≤ b` as `lt_mul_of_one_le_of_lt'`
lemma preorder.lt_mul_of_one_le_of_lt' [pos_mul_strict_mono α] [mul_pos_mono α]
  (a0 : 0 < a) (b0 : 0 < b) (ha : 1 ≤ a) (bc : b < c) : b < a * c :=
calc  b = 1 * b : (one_mul b).symm
    ... ≤ a * b : mul_le_mul_right' b0 ha
    ... < a * c : mul_lt_mul_left a0 bc

lemma lt_mul_of_one_lt_of_lt' [pos_mul_strict_mono α] [mul_pos_strict_mono α]
  (a0 : 0 < a) (b0 : 0 < b) (ha : 1 < a) (bc : b < c) : b < a * c :=
calc  b = 1 * b : (one_mul b).symm
    ... < a * b : mul_lt_mul_right b0 ha
    ... < a * c : mul_lt_mul_left a0 bc

-- proven with `a0 : 0 ≤ a` as `mul_le_of_le_one_right`
lemma preorder.mul_le_of_le_one_right [pos_mul_mono α] (a0 : 0 < a) (h : b ≤ 1) :
  a * b ≤ a :=
preorder.mul_le_of_le_of_le_one a0 le_rfl h

-- proven with `a0 : 0 ≤ a` as `le_mul_of_one_le_right`
lemma preorder.le_mul_of_one_le_right [pos_mul_mono α] (a0 : 0 < a) (h : 1 ≤ b) :
  a ≤ a * b :=
preorder.le_mul_of_le_of_one_le a0 le_rfl h

-- proven with `b0 : 0 ≤ b` as `mul_le_of_le_one_left`
lemma preorder.mul_le_of_le_one_left [mul_pos_mono α] (b0 : 0 < b) (h : a ≤ 1) :
  a * b ≤ b :=
preorder.mul_le_of_le_one_of_le b0 h le_rfl

-- proven with `b0 : 0 ≤ b` as `le_mul_of_one_le_left`
lemma preorder.le_mul_of_one_le_left [mul_pos_mono α] (b0 : 0 < b) (h : 1 ≤ a) :
  b ≤ a * b :=
preorder.le_mul_of_one_le_of_le b0 h le_rfl

lemma mul_lt_of_lt_one_right [pos_mul_strict_mono α] (a0 : 0 < a) (h : b < 1) :
  a * b < a :=
mul_lt_of_le_of_lt_one a0 le_rfl h

lemma lt_mul_of_one_lt_right [pos_mul_strict_mono α] (a0 : 0 < a) (h : 1 < b) :
  a < a * b :=
lt_mul_of_le_of_one_lt a0 le_rfl h

lemma mul_lt_of_lt_one_left [mul_pos_strict_mono α] (b0 : 0 < b) (h : a < 1) :
  a * b < b :=
mul_lt_of_lt_one_of_le b0 h le_rfl

lemma lt_mul_of_one_lt_left [mul_pos_strict_mono α] (b0 : 0 < b) (h : 1 < a) :
  b < a * b :=
lt_mul_of_one_lt_of_le b0 h le_rfl

-- proven with `a0 : 0 ≤ a` as `le_of_mul_le_of_one_le_left`
lemma preorder.le_of_mul_le_of_one_le_left [pos_mul_mono α]
  (a0 : 0 < a) (h : a * b ≤ c) (hle : 1 ≤ b) :
  a ≤ c :=
(preorder.le_mul_of_one_le_right a0 hle).trans h

lemma lt_of_mul_lt_of_one_le_left [pos_mul_mono α]
  (a0 : 0 < a) (h : a * b < c) (hle : 1 ≤ b) :
  a < c :=
(preorder.le_mul_of_one_le_right a0 hle).trans_lt h

-- proven with `b0 : 0 ≤ b` as `le_of_le_mul_of_le_one_left`
lemma preorder.le_of_le_mul_of_le_one_left [pos_mul_mono α]
  (b0 : 0 < b) (h : a ≤ b * c) (hle : c ≤ 1) :
  a ≤ b :=
h.trans (preorder.mul_le_of_le_one_right b0 hle)

lemma lt_of_lt_mul_of_le_one_left [pos_mul_mono α]
  (b0 : 0 < b) (h : a < b * c) (hle : c ≤ 1) :
  a < b :=
h.trans_le (preorder.mul_le_of_le_one_right b0 hle)

-- proven with `b0 : 0 ≤ b` as `le_of_mul_le_of_one_le_right`
lemma preorder.le_of_mul_le_of_one_le_right [mul_pos_mono α]
  (b0 : 0 < b) (h : a * b ≤ c) (hle : 1 ≤ a) :
  b ≤ c :=
(preorder.le_mul_of_one_le_left b0 hle).trans h

lemma lt_of_mul_lt_of_one_le_right [mul_pos_mono α]
  (b0 : 0 < b) (h : a * b < c) (hle : 1 ≤ a) :
  b < c :=
(preorder.le_mul_of_one_le_left b0 hle).trans_lt h

-- proven with `c0 : 0 ≤ b` as `le_of_le_mul_of_le_one_right`
lemma preorder.le_of_le_mul_of_le_one_right [mul_pos_mono α]
  (c0 : 0 < c) (h : a ≤ b * c) (hle : b ≤ 1) :
  a ≤ c :=
h.trans (preorder.mul_le_of_le_one_left c0 hle)

lemma lt_of_lt_mul_of_le_one_right [mul_pos_mono α]
  (c0 : 0 < c) (h : a < b * c) (hle : b ≤ 1) :
  a < c :=
h.trans_le (preorder.mul_le_of_le_one_left c0 hle)

end preorder

section linear_order
variables [linear_order α]

-- proven with `a0 : 0 ≤ a` as `exists_square_le`
lemma exists_square_le' [pos_mul_strict_mono α]
  (a0 : 0 < a) : ∃ (b : α), b * b ≤ a :=
begin
  by_cases h : a < 1,
  { use a,
    have : a*a < a*1,
    exact mul_lt_mul_left a0 h,
    rw mul_one at this,
    exact le_of_lt this },
  { use 1,
    push_neg at h,
    rwa mul_one }
end

end linear_order

end mul_one_class

section mul_zero_one_class
variables [mul_zero_one_class α]

section partial_order
variables [partial_order α]

/-! Lemmas of the form `b ≤ c → a ≤ 1 → b * a ≤ c`. -/

lemma mul_le_of_le_of_le_one [pos_mul_mono α]
  (b0 : 0 ≤ b) (bc : b ≤ c) (ha : a ≤ 1) : b * a ≤ c :=
b0.lt_or_eq.elim (λ h, preorder.mul_le_of_le_of_le_one h bc ha)
  (λ h, by rw [← h, zero_mul]; exact b0.trans bc)

/-- Assumes left covariance. -/
lemma left.mul_le_one_of_le_of_le [pos_mul_mono α]
  (a0 : 0 ≤ a) (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 :=
mul_le_of_le_of_le_one a0 ha hb

alias left.mul_le_one_of_le_of_le ← mul_le_one_of_le_of_le

lemma mul_le_of_le_of_le_one' [pos_mul_mono α] [mul_pos_mono α]
  (a0 : 0 ≤ a) (c0 : 0 ≤ c) (bc : b ≤ c) (ha : a ≤ 1) : b * a ≤ c :=
calc  b * a ≤ c * a : mul_le_mul_right a0 bc
        ... ≤ c * 1 : mul_le_mul_left c0 ha
        ... = c     : mul_one c

lemma mul_lt_of_lt_of_le_one' [pos_mul_mono α] [mul_pos_strict_mono α]
  (a0 : 0 < a) (c0 : 0 ≤ c) (bc : b < c) (ha : a ≤ 1) : b * a < c :=
calc  b * a < c * a : mul_lt_mul_right a0 bc
        ... ≤ c * 1 : mul_le_mul_left c0 ha
        ... = c     : mul_one c

lemma mul_lt_of_le_of_lt_one' [pos_mul_strict_mono α] [mul_pos_mono α]
  (a0 : 0 ≤ a) (c0 : 0 < c) (bc : b ≤ c) (ha : a < 1) : b * a < c :=
calc  b * a ≤ c * a : mul_le_mul_right a0 bc
        ... < c * 1 : mul_lt_mul_left c0 ha
        ... = c     : mul_one c

/-! Lemmas of the form `b ≤ c → 1 ≤ a → b ≤ c * a`. -/

lemma le_mul_of_le_of_one_le [pos_mul_mono α]
  (c0 : 0 ≤ c) (bc : b ≤ c) (ha : 1 ≤ a) : b ≤ c * a :=
c0.lt_or_eq.elim (λ h, preorder.le_mul_of_le_of_one_le h bc ha)
  (λ h, by rw [← h, zero_mul] at *; exact bc)

/-- Assumes left covariance. -/
lemma left.one_le_mul_of_le_of_le [pos_mul_mono α]
  (a0 : 0 ≤ a) (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
le_mul_of_le_of_one_le a0 ha hb

alias left.one_le_mul_of_le_of_le ← one_le_mul_of_le_of_le

lemma le_mul_of_le_of_one_le' [pos_mul_mono α] [mul_pos_mono α]
  (a0 : 0 ≤ a) (b0 : 0 ≤ b) (bc : b ≤ c) (ha : 1 ≤ a) : b ≤ c * a :=
calc  b = b * 1 : (mul_one b).symm
    ... ≤ b * a : mul_le_mul_left b0 ha
    ... ≤ c * a : mul_le_mul_right a0 bc

lemma lt_mul_of_le_of_one_lt' [pos_mul_strict_mono α] [mul_pos_mono α]
  (a0 : 0 ≤ a) (b0 : 0 < b) (bc : b ≤ c) (ha : 1 < a) : b < c * a :=
calc  b = b * 1 : (mul_one b).symm
    ... < b * a : mul_lt_mul_left b0 ha
    ... ≤ c * a : mul_le_mul_right a0 bc

lemma lt_mul_of_lt_of_one_le' [pos_mul_mono α] [mul_pos_strict_mono α]
  (a0 : 0 < a) (b0 : 0 ≤ b) (bc : b < c) (ha : 1 ≤ a) : b < c * a :=
calc  b = b * 1 : (mul_one b).symm
    ... ≤ b * a : mul_le_mul_left b0 ha
    ... < c * a : mul_lt_mul_right a0 bc

/-! Lemmas of the form `a ≤ 1 → b ≤ c → a * b ≤ c`. -/

lemma mul_le_of_le_one_of_le [mul_pos_mono α]
  (b0 : 0 ≤ b) (ha : a ≤ 1) (bc : b ≤ c) : a * b ≤ c :=
b0.lt_or_eq.elim (λ h, preorder.mul_le_of_le_one_of_le h ha bc)
  (λ h, by rw [← h, mul_zero] at *; exact bc)

/-- Assumes right covariance. -/
lemma right.mul_le_one_of_le_of_le [mul_pos_mono α]
  (b0 : 0 < b) (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 :=
preorder.mul_le_of_le_one_of_le b0 ha hb

lemma mul_le_of_le_one_of_le' [pos_mul_mono α] [mul_pos_mono α]
  (a0 : 0 ≤ a) (c0 : 0 ≤ c) (ha : a ≤ 1) (bc : b ≤ c) : a * b ≤ c :=
calc  a * b ≤ a * c : mul_le_mul_left a0 bc
        ... ≤ 1 * c : mul_le_mul_right c0 ha
        ... = c     : one_mul c

lemma mul_lt_of_lt_one_of_le' [pos_mul_mono α] [mul_pos_strict_mono α]
  (a0 : 0 ≤ a) (c0 : 0 < c) (ha : a < 1) (bc : b ≤ c) : a * b < c :=
calc  a * b ≤ a * c : mul_le_mul_left a0 bc
        ... < 1 * c : mul_lt_mul_right c0 ha
        ... = c     : one_mul c

lemma mul_lt_of_le_one_of_lt' [pos_mul_strict_mono α] [mul_pos_mono α]
 (a0 : 0 < a) (c0 : 0 ≤ c)  (ha : a ≤ 1) (bc : b < c) : a * b < c :=
calc  a * b < a * c : mul_lt_mul_left a0 bc
        ... ≤ 1 * c : mul_le_mul_right c0 ha
        ... = c     : one_mul c

/-! Lemmas of the form `1 ≤ a → b ≤ c → b ≤ a * c`. -/

lemma le_mul_of_one_le_of_le [mul_pos_mono α]
  (c0 : 0 ≤ c) (ha : 1 ≤ a) (bc : b ≤ c) : b ≤ a * c :=
c0.lt_or_eq.elim (λ h, preorder.le_mul_of_one_le_of_le h ha bc)
  (λ h, by rw [← h, mul_zero] at *; exact bc)

/-- Assumes right covariance. -/
lemma right.one_le_mul_of_le_of_le [mul_pos_mono α]
  (b0 : 0 ≤ b) (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
le_mul_of_one_le_of_le b0 ha hb

lemma le_mul_of_one_le_of_le' [pos_mul_mono α] [mul_pos_mono α]
  (a0 : 0 ≤ a) (b0 : 0 ≤ b) (ha : 1 ≤ a) (bc : b ≤ c) : b ≤ a * c :=
calc  b = 1 * b : (one_mul b).symm
    ... ≤ a * b : mul_le_mul_right b0 ha
    ... ≤ a * c : mul_le_mul_left a0 bc

lemma lt_mul_of_one_lt_of_le' [pos_mul_mono α] [mul_pos_strict_mono α]
  (a0 : 0 ≤ a) (b0 : 0 < b) (ha : 1 < a) (bc : b ≤ c) : b < a * c :=
calc  b = 1 * b : (one_mul b).symm
    ... < a * b : mul_lt_mul_right b0 ha
    ... ≤ a * c : mul_le_mul_left a0 bc

lemma lt_mul_of_one_le_of_lt' [pos_mul_strict_mono α] [mul_pos_mono α]
  (a0 : 0 < a) (b0 : 0 ≤ b) (ha : 1 ≤ a) (bc : b < c) : b < a * c :=
calc  b = 1 * b : (one_mul b).symm
    ... ≤ a * b : mul_le_mul_right b0 ha
    ... < a * c : mul_lt_mul_left a0 bc

lemma mul_le_of_le_one_right [pos_mul_mono α] (a0 : 0 ≤ a) (h : b ≤ 1) :
  a * b ≤ a :=
mul_le_of_le_of_le_one a0 le_rfl h

lemma le_mul_of_one_le_right [pos_mul_mono α] (a0 : 0 ≤ a) (h : 1 ≤ b) :
  a ≤ a * b :=
le_mul_of_le_of_one_le a0 le_rfl h

lemma mul_le_of_le_one_left [mul_pos_mono α] (b0 : 0 ≤ b) (h : a ≤ 1) :
  a * b ≤ b :=
mul_le_of_le_one_of_le b0 h le_rfl

lemma le_mul_of_one_le_left [mul_pos_mono α] (b0 : 0 ≤ b) (h : 1 ≤ a) :
  b ≤ a * b :=
le_mul_of_one_le_of_le b0 h le_rfl

lemma le_of_mul_le_of_one_le_left [pos_mul_mono α]
  (a0 : 0 ≤ a) (h : a * b ≤ c) (hb : 1 ≤ b) :
  a ≤ c :=
a0.lt_or_eq.elim (λ ha, preorder.le_of_mul_le_of_one_le_left ha h hb)
  (λ ha, by simpa only [← ha, zero_mul] using h)

lemma le_of_le_mul_of_le_one_left [pos_mul_mono α]
  (a0 : 0 ≤ a) (h : c ≤ a * b) (hb : b ≤ 1) :
  c ≤ a :=
a0.lt_or_eq.elim (λ ha, preorder.le_of_le_mul_of_le_one_left ha h hb)
  (λ ha, by simpa only [← ha, zero_mul] using h)

lemma le_of_mul_le_of_one_le_right [mul_pos_mono α]
  (b0 : 0 ≤ b) (h : a * b ≤ c) (ha : 1 ≤ a) :
  b ≤ c :=
b0.lt_or_eq.elim (λ hb, preorder.le_of_mul_le_of_one_le_right hb h ha)
  (λ hb, by simpa only [← hb, mul_zero] using h)

lemma le_of_le_mul_of_le_one_right [mul_pos_mono α]
  (b0 : 0 ≤ b) (h : c ≤ a * b) (ha : a ≤ 1) :
  c ≤ b :=
b0.lt_or_eq.elim (λ hb, preorder.le_of_le_mul_of_le_one_right hb h ha)
  (λ hb, by simpa only [← hb, mul_zero] using h)

end partial_order

section linear_order
variables [linear_order α]

lemma exists_square_le [pos_mul_strict_mono α]
  (a0 : 0 ≤ a) : ∃ (b : α), b * b ≤ a :=
a0.lt_or_eq.elim exists_square_le' (λ h, by rw [← h]; exact ⟨0, by simp⟩)

end linear_order

end mul_zero_one_class

section cancel_monoid_with_zero

variables [cancel_monoid_with_zero α]

section partial_order
variables [partial_order α]

lemma pos_mul_mono.to_pos_mul_strict_mono [pos_mul_mono α] : pos_mul_strict_mono α :=
⟨λ x a b h, lt_of_le_of_ne (mul_le_mul_left' x.2 h.le) (h.ne ∘ mul_left_cancel₀ x.2.ne.symm)⟩

lemma pos_mul_mono_iff_pos_mul_strict_mono : pos_mul_mono α ↔ pos_mul_strict_mono α :=
⟨@pos_mul_mono.to_pos_mul_strict_mono α _ _, @zero_lt.pos_mul_strict_mono.to_pos_mul_mono α _ _ _⟩

lemma mul_pos_mono.to_mul_pos_strict_mono [mul_pos_mono α] : mul_pos_strict_mono α :=
⟨λ x a b h, lt_of_le_of_ne (mul_le_mul_right' x.2 h.le) (h.ne ∘ mul_right_cancel₀ x.2.ne.symm)⟩

lemma mul_pos_mono_iff_mul_pos_strict_mono : mul_pos_mono α ↔ mul_pos_strict_mono α :=
⟨@mul_pos_mono.to_mul_pos_strict_mono α _ _, @zero_lt.mul_pos_strict_mono.to_mul_pos_mono α _ _ _⟩

lemma pos_mul_reflect_lt.to_pos_mul_mono_rev [pos_mul_reflect_lt α] : pos_mul_mono_rev α :=
⟨λ x a b h, h.eq_or_lt.elim (le_of_eq ∘ mul_left_cancel₀ x.2.ne.symm)
                            (le_of_lt ∘ lt_of_mul_lt_mul_left' x.2)⟩

lemma pos_mul_mono_rev_iff_pos_mul_reflect_lt : pos_mul_mono_rev α ↔ pos_mul_reflect_lt α :=
⟨@zero_lt.pos_mul_mono_rev.to_pos_mul_reflect_lt α _ _ _,
 @pos_mul_reflect_lt.to_pos_mul_mono_rev α _ _⟩

lemma mul_pos_reflect_lt.to_mul_pos_mono_rev [mul_pos_reflect_lt α] : mul_pos_mono_rev α :=
⟨λ x a b h, h.eq_or_lt.elim (le_of_eq ∘ mul_right_cancel₀ x.2.ne.symm)
                            (le_of_lt ∘ lt_of_mul_lt_mul_right' x.2)⟩

lemma mul_pos_mono_rev_iff_mul_pos_reflect_lt : mul_pos_mono_rev α ↔ mul_pos_reflect_lt α :=
⟨@zero_lt.mul_pos_mono_rev.to_mul_pos_reflect_lt α _ _ _,
 @mul_pos_reflect_lt.to_mul_pos_mono_rev α _ _⟩

end partial_order

end cancel_monoid_with_zero

section comm_semigroup_has_zero
variables [comm_semigroup α] [has_zero α]

variables [has_lt α]

lemma pos_mul_strict_mono_iff_mul_pos_strict_mono :
  pos_mul_strict_mono α ↔ mul_pos_strict_mono α :=
by simp ! only [mul_comm]

lemma pos_mul_reflect_lt_iff_mul_pos_reflect_lt :
  pos_mul_reflect_lt α ↔ mul_pos_reflect_lt α :=
by simp ! only [mul_comm]

variables [has_le α]

lemma pos_mul_mono_iff_mul_pos_mono :
  pos_mul_mono α ↔ mul_pos_mono α :=
by simp ! only [mul_comm]

lemma pos_mul_mono_rev_iff_mul_pos_mono_rev :
  pos_mul_mono_rev α ↔ mul_pos_mono_rev α :=
by simp ! only [mul_comm]

end comm_semigroup_has_zero

end zero_lt
