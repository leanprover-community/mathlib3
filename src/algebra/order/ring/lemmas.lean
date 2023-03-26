/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Yuyang Zhao
-/
import algebra.covariant_and_contravariant
import algebra.group_with_zero.defs

/-!
# Multiplication by ·positive· elements is monotonic

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Let `α` be a type with `<` and `0`.  We use the type `{x : α // 0 < x}` of positive elements of `α`
to prove results about monotonicity of multiplication.  We also introduce the local notation `α>0`
for the subtype `{x : α // 0 < x}`:

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

## Notation

The following is local notation in this file:
* `α≥0`: `{x : α // 0 ≤ x}`
* `α>0`: `{x : α // 0 < x}`
-/

variable (α : Type*)

/- Notations for nonnegative and positive elements
https://
leanprover.zulipchat.com/#narrow/stream/113488-general/topic/notation.20for.20positive.20elements
-/
local notation `α≥0` := {x : α // 0 ≤ x}
local notation `α>0` := {x : α // 0 < x}

section abbreviations
variables [has_mul α] [has_zero α] [preorder α]

/-- `pos_mul_mono α` is an abbreviation for `covariant_class α≥0 α (λ x y, x * y) (≤)`,
expressing that multiplication by nonnegative elements on the left is monotone. -/
abbreviation pos_mul_mono : Prop := covariant_class α≥0 α (λ x y, x * y) (≤)

/-- `mul_pos_mono α` is an abbreviation for `covariant_class α≥0 α (λ x y, y * x) (≤)`,
expressing that multiplication by nonnegative elements on the right is monotone. -/
abbreviation mul_pos_mono : Prop := covariant_class α≥0 α (λ x y, y * x) (≤)

/-- `pos_mul_strict_mono α` is an abbreviation for `covariant_class α>0 α (λ x y, x * y) (<)`,
expressing that multiplication by positive elements on the left is strictly monotone. -/
abbreviation pos_mul_strict_mono : Prop := covariant_class α>0 α (λ x y, x * y) (<)

/-- `mul_pos_strict_mono α` is an abbreviation for `covariant_class α>0 α (λ x y, y * x) (<)`,
expressing that multiplication by positive elements on the right is strictly monotone. -/
abbreviation mul_pos_strict_mono : Prop := covariant_class α>0 α (λ x y, y * x) (<)

/-- `pos_mul_reflect_lt α` is an abbreviation for `contravariant_class α≥0 α (λ x y, x * y) (<)`,
expressing that multiplication by nonnegative elements on the left is strictly reverse monotone. -/
abbreviation pos_mul_reflect_lt : Prop := contravariant_class α≥0 α (λ x y, x * y) (<)

/-- `mul_pos_reflect_lt α` is an abbreviation for `contravariant_class α≥0 α (λ x y, y * x) (<)`,
expressing that multiplication by nonnegative elements on the right is strictly reverse monotone. -/
abbreviation mul_pos_reflect_lt : Prop := contravariant_class α≥0 α (λ x y, y * x) (<)

/-- `pos_mul_mono_rev α` is an abbreviation for `contravariant_class α>0 α (λ x y, x * y) (≤)`,
expressing that multiplication by positive elements on the left is reverse monotone. -/
abbreviation pos_mul_mono_rev : Prop := contravariant_class α>0 α (λ x y, x * y) (≤)

/-- `mul_pos_mono_rev α` is an abbreviation for `contravariant_class α>0 α (λ x y, y * x) (≤)`,
expressing that multiplication by positive elements on the right is reverse monotone. -/
abbreviation mul_pos_mono_rev : Prop := contravariant_class α>0 α (λ x y, y * x) (≤)

end abbreviations

variables {α} {a b c d : α}

section has_mul_zero
variables [has_mul α] [has_zero α]

section preorder
variables [preorder α]

instance pos_mul_mono.to_covariant_class_pos_mul_le [pos_mul_mono α] :
  covariant_class α>0 α (λ x y, x * y) (≤) :=
⟨λ a b c bc, @covariant_class.elim α≥0 α (λ x y, x * y) (≤) _ ⟨_, a.2.le⟩ _ _ bc⟩

instance mul_pos_mono.to_covariant_class_pos_mul_le [mul_pos_mono α] :
  covariant_class α>0 α (λ x y, y * x) (≤) :=
⟨λ a b c bc, @covariant_class.elim α≥0 α (λ x y, y * x) (≤) _ ⟨_, a.2.le⟩ _ _ bc⟩

instance pos_mul_reflect_lt.to_contravariant_class_pos_mul_lt [pos_mul_reflect_lt α] :
  contravariant_class α>0 α (λ x y, x * y) (<) :=
⟨λ a b c bc, @contravariant_class.elim α≥0 α (λ x y, x * y) (<) _ ⟨_, a.2.le⟩ _ _ bc⟩

instance mul_pos_reflect_lt.to_contravariant_class_pos_mul_lt [mul_pos_reflect_lt α] :
  contravariant_class α>0 α (λ x y, y * x) (<) :=
⟨λ a b c bc, @contravariant_class.elim α≥0 α (λ x y, y * x) (<) _ ⟨_, a.2.le⟩ _ _ bc⟩

lemma mul_le_mul_of_nonneg_left [pos_mul_mono α] (h : b ≤ c) (a0 : 0 ≤ a) : a * b ≤ a * c :=
@covariant_class.elim α≥0 α (λ x y, x * y) (≤) _ ⟨a, a0⟩ _ _ h

lemma mul_le_mul_of_nonneg_right [mul_pos_mono α] (h : b ≤ c) (a0 : 0 ≤ a) : b * a ≤ c * a :=
@covariant_class.elim α≥0 α (λ x y, y * x) (≤) _ ⟨a, a0⟩ _ _ h

lemma mul_lt_mul_of_pos_left [pos_mul_strict_mono α] (bc : b < c) (a0 : 0 < a) : a * b < a * c :=
@covariant_class.elim α>0 α (λ x y, x * y) (<) _ ⟨a, a0⟩ _ _ bc

lemma mul_lt_mul_of_pos_right [mul_pos_strict_mono α] (bc : b < c) (a0 : 0 < a) : b * a < c * a :=
@covariant_class.elim α>0 α (λ x y, y * x) (<) _ ⟨a, a0⟩ _ _ bc

lemma lt_of_mul_lt_mul_left [pos_mul_reflect_lt α] (h : a * b < a * c) (a0 : 0 ≤ a) : b < c :=
@contravariant_class.elim α≥0 α (λ x y, x * y) (<) _ ⟨a, a0⟩ _ _ h

lemma lt_of_mul_lt_mul_right [mul_pos_reflect_lt α] (h : b * a < c * a) (a0 : 0 ≤ a) : b < c :=
@contravariant_class.elim α≥0 α (λ x y, y * x) (<) _ ⟨a, a0⟩ _ _ h

lemma le_of_mul_le_mul_left [pos_mul_mono_rev α] (bc : a * b ≤ a * c) (a0 : 0 < a) : b ≤ c :=
@contravariant_class.elim α>0 α (λ x y, x * y) (≤) _ ⟨a, a0⟩ _ _ bc

lemma le_of_mul_le_mul_right [mul_pos_mono_rev α] (bc : b * a ≤ c * a) (a0 : 0 < a) : b ≤ c :=
@contravariant_class.elim α>0 α (λ x y, y * x) (≤) _ ⟨a, a0⟩ _ _ bc

alias lt_of_mul_lt_mul_left  ← lt_of_mul_lt_mul_of_nonneg_left
alias lt_of_mul_lt_mul_right ← lt_of_mul_lt_mul_of_nonneg_right
alias le_of_mul_le_mul_left  ← le_of_mul_le_mul_of_pos_left
alias le_of_mul_le_mul_right ← le_of_mul_le_mul_of_pos_right

@[simp] lemma mul_lt_mul_left [pos_mul_strict_mono α] [pos_mul_reflect_lt α]
  (a0 : 0 < a) :
  a * b < a * c ↔ b < c :=
@rel_iff_cov α>0 α (λ x y, x * y) (<) _ _ ⟨a, a0⟩ _ _

@[simp] lemma mul_lt_mul_right [mul_pos_strict_mono α] [mul_pos_reflect_lt α]
  (a0 : 0 < a) :
  b * a < c * a ↔ b < c :=
@rel_iff_cov α>0 α (λ x y, y * x) (<) _ _ ⟨a, a0⟩ _ _

@[simp] lemma mul_le_mul_left [pos_mul_mono α] [pos_mul_mono_rev α]
  (a0 : 0 < a) :
  a * b ≤ a * c ↔ b ≤ c :=
@rel_iff_cov α>0 α (λ x y, x * y) (≤) _ _ ⟨a, a0⟩ _ _

@[simp] lemma mul_le_mul_right [mul_pos_mono α] [mul_pos_mono_rev α]
  (a0 : 0 < a) :
  b * a ≤ c * a ↔ b ≤ c :=
@rel_iff_cov α>0 α (λ x y, y * x) (≤) _ _ ⟨a, a0⟩ _ _

lemma mul_lt_mul_of_pos_of_nonneg [pos_mul_strict_mono α] [mul_pos_mono α]
  (h₁ : a ≤ b) (h₂ : c < d) (a0 : 0 < a) (d0 : 0 ≤ d) : a * c < b * d :=
(mul_lt_mul_of_pos_left h₂ a0).trans_le (mul_le_mul_of_nonneg_right h₁ d0)

lemma mul_lt_mul_of_le_of_le' [pos_mul_strict_mono α] [mul_pos_mono α]
  (h₁ : a ≤ b) (h₂ : c < d) (b0 : 0 < b) (c0 : 0 ≤ c) : a * c < b * d :=
(mul_le_mul_of_nonneg_right h₁ c0).trans_lt (mul_lt_mul_of_pos_left h₂ b0)

lemma mul_lt_mul_of_nonneg_of_pos [pos_mul_mono α] [mul_pos_strict_mono α]
  (h₁ : a < b) (h₂ : c ≤ d) (a0 : 0 ≤ a) (d0 : 0 < d) : a * c < b * d :=
(mul_le_mul_of_nonneg_left h₂ a0).trans_lt (mul_lt_mul_of_pos_right h₁ d0)

lemma mul_lt_mul_of_le_of_lt' [pos_mul_mono α] [mul_pos_strict_mono α]
  (h₁ : a < b) (h₂ : c ≤ d) (b0 : 0 ≤ b) (c0 : 0 < c) : a * c < b * d :=
(mul_lt_mul_of_pos_right h₁ c0).trans_le (mul_le_mul_of_nonneg_left h₂ b0)

lemma mul_lt_mul_of_pos_of_pos [pos_mul_strict_mono α] [mul_pos_strict_mono α]
  (h₁ : a < b) (h₂ : c < d) (a0 : 0 < a) (d0 : 0 < d) : a * c < b * d :=
(mul_lt_mul_of_pos_left h₂ a0).trans (mul_lt_mul_of_pos_right h₁ d0)

lemma mul_lt_mul_of_lt_of_lt' [pos_mul_strict_mono α] [mul_pos_strict_mono α]
  (h₁ : a < b) (h₂ : c < d) (b0 : 0 < b) (c0 : 0 < c) : a * c < b * d :=
(mul_lt_mul_of_pos_right h₁ c0).trans (mul_lt_mul_of_pos_left h₂ b0)

lemma mul_lt_of_mul_lt_of_nonneg_left [pos_mul_mono α] (h : a * b < c) (hdb : d ≤ b) (ha : 0 ≤ a) :
  a * d < c :=
(mul_le_mul_of_nonneg_left hdb ha).trans_lt h

lemma lt_mul_of_lt_mul_of_nonneg_left [pos_mul_mono α] (h : a < b * c) (hcd : c ≤ d) (hb : 0 ≤ b) :
  a < b * d :=
h.trans_le $ mul_le_mul_of_nonneg_left hcd hb

lemma mul_lt_of_mul_lt_of_nonneg_right [mul_pos_mono α] (h : a * b < c) (hda : d ≤ a) (hb : 0 ≤ b) :
  d * b < c :=
(mul_le_mul_of_nonneg_right hda hb).trans_lt h

lemma lt_mul_of_lt_mul_of_nonneg_right [mul_pos_mono α] (h : a < b * c) (hbd : b ≤ d) (hc : 0 ≤ c) :
  a < d * c :=
h.trans_le $ mul_le_mul_of_nonneg_right hbd hc

end preorder

section linear_order
variables [linear_order α]

@[priority 100] -- see Note [lower instance priority]
instance pos_mul_strict_mono.to_pos_mul_mono_rev [pos_mul_strict_mono α] : pos_mul_mono_rev α :=
⟨λ x a b h, le_of_not_lt $ λ h', h.not_lt $ mul_lt_mul_of_pos_left h' x.prop⟩

@[priority 100] -- see Note [lower instance priority]
instance mul_pos_strict_mono.to_mul_pos_mono_rev [mul_pos_strict_mono α] : mul_pos_mono_rev α :=
⟨λ x a b h, le_of_not_lt $ λ h', h.not_lt $ mul_lt_mul_of_pos_right h' x.prop⟩

lemma pos_mul_mono_rev.to_pos_mul_strict_mono [pos_mul_mono_rev α] : pos_mul_strict_mono α :=
⟨λ x a b h, lt_of_not_le $ λ h', h.not_le $ le_of_mul_le_mul_of_pos_left h' x.prop⟩

lemma mul_pos_mono_rev.to_mul_pos_strict_mono [mul_pos_mono_rev α] : mul_pos_strict_mono α :=
⟨λ x a b h, lt_of_not_le $ λ h', h.not_le $ le_of_mul_le_mul_of_pos_right h' x.prop⟩

lemma pos_mul_strict_mono_iff_pos_mul_mono_rev : pos_mul_strict_mono α ↔ pos_mul_mono_rev α :=
⟨@pos_mul_strict_mono.to_pos_mul_mono_rev _ _ _ _, @pos_mul_mono_rev.to_pos_mul_strict_mono _ _ _ _⟩

lemma mul_pos_strict_mono_iff_mul_pos_mono_rev : mul_pos_strict_mono α ↔ mul_pos_mono_rev α :=
⟨@mul_pos_strict_mono.to_mul_pos_mono_rev _ _ _ _, @mul_pos_mono_rev.to_mul_pos_strict_mono _ _ _ _⟩

lemma pos_mul_reflect_lt.to_pos_mul_mono [pos_mul_reflect_lt α] : pos_mul_mono α :=
⟨λ x a b h, le_of_not_lt $ λ h', h.not_lt $ lt_of_mul_lt_mul_left h' x.prop⟩

lemma mul_pos_reflect_lt.to_mul_pos_mono [mul_pos_reflect_lt α] : mul_pos_mono α :=
⟨λ x a b h, le_of_not_lt $ λ h', h.not_lt $ lt_of_mul_lt_mul_right h' x.prop⟩

lemma pos_mul_mono.to_pos_mul_reflect_lt [pos_mul_mono α] : pos_mul_reflect_lt α :=
⟨λ x a b h, lt_of_not_le $ λ h', h.not_le $ mul_le_mul_of_nonneg_left h' x.prop⟩

lemma mul_pos_mono.to_mul_pos_reflect_lt [mul_pos_mono α] : mul_pos_reflect_lt α :=
⟨λ x a b h, lt_of_not_le $ λ h', h.not_le $ mul_le_mul_of_nonneg_right h' x.prop⟩

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
lemma left.mul_pos [pos_mul_strict_mono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
by simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha

alias left.mul_pos ← mul_pos

lemma mul_neg_of_pos_of_neg [pos_mul_strict_mono α] (ha : 0 < a) (hb : b < 0) : a * b < 0 :=
by simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha

@[simp] lemma zero_lt_mul_left [pos_mul_strict_mono α] [pos_mul_reflect_lt α] (h : 0 < c) :
  0 < c * b ↔ 0 < b :=
by { convert mul_lt_mul_left h, simp }

/-- Assumes right covariance. -/
lemma right.mul_pos [mul_pos_strict_mono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
by simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb

lemma mul_neg_of_neg_of_pos [mul_pos_strict_mono α] (ha : a < 0) (hb : 0 < b) : a * b < 0 :=
by simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb

@[simp] lemma zero_lt_mul_right [mul_pos_strict_mono α] [mul_pos_reflect_lt α] (h : 0 < c) :
  0 < b * c ↔ 0 < b :=
by { convert mul_lt_mul_right h, simp }

/-- Assumes left covariance. -/
lemma left.mul_nonneg [pos_mul_mono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b :=
by simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha

alias left.mul_nonneg ← mul_nonneg

lemma mul_nonpos_of_nonneg_of_nonpos [pos_mul_mono α] (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 :=
by simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha

/-- Assumes right covariance. -/
lemma right.mul_nonneg [mul_pos_mono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b :=
by simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb

lemma mul_nonpos_of_nonpos_of_nonneg [mul_pos_mono α] (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 :=
by simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb

lemma pos_of_mul_pos_right [pos_mul_reflect_lt α] (h : 0 < a * b) (ha : 0 ≤ a) : 0 < b :=
lt_of_mul_lt_mul_left ((mul_zero a).symm ▸ h : a * 0 < a * b) ha

lemma pos_of_mul_pos_left [mul_pos_reflect_lt α] (h : 0 < a * b) (hb : 0 ≤ b) : 0 < a :=
lt_of_mul_lt_mul_right ((zero_mul b).symm ▸ h : 0 * b < a * b) hb

lemma pos_iff_pos_of_mul_pos [pos_mul_reflect_lt α] [mul_pos_reflect_lt α] (hab : 0 < a * b) :
  0 < a ↔ 0 < b :=
⟨pos_of_mul_pos_right hab ∘ le_of_lt, pos_of_mul_pos_left hab ∘ le_of_lt⟩

lemma mul_le_mul_of_le_of_le [pos_mul_mono α] [mul_pos_mono α]
  (h₁ : a ≤ b) (h₂ : c ≤ d) (a0 : 0 ≤ a) (d0 : 0 ≤ d) : a * c ≤ b * d :=
(mul_le_mul_of_nonneg_left h₂ a0).trans $ mul_le_mul_of_nonneg_right h₁ d0

lemma mul_le_mul [pos_mul_mono α] [mul_pos_mono α]
  (h₁ : a ≤ b) (h₂ : c ≤ d) (c0 : 0 ≤ c) (b0 : 0 ≤ b) : a * c ≤ b * d :=
(mul_le_mul_of_nonneg_right h₁ c0).trans $ mul_le_mul_of_nonneg_left h₂ b0

lemma mul_self_le_mul_self [pos_mul_mono α] [mul_pos_mono α] (ha : 0 ≤ a) (hab : a ≤ b) :
  a * a ≤ b * b :=
mul_le_mul hab hab ha $ ha.trans hab

lemma mul_le_of_mul_le_of_nonneg_left [pos_mul_mono α] (h : a * b ≤ c) (hle : d ≤ b) (a0 : 0 ≤ a) :
  a * d ≤ c :=
(mul_le_mul_of_nonneg_left hle a0).trans h

lemma le_mul_of_le_mul_of_nonneg_left [pos_mul_mono α] (h : a ≤ b * c) (hle : c ≤ d) (b0 : 0 ≤ b) :
  a ≤ b * d :=
h.trans (mul_le_mul_of_nonneg_left hle b0)

lemma mul_le_of_mul_le_of_nonneg_right [mul_pos_mono α] (h : a * b ≤ c) (hle : d ≤ a) (b0 : 0 ≤ b) :
  d * b ≤ c :=
(mul_le_mul_of_nonneg_right hle b0).trans h

lemma le_mul_of_le_mul_of_nonneg_right [mul_pos_mono α] (h : a ≤ b * c) (hle : b ≤ d) (c0 : 0 ≤ c) :
  a ≤ d * c :=
h.trans (mul_le_mul_of_nonneg_right hle c0)

end preorder

section partial_order
variables [partial_order α]

lemma pos_mul_mono_iff_covariant_pos : pos_mul_mono α ↔ covariant_class α>0 α (λ x y, x * y) (≤) :=
⟨@pos_mul_mono.to_covariant_class_pos_mul_le _ _ _ _, λ h, ⟨λ a b c h, begin
    obtain ha | ha := a.prop.eq_or_gt,
    { simp only [ha, zero_mul] },
    { exactI @covariant_class.elim α>0 α (λ x y, x * y) (≤) _ ⟨_, ha⟩ _ _ h }
  end⟩⟩

lemma mul_pos_mono_iff_covariant_pos : mul_pos_mono α ↔ covariant_class α>0 α (λ x y, y * x) (≤) :=
⟨@mul_pos_mono.to_covariant_class_pos_mul_le _ _ _ _, λ h, ⟨λ a b c h, begin
    obtain ha | ha := a.prop.eq_or_gt,
    { simp only [ha, mul_zero] },
    { exactI @covariant_class.elim α>0 α (λ x y, y * x) (≤) _ ⟨_, ha⟩ _ _ h }
  end⟩⟩

lemma pos_mul_reflect_lt_iff_contravariant_pos :
  pos_mul_reflect_lt α ↔ contravariant_class α>0 α (λ x y, x * y) (<) :=
⟨@pos_mul_reflect_lt.to_contravariant_class_pos_mul_lt _ _ _ _, λ h, ⟨λ a b c h, begin
    obtain ha | ha := a.prop.eq_or_gt,
    { simpa [ha] using h },
    { exactI (@contravariant_class.elim α>0 α (λ x y, x * y) (<) _ ⟨_, ha⟩ _ _ h) }
  end⟩⟩

lemma mul_pos_reflect_lt_iff_contravariant_pos :
  mul_pos_reflect_lt α ↔ contravariant_class α>0 α (λ x y, y * x) (<) :=
⟨@mul_pos_reflect_lt.to_contravariant_class_pos_mul_lt _ _ _ _, λ h, ⟨λ a b c h, begin
    obtain ha | ha := a.prop.eq_or_gt,
    { simpa [ha] using h },
    { exactI (@contravariant_class.elim α>0 α (λ x y, y * x) (<) _ ⟨_, ha⟩ _ _ h) }
  end⟩⟩

@[priority 100] -- see Note [lower instance priority]
instance pos_mul_strict_mono.to_pos_mul_mono [pos_mul_strict_mono α] : pos_mul_mono α :=
pos_mul_mono_iff_covariant_pos.2 $ ⟨λ a, strict_mono.monotone $ @covariant_class.elim _ _ _ _ _ _⟩

@[priority 100] -- see Note [lower instance priority]
instance mul_pos_strict_mono.to_mul_pos_mono [mul_pos_strict_mono α] : mul_pos_mono α :=
mul_pos_mono_iff_covariant_pos.2 $ ⟨λ a, strict_mono.monotone $ @covariant_class.elim _ _ _ _ _ _⟩

@[priority 100] -- see Note [lower instance priority]
instance pos_mul_mono_rev.to_pos_mul_reflect_lt [pos_mul_mono_rev α] : pos_mul_reflect_lt α :=
pos_mul_reflect_lt_iff_contravariant_pos.2
  ⟨λ a b c h, (le_of_mul_le_mul_of_pos_left h.le a.2).lt_of_ne $ by { rintro rfl, simpa using h }⟩

@[priority 100] -- see Note [lower instance priority]
instance mul_pos_mono_rev.to_mul_pos_reflect_lt [mul_pos_mono_rev α] : mul_pos_reflect_lt α :=
mul_pos_reflect_lt_iff_contravariant_pos.2
  ⟨λ a b c h, (le_of_mul_le_mul_of_pos_right h.le a.2).lt_of_ne $ by { rintro rfl, simpa using h }⟩

lemma mul_left_cancel_iff_of_pos [pos_mul_mono_rev α] (a0 : 0 < a) : a * b = a * c ↔ b = c :=
⟨λ h, (le_of_mul_le_mul_of_pos_left h.le a0).antisymm $ le_of_mul_le_mul_of_pos_left h.ge a0,
  congr_arg _⟩

lemma mul_right_cancel_iff_of_pos [mul_pos_mono_rev α] (b0 : 0 < b) : a * b = c * b ↔ a = c :=
⟨λ h, (le_of_mul_le_mul_of_pos_right h.le b0).antisymm $ le_of_mul_le_mul_of_pos_right h.ge b0,
  congr_arg _⟩

lemma mul_eq_mul_iff_eq_and_eq_of_pos [pos_mul_strict_mono α] [mul_pos_strict_mono α]
  [pos_mul_mono_rev α] [mul_pos_mono_rev α]
  (hac : a ≤ b) (hbd : c ≤ d) (a0 : 0 < a) (d0 : 0 < d) :
  a * c = b * d ↔ a = b ∧ c = d :=
begin
  refine ⟨λ h, _, λ h, congr_arg2 (*) h.1 h.2⟩,
  rcases hac.eq_or_lt with rfl | hac,
  { exact ⟨rfl, (mul_left_cancel_iff_of_pos a0).mp h⟩ },
  rcases eq_or_lt_of_le hbd with rfl | hbd,
  { exact ⟨(mul_right_cancel_iff_of_pos d0).mp h, rfl⟩ },
  exact ((mul_lt_mul_of_pos_of_pos hac hbd a0 d0).ne h).elim,
end

lemma mul_eq_mul_iff_eq_and_eq_of_pos' [pos_mul_strict_mono α] [mul_pos_strict_mono α]
  [pos_mul_mono_rev α] [mul_pos_mono_rev α]
  (hac : a ≤ b) (hbd : c ≤ d) (b0 : 0 < b) (c0 : 0 < c) :
  a * c = b * d ↔ a = b ∧ c = d :=
begin
  refine ⟨λ h, _, λ h, congr_arg2 (*) h.1 h.2⟩,
  rcases hac.eq_or_lt with rfl | hac,
  { exact ⟨rfl, (mul_left_cancel_iff_of_pos b0).mp h⟩ },
  rcases eq_or_lt_of_le hbd with rfl | hbd,
  { exact ⟨(mul_right_cancel_iff_of_pos c0).mp h, rfl⟩ },
  exact ((mul_lt_mul_of_lt_of_lt' hac hbd b0 c0).ne h).elim,
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
  (h : 0 < a * b) (ha : a ≤ 0) :
  b < 0 :=
((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left $ λ h, h.1.not_le ha).2

lemma neg_of_mul_pos_left [pos_mul_mono α] [mul_pos_mono α]
  (h : 0 < a * b) (ha : b ≤ 0) :
  a < 0 :=
((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left $ λ h, h.2.not_le ha).1

lemma neg_iff_neg_of_mul_pos [pos_mul_mono α] [mul_pos_mono α]
  (hab : 0 < a * b) :
  a < 0 ↔ b < 0 :=
⟨neg_of_mul_pos_right hab ∘ le_of_lt, neg_of_mul_pos_left hab ∘ le_of_lt⟩

lemma left.neg_of_mul_neg_left [pos_mul_mono α]
  (h : a * b < 0) (h1 : 0 ≤ a) :
  b < 0 :=
lt_of_not_ge (assume h2 : b ≥ 0, (left.mul_nonneg h1 h2).not_lt h)

lemma right.neg_of_mul_neg_left [mul_pos_mono α]
  (h : a * b < 0) (h1 : 0 ≤ a) :
  b < 0 :=
lt_of_not_ge (assume h2 : b ≥ 0, (right.mul_nonneg h1 h2).not_lt h)

lemma left.neg_of_mul_neg_right [pos_mul_mono α]
  (h : a * b < 0) (h1 : 0 ≤ b) : a < 0 :=
lt_of_not_ge (assume h2 : a ≥ 0, (left.mul_nonneg h2 h1).not_lt h)

lemma right.neg_of_mul_neg_right [mul_pos_mono α]
  (h : a * b < 0) (h1 : 0 ≤ b) : a < 0 :=
lt_of_not_ge (assume h2 : a ≥ 0, (right.mul_nonneg h2 h1).not_lt h)

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
iff.trans (by rw [mul_one]) (mul_le_mul_left a0)

@[simp]
lemma lt_mul_iff_one_lt_right
  [pos_mul_strict_mono α] [pos_mul_reflect_lt α]
  (a0 : 0 < a) :
  a < a * b ↔ 1 < b :=
iff.trans (by rw [mul_one]) (mul_lt_mul_left a0)

@[simp]
lemma mul_le_iff_le_one_right
  [pos_mul_mono α] [pos_mul_mono_rev α]
  (a0 : 0 < a) :
  a * b ≤ a ↔ b ≤ 1 :=
iff.trans (by rw [mul_one]) (mul_le_mul_left a0)

@[simp]
lemma mul_lt_iff_lt_one_right
  [pos_mul_strict_mono α] [pos_mul_reflect_lt α]
  (a0 : 0 < a) :
  a * b < a ↔ b < 1 :=
iff.trans (by rw [mul_one]) (mul_lt_mul_left a0)

/-! Lemmas of the form `a ≤ b * a ↔ 1 ≤ b` and `a * b ≤ b ↔ a ≤ 1`,
which assume right covariance. -/

@[simp]
lemma le_mul_iff_one_le_left
  [mul_pos_mono α] [mul_pos_mono_rev α]
  (a0 : 0 < a) :
  a ≤ b * a ↔ 1 ≤ b :=
iff.trans (by rw [one_mul]) (mul_le_mul_right a0)

@[simp]
lemma lt_mul_iff_one_lt_left
  [mul_pos_strict_mono α] [mul_pos_reflect_lt α]
  (a0 : 0 < a) :
  a < b * a ↔ 1 < b :=
iff.trans (by rw [one_mul]) (mul_lt_mul_right a0)

@[simp]
lemma mul_le_iff_le_one_left
  [mul_pos_mono α] [mul_pos_mono_rev α]
  (b0 : 0 < b) :
  a * b ≤ b ↔ a ≤ 1 :=
iff.trans (by rw [one_mul]) (mul_le_mul_right b0)

@[simp]
lemma mul_lt_iff_lt_one_left
  [mul_pos_strict_mono α] [mul_pos_reflect_lt α]
  (b0 : 0 < b) :
  a * b < b ↔ a < 1 :=
iff.trans (by rw [one_mul]) (mul_lt_mul_right b0)

/-! Lemmas of the form `1 ≤ b → a ≤ a * b`. -/

lemma mul_le_of_le_one_left [mul_pos_mono α] (hb : 0 ≤ b) (h : a ≤ 1) : a * b ≤ b :=
by simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb

lemma le_mul_of_one_le_left [mul_pos_mono α] (hb : 0 ≤ b) (h : 1 ≤ a) : b ≤ a * b :=
by simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb

lemma mul_le_of_le_one_right [pos_mul_mono α] (ha : 0 ≤ a) (h : b ≤ 1) : a * b ≤ a :=
by simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha

lemma le_mul_of_one_le_right [pos_mul_mono α] (ha : 0 ≤ a) (h : 1 ≤ b) : a ≤ a * b :=
by simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha

lemma mul_lt_of_lt_one_left [mul_pos_strict_mono α] (hb : 0 < b) (h : a < 1) : a * b < b :=
by simpa only [one_mul] using mul_lt_mul_of_pos_right h hb

lemma lt_mul_of_one_lt_left [mul_pos_strict_mono α] (hb : 0 < b) (h : 1 < a) : b < a * b :=
by simpa only [one_mul] using mul_lt_mul_of_pos_right h hb

lemma mul_lt_of_lt_one_right [pos_mul_strict_mono α] (ha : 0 < a) (h : b < 1) : a * b < a :=
by simpa only [mul_one] using mul_lt_mul_of_pos_left h ha

lemma lt_mul_of_one_lt_right [pos_mul_strict_mono α] (ha : 0 < a) (h : 1 < b) : a < a * b :=
by simpa only [mul_one] using mul_lt_mul_of_pos_left h ha

/-! Lemmas of the form `b ≤ c → a ≤ 1 → b * a ≤ c`. -/
/- Yaël: What's the point of these lemmas? They just chain an existing lemma with an assumption in
all possible ways, thereby artificially inflating the API and making the truly relevant lemmas hard
to find -/

lemma mul_le_of_le_of_le_one_of_nonneg [pos_mul_mono α] (h : b ≤ c) (ha : a ≤ 1) (hb : 0 ≤ b) :
  b * a ≤ c :=
(mul_le_of_le_one_right hb ha).trans h

lemma mul_lt_of_le_of_lt_one_of_pos [pos_mul_strict_mono α] (bc : b ≤ c) (ha : a < 1) (b0 : 0 < b) :
  b * a < c :=
(mul_lt_of_lt_one_right b0 ha).trans_le bc

lemma mul_lt_of_lt_of_le_one_of_nonneg [pos_mul_mono α] (h : b < c) (ha : a ≤ 1) (hb : 0 ≤ b) :
  b * a < c :=
(mul_le_of_le_one_right hb ha).trans_lt h

/-- Assumes left covariance. -/
lemma left.mul_le_one_of_le_of_le [pos_mul_mono α] (ha : a ≤ 1) (hb : b ≤ 1) (a0 : 0 ≤ a) :
  a * b ≤ 1 :=
mul_le_of_le_of_le_one_of_nonneg ha hb a0

/-- Assumes left covariance. -/
lemma left.mul_lt_of_le_of_lt_one_of_pos [pos_mul_strict_mono α]
  (ha : a ≤ 1) (hb : b < 1) (a0 : 0 < a) : a * b < 1 :=
mul_lt_of_le_of_lt_one_of_pos ha hb a0

/-- Assumes left covariance. -/
lemma left.mul_lt_of_lt_of_le_one_of_nonneg [pos_mul_mono α]
  (ha : a < 1) (hb : b ≤ 1) (a0 : 0 ≤ a) : a * b < 1 :=
mul_lt_of_lt_of_le_one_of_nonneg ha hb a0

lemma mul_le_of_le_of_le_one' [pos_mul_mono α] [mul_pos_mono α]
  (bc : b ≤ c) (ha : a ≤ 1) (a0 : 0 ≤ a) (c0 : 0 ≤ c) : b * a ≤ c :=
(mul_le_mul_of_nonneg_right bc a0).trans $ mul_le_of_le_one_right c0 ha

lemma mul_lt_of_lt_of_le_one' [pos_mul_mono α] [mul_pos_strict_mono α]
  (bc : b < c) (ha : a ≤ 1) (a0 : 0 < a) (c0 : 0 ≤ c) : b * a < c :=
(mul_lt_mul_of_pos_right bc a0).trans_le $ mul_le_of_le_one_right c0 ha

lemma mul_lt_of_le_of_lt_one' [pos_mul_strict_mono α] [mul_pos_mono α]
  (bc : b ≤ c) (ha : a < 1) (a0 : 0 ≤ a) (c0 : 0 < c) : b * a < c :=
(mul_le_mul_of_nonneg_right bc a0).trans_lt $ mul_lt_of_lt_one_right c0 ha

lemma mul_lt_of_lt_of_lt_one_of_pos [pos_mul_mono α] [mul_pos_strict_mono α]
  (bc : b < c) (ha : a ≤ 1) (a0 : 0 < a) (c0 : 0 ≤ c) : b * a < c :=
(mul_lt_mul_of_pos_right bc a0).trans_le $ mul_le_of_le_one_right c0 ha

/-! Lemmas of the form `b ≤ c → 1 ≤ a → b ≤ c * a`. -/

lemma le_mul_of_le_of_one_le_of_nonneg [pos_mul_mono α] (h : b ≤ c) (ha : 1 ≤ a) (hc : 0 ≤ c) :
  b ≤ c * a :=
h.trans $ le_mul_of_one_le_right hc ha

lemma lt_mul_of_le_of_one_lt_of_pos [pos_mul_strict_mono α] (bc : b ≤ c) (ha : 1 < a) (c0 : 0 < c) :
  b < c * a :=
bc.trans_lt $ lt_mul_of_one_lt_right c0 ha

lemma lt_mul_of_lt_of_one_le_of_nonneg [pos_mul_mono α] (h : b < c) (ha : 1 ≤ a) (hc : 0 ≤ c) :
  b < c * a :=
h.trans_le $ le_mul_of_one_le_right hc ha

/-- Assumes left covariance. -/
lemma left.one_le_mul_of_le_of_le [pos_mul_mono α] (ha : 1 ≤ a) (hb : 1 ≤ b) (a0 : 0 ≤ a) :
  1 ≤ a * b :=
le_mul_of_le_of_one_le_of_nonneg ha hb a0

/-- Assumes left covariance. -/
lemma left.one_lt_mul_of_le_of_lt_of_pos [pos_mul_strict_mono α]
  (ha : 1 ≤ a) (hb : 1 < b) (a0 : 0 < a) : 1 < a * b :=
lt_mul_of_le_of_one_lt_of_pos ha hb a0

/-- Assumes left covariance. -/
lemma left.lt_mul_of_lt_of_one_le_of_nonneg [pos_mul_mono α]
  (ha : 1 < a) (hb : 1 ≤ b) (a0 : 0 ≤ a) : 1 < a * b :=
lt_mul_of_lt_of_one_le_of_nonneg ha hb a0

lemma le_mul_of_le_of_one_le' [pos_mul_mono α] [mul_pos_mono α]
  (bc : b ≤ c) (ha : 1 ≤ a) (a0 : 0 ≤ a) (b0 : 0 ≤ b) : b ≤ c * a :=
(le_mul_of_one_le_right b0 ha).trans $ mul_le_mul_of_nonneg_right bc a0

lemma lt_mul_of_le_of_one_lt' [pos_mul_strict_mono α] [mul_pos_mono α]
  (bc : b ≤ c) (ha : 1 < a) (a0 : 0 ≤ a) (b0 : 0 < b) : b < c * a :=
(lt_mul_of_one_lt_right b0 ha).trans_le $ mul_le_mul_of_nonneg_right bc a0

lemma lt_mul_of_lt_of_one_le' [pos_mul_mono α] [mul_pos_strict_mono α]
  (bc : b < c) (ha : 1 ≤ a) (a0 : 0 < a) (b0 : 0 ≤ b) : b < c * a :=
(le_mul_of_one_le_right b0 ha).trans_lt $ mul_lt_mul_of_pos_right bc a0

lemma lt_mul_of_lt_of_one_lt_of_pos [pos_mul_strict_mono α] [mul_pos_strict_mono α]
  (bc : b < c) (ha : 1 < a) (a0 : 0 < a) (b0 : 0 < b) : b < c * a :=
(lt_mul_of_one_lt_right b0 ha).trans $ mul_lt_mul_of_pos_right bc a0

/-! Lemmas of the form `a ≤ 1 → b ≤ c → a * b ≤ c`. -/

lemma mul_le_of_le_one_of_le_of_nonneg [mul_pos_mono α] (ha : a ≤ 1) (h : b ≤ c) (hb : 0 ≤ b) :
  a * b ≤ c :=
(mul_le_of_le_one_left hb ha).trans h

lemma mul_lt_of_lt_one_of_le_of_pos [mul_pos_strict_mono α] (ha : a < 1) (h : b ≤ c) (hb : 0 < b) :
  a * b < c :=
(mul_lt_of_lt_one_left hb ha).trans_le h

lemma mul_lt_of_le_one_of_lt_of_nonneg [mul_pos_mono α] (ha : a ≤ 1) (h : b < c) (hb : 0 ≤ b) :
  a * b < c :=
(mul_le_of_le_one_left hb ha).trans_lt h

/-- Assumes right covariance. -/
lemma right.mul_lt_one_of_lt_of_le_of_pos [mul_pos_strict_mono α]
  (ha : a < 1) (hb : b ≤ 1) (b0 : 0 < b) : a * b < 1 :=
mul_lt_of_lt_one_of_le_of_pos ha hb b0

/-- Assumes right covariance. -/
lemma right.mul_lt_one_of_le_of_lt_of_nonneg [mul_pos_mono α]
  (ha : a ≤ 1) (hb : b < 1) (b0 : 0 ≤ b) : a * b < 1 :=
mul_lt_of_le_one_of_lt_of_nonneg ha hb b0

lemma mul_lt_of_lt_one_of_lt_of_pos [pos_mul_strict_mono α] [mul_pos_strict_mono α]
  (ha : a < 1) (bc : b < c) (a0 : 0 < a) (c0 : 0 < c) : a * b < c :=
(mul_lt_mul_of_pos_left bc a0).trans $ mul_lt_of_lt_one_left c0 ha

/-- Assumes right covariance. -/
lemma right.mul_le_one_of_le_of_le [mul_pos_mono α]
  (ha : a ≤ 1) (hb : b ≤ 1) (b0 : 0 ≤ b) : a * b ≤ 1 :=
mul_le_of_le_one_of_le_of_nonneg ha hb b0

lemma mul_le_of_le_one_of_le' [pos_mul_mono α] [mul_pos_mono α]
  (ha : a ≤ 1) (bc : b ≤ c) (a0 : 0 ≤ a) (c0 : 0 ≤ c) : a * b ≤ c :=
(mul_le_mul_of_nonneg_left bc a0).trans $ mul_le_of_le_one_left c0 ha

lemma mul_lt_of_lt_one_of_le' [pos_mul_mono α] [mul_pos_strict_mono α]
  (ha : a < 1) (bc : b ≤ c) (a0 : 0 ≤ a) (c0 : 0 < c) : a * b < c :=
(mul_le_mul_of_nonneg_left bc a0).trans_lt $ mul_lt_of_lt_one_left c0 ha

lemma mul_lt_of_le_one_of_lt' [pos_mul_strict_mono α] [mul_pos_mono α]
  (ha : a ≤ 1) (bc : b < c) (a0 : 0 < a) (c0 : 0 ≤ c) : a * b < c :=
(mul_lt_mul_of_pos_left bc a0).trans_le $ mul_le_of_le_one_left c0 ha

/-! Lemmas of the form `1 ≤ a → b ≤ c → b ≤ a * c`. -/

lemma lt_mul_of_one_lt_of_le_of_pos [mul_pos_strict_mono α] (ha : 1 < a) (h : b ≤ c) (hc : 0 < c) :
  b < a * c :=
h.trans_lt $ lt_mul_of_one_lt_left hc ha

lemma lt_mul_of_one_le_of_lt_of_nonneg [mul_pos_mono α] (ha : 1 ≤ a) (h : b < c) (hc : 0 ≤ c) :
  b < a * c :=
h.trans_le $ le_mul_of_one_le_left hc ha

lemma lt_mul_of_one_lt_of_lt_of_pos [mul_pos_strict_mono α] (ha : 1 < a) (h : b < c) (hc : 0 < c) :
  b < a * c :=
h.trans $ lt_mul_of_one_lt_left hc ha

/-- Assumes right covariance. -/
lemma right.one_lt_mul_of_lt_of_le_of_pos [mul_pos_strict_mono α]
  (ha : 1 < a) (hb : 1 ≤ b) (b0 : 0 < b) : 1 < a * b :=
lt_mul_of_one_lt_of_le_of_pos ha hb b0

/-- Assumes right covariance. -/
lemma right.one_lt_mul_of_le_of_lt_of_nonneg [mul_pos_mono α]
  (ha : 1 ≤ a) (hb : 1 < b) (b0 : 0 ≤ b) : 1 < a * b :=
lt_mul_of_one_le_of_lt_of_nonneg ha hb b0

/-- Assumes right covariance. -/
lemma right.one_lt_mul_of_lt_of_lt [mul_pos_strict_mono α]
  (ha : 1 < a) (hb : 1 < b) (b0 : 0 < b) : 1 < a * b :=
lt_mul_of_one_lt_of_lt_of_pos ha hb b0

lemma lt_mul_of_one_lt_of_lt_of_nonneg [mul_pos_mono α] (ha : 1 ≤ a) (h : b < c) (hc : 0 ≤ c) :
  b < a * c :=
h.trans_le $ le_mul_of_one_le_left hc ha

lemma lt_of_mul_lt_of_one_le_of_nonneg_left [pos_mul_mono α] (h : a * b < c) (hle : 1 ≤ b)
  (ha : 0 ≤ a) :
  a < c :=
(le_mul_of_one_le_right ha hle).trans_lt h

lemma lt_of_lt_mul_of_le_one_of_nonneg_left [pos_mul_mono α] (h : a < b * c) (hc : c ≤ 1)
  (hb : 0 ≤ b) :
  a < b :=
h.trans_le $ mul_le_of_le_one_right hb hc

lemma lt_of_lt_mul_of_le_one_of_nonneg_right [mul_pos_mono α] (h : a < b * c) (hb : b ≤ 1)
  (hc : 0 ≤ c) :
  a < c :=
h.trans_le $ mul_le_of_le_one_left hc hb

lemma le_mul_of_one_le_of_le_of_nonneg [mul_pos_mono α] (ha : 1 ≤ a) (bc : b ≤ c) (c0 : 0 ≤ c) :
  b ≤ a * c :=
bc.trans $ le_mul_of_one_le_left c0 ha

/-- Assumes right covariance. -/
lemma right.one_le_mul_of_le_of_le [mul_pos_mono α] (ha : 1 ≤ a) (hb : 1 ≤ b) (b0 : 0 ≤ b) :
  1 ≤ a * b :=
le_mul_of_one_le_of_le_of_nonneg ha hb b0

lemma le_of_mul_le_of_one_le_of_nonneg_left [pos_mul_mono α] (h : a * b ≤ c) (hb : 1 ≤ b)
  (ha : 0 ≤ a) :
  a ≤ c :=
(le_mul_of_one_le_right ha hb).trans h

lemma le_of_le_mul_of_le_one_of_nonneg_left [pos_mul_mono α] (h : a ≤ b * c) (hc : c ≤ 1)
  (hb : 0 ≤ b) :
  a ≤ b :=
h.trans $ mul_le_of_le_one_right hb hc

lemma le_of_mul_le_of_one_le_nonneg_right [mul_pos_mono α] (h : a * b ≤ c) (ha : 1 ≤ a)
  (hb : 0 ≤ b) :
  b ≤ c :=
(le_mul_of_one_le_left hb ha).trans h

lemma le_of_le_mul_of_le_one_of_nonneg_right [mul_pos_mono α] (h : a ≤ b * c) (hb : b ≤ 1)
  (hc : 0 ≤ c) :
  a ≤ c :=
h.trans $ mul_le_of_le_one_left hc hb

end preorder

section linear_order
variables [linear_order α]

-- Yaël: What's the point of this lemma? If we have `0 * 0 = 0`, then we can just take `b = 0`.
-- proven with `a0 : 0 ≤ a` as `exists_square_le`
lemma exists_square_le' [pos_mul_strict_mono α] (a0 : 0 < a) : ∃ (b : α), b * b ≤ a :=
begin
  obtain ha | ha := lt_or_le a 1,
  { exact ⟨a, (mul_lt_of_lt_one_right a0 ha).le⟩ },
  { exact ⟨1, by rwa mul_one⟩ }
end

end linear_order
end mul_one_class

section cancel_monoid_with_zero

variables [cancel_monoid_with_zero α]

section partial_order
variables [partial_order α]

lemma pos_mul_mono.to_pos_mul_strict_mono [pos_mul_mono α] : pos_mul_strict_mono α :=
⟨λ x a b h, (mul_le_mul_of_nonneg_left h.le x.2.le).lt_of_ne (h.ne ∘ mul_left_cancel₀ x.2.ne')⟩

lemma pos_mul_mono_iff_pos_mul_strict_mono : pos_mul_mono α ↔ pos_mul_strict_mono α :=
⟨@pos_mul_mono.to_pos_mul_strict_mono α _ _, @pos_mul_strict_mono.to_pos_mul_mono α _ _⟩

lemma mul_pos_mono.to_mul_pos_strict_mono [mul_pos_mono α] : mul_pos_strict_mono α :=
⟨λ x a b h, (mul_le_mul_of_nonneg_right h.le x.2.le).lt_of_ne (h.ne ∘ mul_right_cancel₀ x.2.ne')⟩

lemma mul_pos_mono_iff_mul_pos_strict_mono : mul_pos_mono α ↔ mul_pos_strict_mono α :=
⟨@mul_pos_mono.to_mul_pos_strict_mono α _ _, @mul_pos_strict_mono.to_mul_pos_mono α _ _⟩

lemma pos_mul_reflect_lt.to_pos_mul_mono_rev [pos_mul_reflect_lt α] : pos_mul_mono_rev α :=
⟨λ x a b h, h.eq_or_lt.elim (le_of_eq ∘ mul_left_cancel₀ x.2.ne.symm)
                            (λ h', (lt_of_mul_lt_mul_left h' x.2.le).le)⟩

lemma pos_mul_mono_rev_iff_pos_mul_reflect_lt : pos_mul_mono_rev α ↔ pos_mul_reflect_lt α :=
⟨@pos_mul_mono_rev.to_pos_mul_reflect_lt α _ _, @pos_mul_reflect_lt.to_pos_mul_mono_rev α _ _⟩

lemma mul_pos_reflect_lt.to_mul_pos_mono_rev [mul_pos_reflect_lt α] : mul_pos_mono_rev α :=
⟨λ x a b h, h.eq_or_lt.elim (le_of_eq ∘ mul_right_cancel₀ x.2.ne.symm)
                            (λ h', (lt_of_mul_lt_mul_right h' x.2.le).le)⟩

lemma mul_pos_mono_rev_iff_mul_pos_reflect_lt : mul_pos_mono_rev α ↔ mul_pos_reflect_lt α :=
⟨@mul_pos_mono_rev.to_mul_pos_reflect_lt α _ _, @mul_pos_reflect_lt.to_mul_pos_mono_rev α _ _⟩

end partial_order

end cancel_monoid_with_zero

section comm_semigroup_has_zero
variables [comm_semigroup α] [has_zero α] [preorder α]

lemma pos_mul_strict_mono_iff_mul_pos_strict_mono :
  pos_mul_strict_mono α ↔ mul_pos_strict_mono α :=
by simp ! only [mul_comm]

lemma pos_mul_reflect_lt_iff_mul_pos_reflect_lt :
  pos_mul_reflect_lt α ↔ mul_pos_reflect_lt α :=
by simp ! only [mul_comm]

lemma pos_mul_mono_iff_mul_pos_mono :
  pos_mul_mono α ↔ mul_pos_mono α :=
by simp ! only [mul_comm]

lemma pos_mul_mono_rev_iff_mul_pos_mono_rev :
  pos_mul_mono_rev α ↔ mul_pos_mono_rev α :=
by simp ! only [mul_comm]

end comm_semigroup_has_zero
