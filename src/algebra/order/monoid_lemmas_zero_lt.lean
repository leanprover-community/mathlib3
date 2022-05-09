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

variables {a b c d : α}

section has_mul_zero
variables [has_mul α] [has_zero α]

section has_lt
variables [has_lt α]

lemma mul_lt_mul_left' [pos_mul_strict_mono α]
  (bc : b < c) (a0 : 0 < a) :
  a * b < a * c :=
@covariant_class.elim α>0 α (λ x y, x * y) (<) _ ⟨a, a0⟩ _ _ bc

lemma mul_lt_mul_right' [mul_pos_strict_mono α]
  (bc : b < c) (a0 : 0 < a) :
  b * a < c * a :=
@covariant_class.elim α>0 α (λ x y, y * x) (<) _ ⟨a, a0⟩ _ _ bc

-- proven with `a0 : 0 ≤ a` as `lt_of_mul_lt_mul_left''`
lemma lt_of_mul_lt_mul_left' [pos_mul_reflect_lt α]
  (bc : a * b < a * c) (a0 : 0 < a) :
  b < c :=
@contravariant_class.elim α>0 α (λ x y, x * y) (<) _ ⟨a, a0⟩ _ _ bc

-- proven with `a0 : 0 ≤ a` as `lt_of_mul_lt_mul_right''`
lemma lt_of_mul_lt_mul_right' [mul_pos_reflect_lt α]
  (bc : b * a < c * a) (a0 : 0 < a) :
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

section preorder
variables [preorder α]

lemma mul_le_mul_left' [pos_mul_mono α]
  (bc : b ≤ c) (a0 : 0 < a) :
  a * b ≤ a * c :=
@covariant_class.elim α>0 α (λ x y, x * y) (≤) _ ⟨a, a0⟩ _ _ bc

lemma mul_le_mul_right' [mul_pos_mono α]
  (bc : b ≤ c) (a0 : 0 < a) :
  b * a ≤ c * a :=
@covariant_class.elim α>0 α (λ x y, y * x) (≤) _ ⟨a, a0⟩ _ _ bc

lemma le_of_mul_le_mul_left' [pos_mul_mono_rev α]
  (bc : a * b ≤ a * c) (a0 : 0 < a) :
  b ≤ c :=
@contravariant_class.elim α>0 α (λ x y, x * y) (≤) _ ⟨a, a0⟩ _ _ bc

lemma le_of_mul_le_mul_right' [mul_pos_mono_rev α]
  (bc : b * a ≤ c * a) (a0 : 0 < a) :
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

-- proven with `a0 : 0 ≤ a` `d0 : 0 ≤ d` as `mul_le_mul_of_le_of_le''`
lemma mul_le_mul_of_le_of_le [pos_mul_mono α] [mul_pos_mono α]
  (h₁ : a ≤ b) (h₂ : c ≤ d) (a0 : 0 < a) (d0 : 0 < d) : a * c ≤ b * d :=
(mul_le_mul_left' h₂ a0).trans (mul_le_mul_right' h₁ d0)

-- proven with `b0 : 0 ≤ b` `c0 : 0 ≤ c` as `mul_le_mul_of_le_of_le'''`
lemma mul_le_mul_of_le_of_le' [pos_mul_mono α] [mul_pos_mono α]
  (h₁ : a ≤ b) (h₂ : c ≤ d) (b0 : 0 < b) (c0 : 0 < c) : a * c ≤ b * d :=
(mul_le_mul_right' h₁ c0).trans (mul_le_mul_left' h₂ b0)

lemma mul_lt_mul_of_le_of_lt [pos_mul_strict_mono α] [mul_pos_mono α]
  (h₁ : a ≤ b) (h₂ : c < d) (a0 : 0 < a) (d0 : 0 < d) : a * c < b * d :=
(mul_lt_mul_left' h₂ a0).trans_le (mul_le_mul_right' h₁ d0)

lemma mul_lt_mul_of_le_of_lt' [pos_mul_strict_mono α] [mul_pos_mono α]
  (h₁ : a ≤ b) (h₂ : c < d) (b0 : 0 < b) (c0 : 0 < c) : a * c < b * d :=
(mul_le_mul_right' h₁ c0).trans_lt (mul_lt_mul_left' h₂ b0)

lemma mul_lt_mul_of_lt_of_le [pos_mul_mono α] [mul_pos_strict_mono α]
  (h₁ : a < b) (h₂ : c ≤ d) (a0 : 0 < a) (d0 : 0 < d) : a * c < b * d :=
(mul_le_mul_left' h₂ a0).trans_lt (mul_lt_mul_right' h₁ d0)

lemma mul_lt_mul_of_lt_of_le' [pos_mul_mono α] [mul_pos_strict_mono α]
  (h₁ : a < b) (h₂ : c ≤ d) (b0 : 0 < b) (c0 : 0 < c) : a * c < b * d :=
(mul_lt_mul_right' h₁ c0).trans_le (mul_le_mul_left' h₂ b0)

lemma mul_lt_mul_of_lt_of_lt [pos_mul_strict_mono α] [mul_pos_strict_mono α]
  (h₁ : a < b) (h₂ : c < d) (a0 : 0 < a) (d0 : 0 < d) : a * c < b * d :=
(mul_lt_mul_left' h₂ a0).trans (mul_lt_mul_right' h₁ d0)

lemma mul_lt_mul_of_lt_of_lt' [pos_mul_strict_mono α] [mul_pos_strict_mono α]
  (h₁ : a < b) (h₂ : c < d) (b0 : 0 < b) (c0 : 0 < c) : a * c < b * d :=
(mul_lt_mul_right' h₁ c0).trans (mul_lt_mul_left' h₂ b0)

-- proven with `a0 : 0 ≤ a` as `mul_le_of_mul_le_left'`
lemma mul_le_of_mul_le_left [pos_mul_mono α]
  (h : a * b ≤ c) (hle : d ≤ b) (a0 : 0 < a) :
  a * d ≤ c :=
(mul_le_mul_left' hle a0).trans h

lemma mul_lt_of_mul_lt_left [pos_mul_mono α]
  (h : a * b < c) (hle : d ≤ b) (a0 : 0 < a) :
  a * d < c :=
(mul_le_mul_left' hle a0).trans_lt h

-- proven with `b0 : 0 ≤ b` as `le_mul_of_le_mul_left'`
lemma le_mul_of_le_mul_left [pos_mul_mono α]
  (h : a ≤ b * c) (hle : c ≤ d) (b0 : 0 < b) :
  a ≤ b * d :=
h.trans (mul_le_mul_left' hle b0)

lemma lt_mul_of_lt_mul_left [pos_mul_mono α]
  (h : a < b * c) (hle : c ≤ d) (b0 : 0 < b) :
  a < b * d :=
h.trans_le (mul_le_mul_left' hle b0)

-- proven with `b0 : 0 ≤ b` as `mul_le_of_mul_le_right'`
lemma mul_le_of_mul_le_right [mul_pos_mono α]
  (h : a * b ≤ c) (hle : d ≤ a) (b0 : 0 < b) :
  d * b ≤ c :=
(mul_le_mul_right' hle b0).trans h

lemma mul_lt_of_mul_lt_right [mul_pos_mono α]
  (h : a * b < c) (hle : d ≤ a) (b0 : 0 < b) :
  d * b < c :=
(mul_le_mul_right' hle b0).trans_lt h

-- proven with `c0 : 0 ≤ c` as `le_mul_of_le_mul_right'`
lemma le_mul_of_le_mul_right [mul_pos_mono α]
  (h : a ≤ b * c) (hle : b ≤ d) (c0 : 0 < c) :
  a ≤ d * c :=
h.trans (mul_le_mul_right' hle c0)

lemma lt_mul_of_lt_mul_right [mul_pos_mono α]
  (h : a < b * c) (hle : b ≤ d) (c0 : 0 < c) :
  a < d * c :=
h.trans_le (mul_le_mul_right' hle c0)

end preorder

section partial_order
variables [partial_order α]

@[priority 100] -- see Note [lower instance priority]
instance pos_mul_strict_mono.to_pos_mul_mono [pos_mul_strict_mono α] : pos_mul_mono α :=
⟨λ x a b h, h.eq_or_lt.elim (λ h', h' ▸ le_rfl) (λ h', (mul_lt_mul_left' h' x.prop).le)⟩

@[priority 100] -- see Note [lower instance priority]
instance mul_pos_strict_mono.to_mul_pos_mono [mul_pos_strict_mono α] : mul_pos_mono α :=
⟨λ x a b h, h.eq_or_lt.elim (λ h', h' ▸ le_rfl) (λ h', (mul_lt_mul_right' h' x.prop).le)⟩

@[priority 100] -- see Note [lower instance priority]
instance pos_mul_mono_rev.to_pos_mul_reflect_lt [pos_mul_mono_rev α] : pos_mul_reflect_lt α :=
⟨λ x a b h, lt_of_le_of_ne (le_of_mul_le_mul_left' h.le x.prop) (λ h', by simpa [h'] using h)⟩

@[priority 100] -- see Note [lower instance priority]
instance mul_pos_mono_rev.to_mul_pos_reflect_lt [mul_pos_mono_rev α] : mul_pos_reflect_lt α :=
⟨λ x a b h, lt_of_le_of_ne (le_of_mul_le_mul_right' h.le x.prop) (λ h', by simpa [h'] using h)⟩

end partial_order

section linear_order
variables [linear_order α]

@[priority 100] -- see Note [lower instance priority]
instance pos_mul_strict_mono.to_pos_mul_mono_rev [pos_mul_strict_mono α] : pos_mul_mono_rev α :=
⟨λ x a b h, le_of_not_lt $ λ h', h.not_lt (mul_lt_mul_left' h' x.prop)⟩

@[priority 100] -- see Note [lower instance priority]
instance mul_pos_strict_mono.to_mul_pos_mono_rev [mul_pos_strict_mono α] : mul_pos_mono_rev α :=
⟨λ x a b h, le_of_not_lt $ λ h', h.not_lt (mul_lt_mul_right' h' x.prop)⟩

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
have h : a * 0 < a * b, from mul_lt_mul_left' hb ha,
by rwa [mul_zero] at h

lemma mul_neg_of_pos_of_neg [pos_mul_strict_mono α]
  (ha : 0 < a) (hb : b < 0) :
  a * b < 0 :=
have h : a * b < a * 0, from mul_lt_mul_left' hb ha,
by rwa [mul_zero] at h

/-- Assumes right covariance. -/
lemma right.mul_pos [mul_pos_strict_mono α]
  (ha : 0 < a) (hb : 0 < b) :
  0 < a * b :=
have h : 0 * b < a * b, from mul_lt_mul_right' ha hb,
by rwa [zero_mul] at h

lemma mul_neg_of_neg_of_pos [mul_pos_strict_mono α]
  (ha : a < 0) (hb : 0 < b) :
  a * b < 0 :=
have h : a * b < 0 * b, from mul_lt_mul_right' ha hb,
by rwa [zero_mul] at h

end preorder

section partial_order
variables [partial_order α]

lemma mul_le_mul_left'' [pos_mul_mono α]
  (bc : b ≤ c) (a0 : 0 ≤ a) :
  a * b ≤ a * c :=
a0.lt_or_eq.elim (mul_le_mul_left' bc) (λ h, by simp only [← h, zero_mul])

lemma mul_le_mul_right'' [mul_pos_mono α]
  (bc : b ≤ c) (a0 : 0 ≤ a) :
  b * a ≤ c * a :=
a0.lt_or_eq.elim (mul_le_mul_right' bc) (λ h, by simp only [← h, mul_zero])

/-- Assumes left covariance. -/
lemma left.mul_nonneg [pos_mul_mono α]
  (ha : 0 ≤ a) (hb : 0 ≤ b) :
  0 ≤ a * b :=
have h : a * 0 ≤ a * b, from mul_le_mul_left'' hb ha,
by rwa [mul_zero] at h

lemma mul_nonpos_of_nonneg_of_nonpos [pos_mul_mono α]
  (ha : 0 ≤ a) (hb : b ≤ 0) :
  a * b ≤ 0 :=
have h : a * b ≤ a * 0, from mul_le_mul_left'' hb ha,
by rwa [mul_zero] at h

/-- Assumes right covariance. -/
lemma right.mul_nonneg [mul_pos_mono α]
  (ha : 0 ≤ a) (hb : 0 ≤ b) :
  0 ≤ a * b :=
have h : 0 * b ≤ a * b, from mul_le_mul_right'' ha hb,
by rwa [zero_mul] at h

lemma mul_nonpos_of_nonpos_of_nonneg [mul_pos_mono α]
  (ha : a ≤ 0) (hb : 0 ≤ b) :
  a * b ≤ 0 :=
have h : a * b ≤ 0 * b, from mul_le_mul_right'' ha hb,
by rwa [zero_mul] at h

lemma lt_of_mul_lt_mul_left'' [pos_mul_reflect_lt α]
  (bc : a * b < a * c) (a0 : 0 ≤ a) :
  b < c :=
begin
  by_cases a₀ : a = 0,
  { exact (lt_irrefl (0 : α) (by simpa only [a₀, zero_mul] using bc)).elim },
  { exact lt_of_mul_lt_mul_left' bc ((ne.symm a₀).le_iff_lt.mp a0) }
end

lemma pos_of_mul_pos_left [pos_mul_reflect_lt α] (h : 0 < a * b) (ha : 0 ≤ a) :
  0 < b :=
lt_of_mul_lt_mul_left'' ((mul_zero a).symm ▸ h : a * 0 < a * b) ha

lemma lt_of_mul_lt_mul_right'' [mul_pos_reflect_lt α]
  (bc : b * a < c * a) (a0 : 0 ≤ a) :
  b < c :=
begin
  by_cases a₀ : a = 0,
  { exact (lt_irrefl (0 : α) (by simpa only [a₀, mul_zero] using bc)).elim },
  { exact lt_of_mul_lt_mul_right' bc ((ne.symm a₀).le_iff_lt.mp a0) }
end

lemma pos_of_mul_pos_right [mul_pos_reflect_lt α] (h : 0 < a * b) (hb : 0 ≤ b) :
  0 < a :=
lt_of_mul_lt_mul_right'' ((zero_mul b).symm ▸ h : 0 * b < a * b) hb

lemma pos_iff_pos_of_mul_pos [pos_mul_reflect_lt α] [mul_pos_reflect_lt α] (hab : 0 < a * b) :
  0 < a ↔ 0 < b :=
⟨pos_of_mul_pos_left hab ∘ le_of_lt, pos_of_mul_pos_right hab ∘ le_of_lt⟩

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

lemma neg_of_mul_pos_left [pos_mul_mono α] [mul_pos_mono α]
  (h : 0 < a * b) (ha : a ≤ 0) :
  b < 0 :=
((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left $ λ h, h.1.not_le ha).2

lemma neg_of_mul_pos_right [pos_mul_mono α] [mul_pos_mono α]
  (h : 0 < a * b) (ha : b ≤ 0) :
  a < 0 :=
((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left $ λ h, h.2.not_le ha).1

lemma neg_iff_neg_of_mul_pos [pos_mul_mono α] [mul_pos_mono α]
  (hab : 0 < a * b) :
  a < 0 ↔ b < 0 :=
⟨neg_of_mul_pos_left hab ∘ le_of_lt, neg_of_mul_pos_right hab ∘ le_of_lt⟩

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

-- Lemmas in the form of `a ≤ a * b ↔ 1 ≤ b` and `a * b ≤ a ↔ b ≤ 1`,
-- which assume left covariance.

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

-- Lemmas in the form of `a ≤ b * a ↔ 1 ≤ b` and `a * b ≤ b ↔ a ≤ 1`,
-- which assume right covariance.

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

-- Lemmas in the form of `b ≤ c → a ≤ 1 → 0 < b → b * a ≤ c`,
-- which assume left covariance.

-- proven with `b0 : 0 ≤ b` as `mul_le_of_le_of_le_one'`
lemma mul_le_of_le_of_le_one [pos_mul_mono α]
  (bc : b ≤ c) (ha : a ≤ 1) (b0 : 0 < b) : b * a ≤ c :=
calc  b * a ≤ b * 1 : mul_le_mul_left' ha b0
        ... = b     : mul_one b
        ... ≤ c     : bc

lemma mul_lt_of_le_of_lt_one [pos_mul_strict_mono α]
  (bc : b ≤ c) (ha : a < 1) (b0 : 0 < b) : b * a < c :=
calc  b * a < b * 1 : mul_lt_mul_left' ha b0
        ... = b     : mul_one b
        ... ≤ c     : bc

lemma mul_lt_of_lt_of_le_one [pos_mul_mono α]
  (bc : b < c) (ha : a ≤ 1) (b0 : 0 < b) : b * a < c :=
calc  b * a ≤ b * 1 : mul_le_mul_left' ha b0
        ... = b     : mul_one b
        ... < c     : bc

lemma mul_lt_of_lt_of_lt_one [pos_mul_strict_mono α]
  (bc : b < c) (ha : a < 1) (b0 : 0 < b) : b * a < c :=
calc  b * a < b * 1 : mul_lt_mul_left' ha b0
        ... = b     : mul_one b
        ... < c     : bc

/-- Assumes left covariance. -/
lemma left.mul_le_one_of_le_of_le [pos_mul_mono α]
  (ha : a ≤ 1) (hb : b ≤ 1) (a0 : 0 < a) : a * b ≤ 1 :=
mul_le_of_le_of_le_one ha hb a0

/-- Assumes left covariance. -/
lemma left.mul_lt_one_of_le_of_lt [pos_mul_strict_mono α]
  (ha : a ≤ 1) (hb : b < 1) (a0 : 0 < a) : a * b < 1 :=
mul_lt_of_le_of_lt_one ha hb a0

/-- Assumes left covariance. -/
lemma left.mul_lt_one_of_lt_of_le [pos_mul_mono α]
  (ha : a < 1) (hb : b ≤ 1) (a0 : 0 < a) : a * b < 1 :=
mul_lt_of_lt_of_le_one ha hb a0

/-- Assumes left covariance. -/
lemma left.mul_lt_one_of_lt_of_lt [pos_mul_strict_mono α]
  (ha : a < 1) (hb : b < 1) (a0 : 0 < a) : a * b < 1 :=
mul_lt_of_lt_of_lt_one ha hb a0

-- Lemmas in the form of `b ≤ c → 1 ≤ a → 0 < c → b ≤ c * a`,
-- which assume left covariance.

-- proven with `c0 : 0 ≤ c` as `le_mul_of_le_of_one_le'`
lemma le_mul_of_le_of_one_le [pos_mul_mono α]
  (bc : b ≤ c) (ha : 1 ≤ a) (c0 : 0 < c) : b ≤ c * a :=
calc  b ≤ c     : bc
    ... = c * 1 : (mul_one c).symm
    ... ≤ c * a : mul_le_mul_left' ha c0

lemma lt_mul_of_le_of_one_lt [pos_mul_strict_mono α]
  (bc : b ≤ c) (ha : 1 < a) (c0 : 0 < c) : b < c * a :=
calc  b ≤ c     : bc
    ... = c * 1 : (mul_one c).symm
    ... < c * a : mul_lt_mul_left' ha c0

lemma lt_mul_of_lt_of_one_le [pos_mul_mono α]
  (bc : b < c) (ha : 1 ≤ a) (c0 : 0 < c) : b < c * a :=
calc  b < c     : bc
    ... = c * 1 : (mul_one c).symm
    ... ≤ c * a : mul_le_mul_left' ha c0

lemma lt_mul_of_lt_of_one_lt [pos_mul_strict_mono α]
  (bc : b < c) (ha : 1 < a) (c0 : 0 < c) : b < c * a :=
calc  b < c     : bc
    ... = c * 1 : (mul_one _).symm
    ... < c * a : mul_lt_mul_left' ha c0

/-- Assumes left covariance. -/
lemma left.one_le_mul_of_le_of_le [pos_mul_mono α]
  (ha : 1 ≤ a) (hb : 1 ≤ b) (a0 : 0 < a) : 1 ≤ a * b :=
le_mul_of_le_of_one_le ha hb a0

/-- Assumes left covariance. -/
lemma left.one_lt_mul_of_le_of_lt [pos_mul_strict_mono α]
  (ha : 1 ≤ a) (hb : 1 < b) (a0 : 0 < a) : 1 < a * b :=
lt_mul_of_le_of_one_lt ha hb a0

/-- Assumes left covariance. -/
lemma left.one_lt_mul_of_lt_of_le [pos_mul_mono α]
  (ha : 1 < a) (hb : 1 ≤ b) (a0 : 0 < a) : 1 < a * b :=
lt_mul_of_lt_of_one_le ha hb a0

/-- Assumes left covariance. -/
lemma left.one_lt_mul_of_lt_of_lt [pos_mul_strict_mono α]
  (ha : 1 < a) (hb : 1 < b) (a0 : 0 < a) : 1 < a * b :=
lt_mul_of_lt_of_one_lt ha hb a0

-- Lemmas in the form of `a ≤ 1 → b ≤ c → 0 < b → a * b ≤ c`,
-- which assume right covariance.

-- proven with `b0 : 0 ≤ b` as `mul_le_of_le_one_of_le'`
lemma mul_le_of_le_one_of_le [mul_pos_mono α]
  (ha : a ≤ 1) (bc : b ≤ c) (b0 : 0 < b) : a * b ≤ c :=
calc  a * b ≤ 1 * b : mul_le_mul_right' ha b0
        ... = b     : one_mul b
        ... ≤ c     : bc

lemma mul_lt_of_lt_one_of_le [mul_pos_strict_mono α]
  (ha : a < 1) (bc : b ≤ c) (b0 : 0 < b) : a * b < c :=
calc  a * b < 1 * b : mul_lt_mul_right' ha b0
        ... = b     : one_mul b
        ... ≤ c     : bc

lemma mul_lt_of_le_one_of_lt [mul_pos_mono α]
  (ha : a ≤ 1) (hb : b < c) (b0 : 0 < b) : a * b < c :=
calc  a * b ≤ 1 * b : mul_le_mul_right' ha b0
        ... = b     : one_mul b
        ... < c     : hb

lemma mul_lt_of_lt_one_of_lt [mul_pos_strict_mono α]
  (ha : a < 1) (bc : b < c) (b0 : 0 < b) : a * b < c :=
calc  a * b < 1 * b : mul_lt_mul_right' ha b0
        ... = b     : one_mul b
        ... < c     : bc

/-- Assumes right covariance. -/
lemma right.mul_le_one_of_le_of_le [mul_pos_mono α]
  (ha : a ≤ 1) (hb : b ≤ 1) (b0 : 0 < b) : a * b ≤ 1 :=
mul_le_of_le_one_of_le ha hb b0

/-- Assumes right covariance. -/
lemma right.mul_lt_one_of_lt_of_le [mul_pos_strict_mono α]
  (ha : a < 1) (hb : b ≤ 1) (b0 : 0 < b) : a * b < 1 :=
mul_lt_of_lt_one_of_le ha hb b0

/-- Assumes right covariance. -/
lemma right.mul_lt_one_of_le_of_lt [mul_pos_mono α]
  (ha : a ≤ 1) (hb : b < 1) (b0 : 0 < b) : a * b < 1 :=
mul_lt_of_le_one_of_lt ha hb b0

/-- Assumes right covariance. -/
lemma right.mul_lt_one_of_lt_of_lt [mul_pos_strict_mono α]
  (ha : a < 1) (hb : b < 1) (b0 : 0 < b) : a * b < 1 :=
mul_lt_of_lt_one_of_lt ha hb b0

-- Lemmas in the form of `1 ≤ a → b ≤ c → 0 < c → b ≤ a * c`,
-- which assume right covariance.

-- proven with `c0 : 0 ≤ c` as `le_mul_of_one_le_of_le'`
lemma le_mul_of_one_le_of_le [mul_pos_mono α]
  (ha : 1 ≤ a) (bc : b ≤ c) (c0 : 0 < c) : b ≤ a * c :=
calc  b ≤ c     : bc
    ... = 1 * c : (one_mul c).symm
    ... ≤ a * c : mul_le_mul_right' ha c0

lemma lt_mul_of_one_lt_of_le [mul_pos_strict_mono α]
  (ha : 1 < a) (bc : b ≤ c) (c0 : 0 < c) : b < a * c :=
calc  b ≤ c     : bc
    ... = 1 * c : (one_mul c).symm
    ... < a * c : mul_lt_mul_right' ha c0

lemma lt_mul_of_one_le_of_lt [mul_pos_mono α]
  (ha : 1 ≤ a) (bc : b < c) (c0 : 0 < c) : b < a * c :=
calc  b < c     : bc
    ... = 1 * c : (one_mul c).symm
    ... ≤ a * c : mul_le_mul_right' ha c0

lemma lt_mul_of_one_lt_of_lt [mul_pos_strict_mono α]
  (ha : 1 < a) (bc : b < c) (c0 : 0 < c) : b < a * c :=
calc  b < c     : bc
    ... = 1 * c : (one_mul c).symm
    ... < a * c : mul_lt_mul_right' ha c0

/-- Assumes right covariance. -/
lemma right.one_le_mul_of_le_of_le [mul_pos_mono α]
  (ha : 1 ≤ a) (hb : 1 ≤ b) (b0 : 0 < b) : 1 ≤ a * b :=
le_mul_of_one_le_of_le ha hb b0

/-- Assumes right covariance. -/
lemma right.one_lt_mul_of_lt_of_le [mul_pos_strict_mono α]
  (ha : 1 < a) (hb : 1 ≤ b) (b0 : 0 < b) : 1 < a * b :=
lt_mul_of_one_lt_of_le ha hb b0

/-- Assumes right covariance. -/
lemma right.one_lt_mul_of_le_of_lt [mul_pos_mono α]
  (ha : 1 ≤ a) (hb : 1 < b) (b0 : 0 < b) : 1 < a * b :=
lt_mul_of_one_le_of_lt ha hb b0

/-- Assumes right covariance. -/
lemma right.one_lt_mul_of_lt_of_lt [mul_pos_strict_mono α]
  (ha : 1 < a) (hb : 1 < b) (b0 : 0 < b) : 1 < a * b :=
lt_mul_of_one_lt_of_lt ha hb b0

-- proven with `a0 : 0 ≤ a` as `mul_le_of_le_one_right'`
lemma mul_le_of_le_one_right [pos_mul_mono α] (h : b ≤ 1) (a0 : 0 < a) :
  a * b ≤ a :=
mul_le_of_le_of_le_one le_rfl h a0

-- proven with `a0 : 0 ≤ a` as `le_mul_of_one_le_right'`
lemma le_mul_of_one_le_right [pos_mul_mono α] (h : 1 ≤ b) (a0 : 0 < a) :
  a ≤ a * b :=
le_mul_of_le_of_one_le le_rfl h a0

-- proven with `b0 : 0 ≤ b` as `mul_le_of_le_one_left'`
lemma mul_le_of_le_one_left [mul_pos_mono α] (h : a ≤ 1) (b0 : 0 < b) :
  a * b ≤ b :=
mul_le_of_le_one_of_le h le_rfl b0

-- proven with `b0 : 0 ≤ b` as `le_mul_of_one_le_left'`
lemma le_mul_of_one_le_left [mul_pos_mono α] (h : 1 ≤ a) (b0 : 0 < b) :
  b ≤ a * b :=
le_mul_of_one_le_of_le h le_rfl b0

-- proven with `a0 : 0 ≤ a` as `le_of_mul_le_of_one_le_left'`
lemma le_of_mul_le_of_one_le_left [pos_mul_mono α]
  (h : a * b ≤ c) (hle : 1 ≤ b) (a0 : 0 < a) :
  a ≤ c :=
(le_mul_of_one_le_right hle a0).trans h

lemma lt_of_mul_lt_of_one_le_left [pos_mul_mono α]
  (h : a * b < c) (hle : 1 ≤ b) (a0 : 0 < a) :
  a < c :=
(le_mul_of_one_le_right hle a0).trans_lt h

-- proven with `b0 : 0 ≤ b` as `le_of_le_mul_of_le_one_left'`
lemma le_of_le_mul_of_le_one_left [pos_mul_mono α]
  (h : a ≤ b * c) (hle : c ≤ 1) (b0 : 0 < b) :
  a ≤ b :=
h.trans (mul_le_of_le_one_right hle b0)

lemma lt_of_lt_mul_of_le_one_left [pos_mul_mono α]
  (h : a < b * c) (hle : c ≤ 1) (b0 : 0 < b) :
  a < b :=
h.trans_le (mul_le_of_le_one_right hle b0)

-- proven with `b0 : 0 ≤ b` as `le_of_mul_le_of_one_le_right'`
lemma le_of_mul_le_of_one_le_right [mul_pos_mono α]
  (h : a * b ≤ c) (hle : 1 ≤ a) (b0 : 0 < b) :
  b ≤ c :=
(le_mul_of_one_le_left hle b0).trans h

lemma lt_of_mul_lt_of_one_le_right [mul_pos_mono α]
  (h : a * b < c) (hle : 1 ≤ a) (b0 : 0 < b) :
  b < c :=
(le_mul_of_one_le_left hle b0).trans_lt h

-- proven with `c0 : 0 ≤ b` as `le_of_le_mul_of_le_one_right'`
lemma le_of_le_mul_of_le_one_right [mul_pos_mono α]
  (h : a ≤ b * c) (hle : b ≤ 1) (c0 : 0 < c) :
  a ≤ c :=
h.trans (mul_le_of_le_one_left hle c0)

lemma lt_of_lt_mul_of_le_one_right [mul_pos_mono α]
  (h : a < b * c) (hle : b ≤ 1) (c0 : 0 < c) :
  a < c :=
h.trans_le (mul_le_of_le_one_left hle c0)

end preorder

section linear_order
variables [linear_order α]

-- proven with `a0 : 0 ≤ a` as `exists_square_le'`
lemma exists_square_le [pos_mul_strict_mono α]
  (a0 : 0 < a) : ∃ (b : α), b * b ≤ a :=
begin
  by_cases h : a < 1,
  { use a,
    have : a*a < a*1,
    exact mul_lt_mul_left' h a0,
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

lemma mul_le_of_le_of_le_one' [pos_mul_mono α]
  (bc : b ≤ c) (ha : a ≤ 1) (b0 : 0 ≤ b) : b * a ≤ c :=
b0.lt_or_eq.elim (mul_le_of_le_of_le_one bc ha) (λ h, by rw [← h, zero_mul]; exact b0.trans bc)

/-- Assumes left covariance. -/
lemma left.mul_le_one_of_le_of_le' [pos_mul_mono α]
  (ha : a ≤ 1) (hb : b ≤ 1) (a0 : 0 ≤ a) : a * b ≤ 1 :=
mul_le_of_le_of_le_one' ha hb a0

lemma le_mul_of_le_of_one_le' [pos_mul_mono α]
  (bc : b ≤ c) (ha : 1 ≤ a) (c0 : 0 ≤ c) : b ≤ c * a :=
c0.lt_or_eq.elim (le_mul_of_le_of_one_le bc ha) (λ h, by rw [← h, zero_mul] at *; exact bc)

/-- Assumes left covariance. -/
lemma left.one_le_mul_of_le_of_le' [pos_mul_mono α]
  (ha : 1 ≤ a) (hb : 1 ≤ b) (a0 : 0 ≤ a) : 1 ≤ a * b :=
le_mul_of_le_of_one_le' ha hb a0

lemma mul_le_of_le_one_of_le' [mul_pos_mono α]
  (ha : a ≤ 1) (bc : b ≤ c) (b0 : 0 ≤ b) : a * b ≤ c :=
b0.lt_or_eq.elim (mul_le_of_le_one_of_le ha bc) (λ h, by rw [← h, mul_zero] at *; exact bc)

/-- Assumes right covariance. -/
lemma right.mul_le_one_of_le_of_le' [mul_pos_mono α]
  (ha : a ≤ 1) (hb : b ≤ 1) (b0 : 0 < b) : a * b ≤ 1 :=
mul_le_of_le_one_of_le ha hb b0

lemma le_mul_of_one_le_of_le' [mul_pos_mono α]
  (ha : 1 ≤ a) (bc : b ≤ c) (c0 : 0 ≤ c) : b ≤ a * c :=
c0.lt_or_eq.elim (le_mul_of_one_le_of_le ha bc) (λ h, by rw [← h, mul_zero] at *; exact bc)

/-- Assumes right covariance. -/
lemma right.one_le_mul_of_le_of_le' [mul_pos_mono α]
  (ha : 1 ≤ a) (hb : 1 ≤ b) (b0 : 0 ≤ b) : 1 ≤ a * b :=
le_mul_of_one_le_of_le' ha hb b0

lemma mul_le_of_le_one_right' [pos_mul_mono α] (h : b ≤ 1) (a0 : 0 ≤ a) :
  a * b ≤ a :=
mul_le_of_le_of_le_one' le_rfl h a0

lemma le_mul_of_one_le_right' [pos_mul_mono α] (h : 1 ≤ b) (a0 : 0 ≤ a) :
  a ≤ a * b :=
le_mul_of_le_of_one_le' le_rfl h a0

lemma mul_le_of_le_one_left' [mul_pos_mono α] (h : a ≤ 1) (b0 : 0 ≤ b) :
  a * b ≤ b :=
mul_le_of_le_one_of_le' h le_rfl b0

lemma le_mul_of_one_le_left' [mul_pos_mono α] (h : 1 ≤ a) (b0 : 0 ≤ b) :
  b ≤ a * b :=
le_mul_of_one_le_of_le' h le_rfl b0

lemma le_of_mul_le_of_one_le_left' [pos_mul_mono α]
  (h : a * b ≤ c) (hle : 1 ≤ b) (a0 : 0 ≤ a) :
  a ≤ c :=
a0.lt_or_eq.elim (le_of_mul_le_of_one_le_left h hle)
  (λ ha, by simpa only [← ha, zero_mul] using h)

lemma le_of_le_mul_of_le_one_left' [pos_mul_mono α]
  (h : a ≤ b * c) (hle : c ≤ 1) (b0 : 0 ≤ b) :
  a ≤ b :=
b0.lt_or_eq.elim (le_of_le_mul_of_le_one_left h hle)
  (λ hb, by simpa only [← hb, zero_mul] using h)

lemma le_of_mul_le_of_one_le_right' [mul_pos_mono α]
  (h : a * b ≤ c) (hle : 1 ≤ a) (b0 : 0 ≤ b) :
  b ≤ c :=
b0.lt_or_eq.elim (le_of_mul_le_of_one_le_right h hle)
  (λ ha, by simpa only [← ha, mul_zero] using h)

lemma le_of_le_mul_of_le_one_right' [mul_pos_mono α]
  (h : a ≤ b * c) (hle : b ≤ 1) (c0 : 0 ≤ c) :
  a ≤ c :=
c0.lt_or_eq.elim (le_of_le_mul_of_le_one_right h hle)
  (λ ha, by simpa only [← ha, mul_zero] using h)

end partial_order

section linear_order
variables [linear_order α]

lemma exists_square_le' [pos_mul_strict_mono α]
  (a0 : 0 ≤ a) : ∃ (b : α), b * b ≤ a :=
a0.lt_or_eq.elim exists_square_le (λ h, by rw [← h]; exact ⟨0, by simp⟩)

end linear_order

end mul_zero_one_class

end zero_lt
