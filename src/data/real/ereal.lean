/-
Copyright (c) 2019 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import data.real.basic
import data.real.ennreal

/-!
# The extended reals [-∞, ∞].

This file defines `ereal`, the real numbers together with a top and bottom element,
referred to as ⊤ and ⊥. It is implemented as `with_bot (with_top ℝ)`

Addition and multiplication are problematic in the presence of ±∞, but
negation has a natural definition and satisfies the usual properties.

An ad hoc addition is defined, for which `ereal` is an `add_comm_monoid`, and even an ordered one
(if `a ≤ a'` and `b ≤ b'` then `a + b ≤ a' + b'`).
Note however that addition is badly behaved at `(⊥, ⊤)` and `(⊤, ⊥)` so this can not be upgraded
to a group structure. Our choice is that `⊥ + ⊤ = ⊤ + ⊥ = ⊥`.

An ad hoc subtraction is then defined by `x - y = x + (-y)`. It does not have nice properties,
but it is sometimes convenient to have.

An ad hoc multiplication is defined, for which `ereal` is a `comm_monoid_with_zero`.
This does not distribute with addition, as `⊤ = ⊤ - ⊥ = 1*⊤ - 1*⊤ ≠ (1 - 1) * ⊤ = 0 * ⊤ = 0`.

`ereal` is a `complete_linear_order`; this is deduced by type class inference from
the fact that `with_bot (with_top L)` is a complete linear order if `L` is
a conditionally complete linear order.

Coercions from `ℝ` and from `ℝ≥0∞` are registered, and their basic properties are proved. The main
one is the real coercion, and is usually referred to just as `coe` (lemmas such as
`ereal.coe_add` deal with this coercion). The one from `ennreal` is usually called `coe_ennreal`
in the `ereal` namespace.

## Tags

real, ereal, complete lattice

## TODO

abs : ereal → ℝ≥0∞

In Isabelle they define + - * and / (making junk choices for things like -∞ + ∞)
and then prove whatever bits of the ordered ring/field axioms still hold. They
also do some limits stuff (liminf/limsup etc).
See https://isabelle.in.tum.de/dist/library/HOL/HOL-Library/Extended_Real.html
-/

open function
open_locale ennreal nnreal

noncomputable theory

/-- ereal : The type `[-∞, ∞]` -/
@[derive [has_bot, has_zero, has_one, nontrivial, add_monoid,
  has_Sup, has_Inf, complete_linear_order, linear_ordered_add_comm_monoid]]
def ereal := with_bot (with_top ℝ)

/-- The canonical inclusion froms reals to ereals. Do not use directly: as this is registered as
a coercion, use the coercion instead. -/
def real.to_ereal : ℝ → ereal := some ∘ some

namespace ereal

-- TODO: Provide explicitly, otherwise it is inferred noncomputably from `complete_linear_order`
instance : has_top ereal := ⟨some ⊤⟩

instance : has_coe ℝ ereal := ⟨real.to_ereal⟩

lemma coe_strict_mono : strict_mono (coe : ℝ → ereal) :=
with_bot.coe_strict_mono.comp with_top.coe_strict_mono

lemma coe_injective : injective (coe : ℝ → ereal) := coe_strict_mono.injective

@[simp, norm_cast] protected lemma coe_le_coe_iff {x y : ℝ} : (x : ereal) ≤ (y : ereal) ↔ x ≤ y :=
coe_strict_mono.le_iff_le
@[simp, norm_cast] protected lemma coe_lt_coe_iff {x y : ℝ} : (x : ereal) < (y : ereal) ↔ x < y :=
coe_strict_mono.lt_iff_lt
@[simp, norm_cast] protected lemma coe_eq_coe_iff {x y : ℝ} : (x : ereal) = (y : ereal) ↔ x = y :=
coe_injective.eq_iff
protected lemma coe_ne_coe_iff {x y : ℝ} : (x : ereal) ≠ (y : ereal) ↔ x ≠ y := coe_injective.ne_iff

/-- The canonical map from nonnegative extended reals to extended reals -/
def _root_.ennreal.to_ereal : ℝ≥0∞ → ereal
| ⊤ := ⊤
| (some x) := x.1

instance has_coe_ennreal : has_coe ℝ≥0∞ ereal := ⟨ennreal.to_ereal⟩

instance : inhabited ereal := ⟨0⟩

@[simp, norm_cast] lemma coe_zero : ((0 : ℝ) : ereal) = 0 := rfl
@[simp, norm_cast] lemma coe_one : ((1 : ℝ) : ereal) = 1 := rfl

/-- A recursor for `ereal` in terms of the coercion.

A typical invocation looks like `induction x using ereal.rec`. Note that using `induction`
directly will unfold `ereal` to `option` which is undesirable.

When working in term mode, note that pattern matching can be used directly. -/
@[elab_as_eliminator]
protected def rec {C : ereal → Sort*} (h_bot : C ⊥) (h_real : Π a : ℝ, C a) (h_top : C ⊤) :
  ∀ a : ereal, C a
| ⊥ := h_bot
| (a : ℝ) := h_real a
| ⊤ := h_top

protected def mul : ereal → ereal → ereal
| ⊥ ⊥ := ⊤
| ⊥ ⊤ := ⊥
| ⊥ (x : ℝ) := if 0 < x then ⊥ else if x = 0 then 0 else ⊤
| ⊤ ⊥ := ⊥
| ⊤ ⊤ := ⊤
| ⊤ (x : ℝ) := if 0 < x then ⊤ else if x = 0 then 0 else ⊥
| (x : ℝ) ⊤ := if 0 < x then ⊤ else if x = 0 then 0 else ⊥
| (x : ℝ) ⊥ := if 0 < x then ⊥ else if x = 0 then 0 else ⊤
| (x : ℝ) (y : ℝ) := (x * y : ℝ)

instance : has_mul ereal := ⟨ereal.mul⟩

instance : mul_zero_one_class ereal :=
{ one_mul := λ x, begin
    induction x using ereal.rec;
    { dsimp only [(*)], simp only [ereal.mul, ← ereal.coe_one, zero_lt_one, if_true, one_mul] },
  end,
  mul_one := λ x, begin
    induction x using ereal.rec;
    { dsimp only [(*)], simp only [ereal.mul, ← ereal.coe_one, zero_lt_one, if_true, mul_one] },
  end,
  zero_mul := λ x, begin
    induction x using ereal.rec;
    { simp only [(*)], simp only [ereal.mul, ← ereal.coe_zero, zero_lt_one, if_true, if_false,
        lt_irrefl (0 : ℝ), eq_self_iff_true, zero_mul] },
  end,
  mul_zero := λ x, begin
    induction x using ereal.rec;
    { simp only [(*)], simp only [ereal.mul, ← ereal.coe_zero, zero_lt_one, if_true, if_false,
        lt_irrefl (0 : ℝ), eq_self_iff_true, mul_zero] },
  end,
  ..ereal.has_mul, ..ereal.has_one, ..ereal.has_zero }

protected lemma mul_comm (x y : ereal) : x * y = y * x :=
begin
  induction x using ereal.rec; induction y using ereal.rec; try { refl },
  dsimp only [(*)],
  simp only [ereal.mul, mul_comm],
end

/-
instance : comm_monoid_with_zero ereal :=
{ mul_assoc := λ x y z, begin
    induction x using ereal.rec; induction y using ereal.rec; induction z using ereal.rec,
    { refl },
    { dsimp only [ereal.has_mul, ereal.mul],
      split_ifs,
      { refl },
      { exact (mul_zero ⊥).symm },
      { refl } },
    { refl },
    { dsimp only [ereal.has_mul, ereal.mul],
      split_ifs,
      { refl },
      { exact ereal.mul_comm 0 ⊥ },
      { refl } },
    { rw ← coe_mul,
      rcases lt_trichotomy 0 y with hy|rfl|hy; rcases lt_trichotomy 0 z with hz|rfl|hz,
      { dsimp only [ereal.has_mul, ereal.mul],
        simp only [hy, mul_pos hy hz, if_true, ereal.has_mul, ereal.mul, hz] },
      { simp only [coe_zero, mul_zero, zero_mul] },
      sorry,
      { simp only [coe_zero, mul_zero, zero_mul] },
      { simp only [coe_zero, mul_zero, zero_mul] },
      sorry,
      sorry,
      { simp only [coe_zero, mul_zero, zero_mul] },
      sorry }


  end,
  one_mul := λ x, begin
    induction x using ereal.rec;
    { dsimp only [(*)], simp only [ereal.mul, ← ereal.coe_one, zero_lt_one, if_true, one_mul] },
  end,
  mul_one := λ x, begin
    induction x using ereal.rec;
    { dsimp only [(*)], simp only [ereal.mul, ← ereal.coe_one, zero_lt_one, if_true, mul_one] },
  end,
  mul_comm := λ x y, begin

  end,
  zero_mul := λ x, begin
    induction x using ereal.rec;
    { simp only [(*)], simp only [ereal.mul, ← ereal.coe_zero, zero_lt_one, if_true, if_false,
        lt_irrefl (0 : ℝ), eq_self_iff_true, zero_mul] },
  end,
  mul_zero := λ x, begin
    induction x using ereal.rec;
    { simp only [(*)], simp only [ereal.mul, ← ereal.coe_zero, zero_lt_one, if_true, if_false,
        lt_irrefl (0 : ℝ), eq_self_iff_true, mul_zero] },
  end,
  ..ereal.has_mul, ..ereal.has_one, ..ereal.has_zero }

-/

/-! ### Real coercion -/

instance can_lift : can_lift ereal ℝ coe (λ r, r ≠ ⊤ ∧ r ≠ ⊥) :=
{ prf := λ x hx,
  begin
    induction x using ereal.rec,
    { simpa using hx },
    { simp },
    { simpa using hx }
  end }

/-- The map from extended reals to reals sending infinities to zero. -/
def to_real : ereal → ℝ
| ⊥       := 0
| ⊤       := 0
| (x : ℝ) := x

@[simp] lemma to_real_top : to_real ⊤ = 0 := rfl

@[simp] lemma to_real_bot : to_real ⊥ = 0 := rfl

@[simp] lemma to_real_zero : to_real 0 = 0 := rfl

@[simp] lemma to_real_coe (x : ℝ) : to_real (x : ereal) = x := rfl

@[simp] lemma bot_lt_coe (x : ℝ) : (⊥ : ereal) < x := with_bot.bot_lt_coe _

@[simp] lemma coe_ne_bot (x : ℝ) : (x : ereal) ≠ ⊥  := (bot_lt_coe x).ne'

@[simp] lemma bot_ne_coe (x : ℝ) : (⊥ : ereal) ≠ x := (bot_lt_coe x).ne

@[simp] lemma coe_lt_top (x : ℝ) : (x : ereal) < ⊤ :=
by { apply with_bot.coe_lt_coe.2, exact with_top.coe_lt_top _ }

@[simp] lemma coe_ne_top (x : ℝ) : (x : ereal) ≠ ⊤ := (coe_lt_top x).ne

@[simp] lemma top_ne_coe (x : ℝ) : (⊤ : ereal) ≠ x := (coe_lt_top x).ne'

@[simp] lemma bot_lt_zero : (⊥ : ereal) < 0 := bot_lt_coe 0

@[simp] lemma bot_ne_zero : (⊥ : ereal) ≠ 0 := (coe_ne_bot 0).symm

@[simp] lemma zero_ne_bot : (0 : ereal) ≠ ⊥ := coe_ne_bot 0

@[simp] lemma zero_lt_top : (0 : ereal) < ⊤ := coe_lt_top 0

@[simp] lemma zero_ne_top : (0 : ereal) ≠ ⊤ := coe_ne_top 0

@[simp] lemma top_ne_zero : (⊤ : ereal) ≠ 0 := (coe_ne_top 0).symm

@[simp, norm_cast] lemma coe_add (x y : ℝ) : (↑(x + y) : ereal) = x + y := rfl
@[simp, norm_cast] lemma coe_mul (x y : ℝ) : (↑(x * y) : ereal) = x * y := rfl
@[norm_cast] lemma coe_nsmul (n : ℕ) (x : ℝ) : (↑(n • x) : ereal) = n • x :=
map_nsmul (⟨coe, coe_zero, coe_add⟩ : ℝ →+ ereal) _ _

/- TODO : put after comm_monoid instance
@[simp, norm_cast] lemma coe_pow (x : ℝ) (n : ℕ) : (↑(x ^ n) : ereal) = x ^ n :=
map_pow (⟨coe, coe_one, coe_mul⟩ : ℝ →* ereal) _ _
-/

@[simp, norm_cast] lemma coe_bit0 (x : ℝ) : (↑(bit0 x) : ereal) = bit0 x := rfl
@[simp, norm_cast] lemma coe_bit1 (x : ℝ) : (↑(bit1 x) : ereal) = bit1 x := rfl

@[simp, norm_cast] lemma coe_eq_zero {x : ℝ} : (x : ereal) = 0 ↔ x = 0 := ereal.coe_eq_coe_iff
@[simp, norm_cast] lemma coe_eq_one {x : ℝ} : (x : ereal) = 1 ↔ x = 1 := ereal.coe_eq_coe_iff
lemma coe_ne_zero {x : ℝ} : (x : ereal) ≠ 0 ↔ x ≠ 0 := ereal.coe_ne_coe_iff
lemma coe_ne_one {x : ℝ} : (x : ereal) ≠ 1 ↔ x ≠ 1 := ereal.coe_ne_coe_iff

@[simp, norm_cast] protected lemma coe_nonneg {x : ℝ} : (0 : ereal) ≤ x ↔ 0 ≤ x :=
ereal.coe_le_coe_iff

@[simp, norm_cast] protected lemma coe_nonpos {x : ℝ} : (x : ereal) ≤ 0 ↔ x ≤ 0 :=
ereal.coe_le_coe_iff

@[simp, norm_cast] protected lemma coe_pos {x : ℝ} : (0 : ereal) < x ↔ 0 < x :=
ereal.coe_lt_coe_iff

@[simp, norm_cast] protected lemma coe_neg' {x : ℝ} : (x : ereal) < 0 ↔ x < 0 :=
ereal.coe_lt_coe_iff

lemma to_real_le_to_real {x y : ereal} (h : x ≤ y) (hx : x ≠ ⊥) (hy : y ≠ ⊤) :
  x.to_real ≤ y.to_real :=
begin
  lift x to ℝ,
  { simp [hx, (h.trans_lt (lt_top_iff_ne_top.2 hy)).ne], },
  lift y to ℝ,
  { simp [hy, ((bot_lt_iff_ne_bot.2 hx).trans_le h).ne'] },
  simpa using h
end

lemma coe_to_real {x : ereal} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) : (x.to_real : ereal) = x :=
begin
  induction x using ereal.rec,
  { simpa using h'x },
  { refl },
  { simpa using hx },
end

lemma le_coe_to_real {x : ereal} (h : x ≠ ⊤) : x ≤ x.to_real :=
begin
  by_cases h' : x = ⊥,
  { simp only [h', bot_le] },
  { simp only [le_refl, coe_to_real h h'] },
end

lemma coe_to_real_le {x : ereal} (h : x ≠ ⊥) : ↑x.to_real ≤ x :=
begin
  by_cases h' : x = ⊤,
  { simp only [h', le_top] },
  { simp only [le_refl, coe_to_real h' h] },
end

lemma eq_top_iff_forall_lt (x : ereal) : x = ⊤ ↔ ∀ (y : ℝ), (y : ereal) < x :=
begin
  split,
  { rintro rfl, exact ereal.coe_lt_top },
  { contrapose!,
    intro h,
    exact ⟨x.to_real, le_coe_to_real h⟩, },
end

lemma eq_bot_iff_forall_lt (x : ereal) : x = ⊥ ↔ ∀ (y : ℝ), x < (y : ereal) :=
begin
  split,
  { rintro rfl, exact bot_lt_coe },
  { contrapose!,
    intro h,
    exact ⟨x.to_real, coe_to_real_le h⟩, },
end

/-! ### ennreal coercion -/

@[simp] lemma to_real_coe_ennreal : ∀ {x : ℝ≥0∞}, to_real (x : ereal) = ennreal.to_real x
| ⊤ := rfl
| (some x) := rfl

lemma coe_nnreal_eq_coe_real (x : ℝ≥0) : ((x : ℝ≥0∞) : ereal) = (x : ℝ) := rfl

@[simp, norm_cast] lemma coe_ennreal_zero : ((0 : ℝ≥0∞) : ereal) = 0 := rfl
@[simp, norm_cast] lemma coe_ennreal_one : ((1 : ℝ≥0∞) : ereal) = 1 := rfl
@[simp, norm_cast] lemma coe_ennreal_top : ((⊤ : ℝ≥0∞) : ereal) = ⊤ := rfl

@[simp] lemma coe_ennreal_eq_top_iff : ∀ {x : ℝ≥0∞}, (x : ereal) = ⊤ ↔ x = ⊤
| ⊤ := by simp
| (some x) := by { simp only [ennreal.coe_ne_top, iff_false, ennreal.some_eq_coe], dec_trivial }

lemma coe_nnreal_ne_top (x : ℝ≥0) : ((x : ℝ≥0∞) : ereal) ≠ ⊤ := dec_trivial

@[simp] lemma coe_nnreal_lt_top (x : ℝ≥0) : ((x : ℝ≥0∞) : ereal) < ⊤ := dec_trivial

lemma coe_ennreal_strict_mono : strict_mono (coe : ℝ≥0∞ → ereal)
| ⊤ ⊤ := by simp
| (some x) ⊤ := by simp
| ⊤ (some y) := by simp
| (some x) (some y) := by simp [coe_nnreal_eq_coe_real]

lemma coe_ennreal_injective : injective (coe : ℝ≥0∞ → ereal) := coe_ennreal_strict_mono.injective

@[simp, norm_cast] lemma coe_ennreal_le_coe_ennreal_iff {x y : ℝ≥0∞} :
  (x : ereal) ≤ (y : ereal) ↔ x ≤ y :=
coe_ennreal_strict_mono.le_iff_le

@[simp, norm_cast] lemma coe_ennreal_lt_coe_ennreal_iff {x y : ℝ≥0∞} :
  (x : ereal) < (y : ereal) ↔ x < y :=
coe_ennreal_strict_mono.lt_iff_lt

@[simp, norm_cast] lemma coe_ennreal_eq_coe_ennreal_iff {x y : ℝ≥0∞} :
  (x : ereal) = (y : ereal) ↔ x = y :=
coe_ennreal_injective.eq_iff

lemma coe_ennreal_ne_coe_ennreal_iff {x y : ℝ≥0∞} : (x : ereal) ≠ (y : ereal) ↔ x ≠ y :=
coe_ennreal_injective.ne_iff

@[simp, norm_cast] lemma coe_ennreal_eq_zero {x : ℝ≥0∞} : (x : ereal) = 0 ↔ x = 0 :=
by rw [←coe_ennreal_eq_coe_ennreal_iff, coe_ennreal_zero]

@[simp, norm_cast] lemma coe_ennreal_eq_one {x : ℝ≥0∞} : (x : ereal) = 1 ↔ x = 1 :=
by rw [←coe_ennreal_eq_coe_ennreal_iff, coe_ennreal_one]

@[norm_cast] lemma coe_ennreal_ne_zero {x : ℝ≥0∞} : (x : ereal) ≠ 0 ↔ x ≠ 0 :=
coe_ennreal_eq_zero.not

@[norm_cast] lemma coe_ennreal_ne_one {x : ℝ≥0∞} : (x : ereal) ≠ 1 ↔ x ≠ 1 := coe_ennreal_eq_one.not

lemma coe_ennreal_nonneg (x : ℝ≥0∞) : (0 : ereal) ≤ x :=
coe_ennreal_le_coe_ennreal_iff.2 (zero_le x)

@[simp, norm_cast] lemma coe_ennreal_pos {x : ℝ≥0∞} : (0 : ereal) < x ↔ 0 < x :=
by rw [←coe_ennreal_zero, coe_ennreal_lt_coe_ennreal_iff]

@[simp] lemma bot_lt_coe_ennreal (x : ℝ≥0∞) : (⊥ : ereal) < x :=
(bot_lt_coe 0).trans_le (coe_ennreal_nonneg _)

@[simp] lemma coe_ennreal_ne_bot (x : ℝ≥0∞) : (x : ereal) ≠ ⊥ := (bot_lt_coe_ennreal x).ne'

@[simp, norm_cast] lemma coe_ennreal_add (x y : ennreal) : ((x + y : ℝ≥0∞) : ereal) = x + y :=
by cases x; cases y; refl

@[simp, norm_cast] lemma coe_ennreal_mul : ∀ (x y : ℝ≥0∞), ((x * y : ℝ≥0∞) : ereal) = x * y
| ⊤ y := by { rw ennreal.top_mul, split_ifs, simp [h],
  simp [h],
 }
| x ⊤ := by { rw ennreal.mul_top, split_ifs; simp [h] }
| (some x) (some y) := by simp [←ennreal.coe_mul, coe_nnreal_eq_coe_real]

@[norm_cast] lemma coe_ennreal_nsmul (n : ℕ) (x : ℝ≥0∞) : (↑(n • x) : ereal) = n • x :=
map_nsmul (⟨coe, coe_ennreal_zero, coe_ennreal_add⟩ : ℝ≥0∞ →+ ereal) _ _

/-
TODO
@[simp, norm_cast] lemma coe_ennreal_pow (x : ℝ≥0∞) (n : ℕ) : (↑(x ^ n) : ereal) = x ^ n :=
map_pow (⟨coe, coe_ennreal_one, coe_ennreal_mul⟩ : ℝ≥0∞ →* ereal) _ _
-/

@[simp, norm_cast] lemma coe_ennreal_bit0 (x : ℝ≥0∞) : (↑(bit0 x) : ereal) = bit0 x :=
coe_ennreal_add _ _
@[simp, norm_cast] lemma coe_ennreal_bit1 (x : ℝ≥0∞) : (↑(bit1 x) : ereal) = bit1 x :=
by simp_rw [bit1, coe_ennreal_add, coe_ennreal_bit0, coe_ennreal_one]

/-! ### Absolute value -/

protected def abs : ereal → ℝ≥0∞
| ⊥ := ⊤
| ⊤ := ⊤
| (x : ℝ) := ennreal.of_real (|x|)

@[simp] lemma abs_top : (⊤ : ereal).abs = ⊤ := rfl
@[simp] lemma abs_bot : (⊥ : ereal).abs = ⊤ := rfl

lemma abs_eq_zero_iff {x : ereal} : x.abs = 0 ↔ x = 0 :=
begin
  induction x using ereal.rec,
  { simp only [abs_bot, ennreal.top_ne_zero, bot_ne_zero] },
  { simp only [ereal.abs, coe_eq_zero, ennreal.of_real_eq_zero, abs_nonpos_iff] },
  { simp only [abs_top, ennreal.top_ne_zero, top_ne_zero] }
end

@[simp] lemma abs_zero : (0 : ereal).abs = 0 :=
by rw [abs_eq_zero_iff]

@[simp] lemma abs_mul (x y : ereal) : (x * y).abs = x.abs * y.abs :=
begin
  induction x using ereal.rec; induction y using ereal.rec,
  { refl },
  { dsimp only [ereal.has_mul, ereal.mul],
    split_ifs with hy h'y,
    { symmetry,
      simp only [abs_bot, ne.def, not_false_iff, abs_eq_zero_iff, hy.ne', with_top.top_mul,
        coe_eq_zero] },
    { simp only [h'y, abs_zero, coe_zero, mul_zero] },
    { symmetry,
      simp only [abs_bot, abs_top, with_top.mul_eq_top_iff, ne.def, ennreal.top_ne_zero,
        not_false_iff, true_and, eq_self_iff_true,
        abs_eq_zero_iff, h'y, coe_eq_zero, not_false_iff, or_true] } },
  { refl },
  { dsimp only [ereal.has_mul, ereal.mul],
    split_ifs with hx h'x,
    { symmetry,
      simp only [abs_bot, ne.def, not_false_iff, abs_eq_zero_iff, hx.ne', with_top.mul_top,
        coe_eq_zero], },
    { simp only [h'x, abs_zero, coe_zero, zero_mul], },
    { symmetry,
      simp only [abs_bot, abs_top, with_top.mul_eq_top_iff, ne.def, ennreal.top_ne_zero,
        not_false_iff, true_and, eq_self_iff_true, true_or,
        abs_eq_zero_iff, h'x, coe_eq_zero, not_false_iff, or_true] } },
  { simp only [← coe_mul, ereal.abs, abs_mul, ← ennreal.coe_mul,
      ennreal.of_real_mul (abs_nonneg x)] },
  { dsimp only [ereal.has_mul, ereal.mul],
    split_ifs with hx h'x,
    { symmetry,
      simp only [ne.def, not_false_iff, abs_eq_zero_iff, hx.ne', with_top.mul_top, coe_eq_zero,
        abs_top] },
    { simp only [h'x, abs_zero, coe_zero, zero_mul], },
    { symmetry,
      simp only [abs_bot, abs_top, with_top.mul_eq_top_iff, ne.def, ennreal.top_ne_zero,
        not_false_iff, true_and, eq_self_iff_true, true_or,
        abs_eq_zero_iff, h'x, coe_eq_zero, not_false_iff, or_true] } },
  { refl },
  { dsimp only [ereal.has_mul, ereal.mul],
    split_ifs with hy h'y,
    { symmetry,
      simp only [abs_top, ne.def, not_false_iff, abs_eq_zero_iff, hy.ne', with_top.top_mul,
        coe_eq_zero] },
    { simp only [h'y, abs_zero, coe_zero, mul_zero] },
    { symmetry,
      simp only [abs_bot, abs_top, with_top.mul_eq_top_iff, ne.def, ennreal.top_ne_zero,
        not_false_iff, true_and, eq_self_iff_true,
        abs_eq_zero_iff, h'y, coe_eq_zero, not_false_iff, or_true] } },
  { have : (⊤ : ereal) * ⊤ = ⊤ := rfl,
    simp only [abs_top, ennreal.top_mul_top, this] },
end

/-! ### Sign -/

protected def sgn : ereal → sign_type :=

/-! ### Order -/

lemma exists_rat_btwn_of_lt : Π {a b : ereal} (hab : a < b),
  ∃ (x : ℚ), a < (x : ℝ) ∧ ((x : ℝ) : ereal) < b
| ⊤ b h := (not_top_lt h).elim
| (a : ℝ) ⊥ h := (lt_irrefl _ ((bot_lt_coe a).trans h)).elim
| (a : ℝ) (b : ℝ) h := by simp [exists_rat_btwn (ereal.coe_lt_coe_iff.1 h)]
| (a : ℝ) ⊤ h := let ⟨b, hab⟩ := exists_rat_gt a in ⟨b, by simpa using hab, coe_lt_top _⟩
| ⊥ ⊥ h := (lt_irrefl _ h).elim
| ⊥ (a : ℝ) h := let ⟨b, hab⟩ := exists_rat_lt a in ⟨b, bot_lt_coe _, by simpa using hab⟩
| ⊥ ⊤ h := ⟨0, bot_lt_coe _, coe_lt_top _⟩

lemma lt_iff_exists_rat_btwn {a b : ereal} :
  a < b ↔ ∃ (x : ℚ), a < (x : ℝ) ∧ ((x : ℝ) : ereal) < b :=
⟨λ hab, exists_rat_btwn_of_lt hab, λ ⟨x, ax, xb⟩, ax.trans xb⟩

lemma lt_iff_exists_real_btwn {a b : ereal} :
  a < b ↔ ∃ (x : ℝ), a < x ∧ (x : ereal) < b :=
⟨λ hab, let ⟨x, ax, xb⟩ := exists_rat_btwn_of_lt hab in ⟨(x : ℝ), ax, xb⟩,
 λ ⟨x, ax, xb⟩, ax.trans xb⟩

/-- The set of numbers in `ereal` that are not equal to `±∞` is equivalent to `ℝ`. -/
def ne_top_bot_equiv_real : ({⊥, ⊤}ᶜ : set ereal) ≃ ℝ :=
{ to_fun := λ x, ereal.to_real x,
  inv_fun := λ x, ⟨x, by simp⟩,
  left_inv := λ ⟨x, hx⟩, subtype.eq $ begin
    lift x to ℝ,
    { simpa [not_or_distrib, and_comm] using hx },
    { simp },
  end,
  right_inv := λ x, by simp }

/-! ### Addition -/

@[simp] lemma add_bot (x : ereal) : x + ⊥ = ⊥ := with_bot.add_bot _
@[simp] lemma bot_add (x : ereal) : ⊥ + x = ⊥ := with_bot.bot_add _

@[simp] lemma top_add_top : (⊤ : ereal) + ⊤ = ⊤ := rfl
@[simp] lemma top_add_coe (x : ℝ) : (⊤ : ereal) + x = ⊤ := rfl
@[simp] lemma coe_add_top (x : ℝ) : (x : ereal) + ⊤ = ⊤ := rfl

lemma to_real_add : ∀ {x y : ereal} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) (hy : y ≠ ⊤) (h'y : y ≠ ⊥),
  to_real (x + y) = to_real x + to_real y
| ⊥ y hx h'x hy h'y := (h'x rfl).elim
| ⊤ y hx h'x hy h'y := (hx rfl).elim
| x ⊤ hx h'x hy h'y := (hy rfl).elim
| x ⊥ hx h'x hy h'y := (h'y rfl).elim
| (x : ℝ) (y : ℝ) hx h'x hy h'y := by simp [← ereal.coe_add]

lemma add_lt_add_right_coe {x y : ereal} (h : x < y) (z : ℝ) : x + z < y + z :=
begin
  induction x using ereal.rec; induction y using ereal.rec,
  { exact (lt_irrefl _ h).elim },
  { simp only [← coe_add, bot_add, bot_lt_coe] },
  { simp },
  { exact (lt_irrefl _ (h.trans (bot_lt_coe x))).elim },
  { norm_cast at h ⊢, exact add_lt_add_right h _ },
  { simp only [← coe_add, top_add_coe, coe_lt_top] },
  { exact (lt_irrefl _ (h.trans_le le_top)).elim },
  { exact (lt_irrefl _ (h.trans_le le_top)).elim },
  { exact (lt_irrefl _ (h.trans_le le_top)).elim },
end

lemma add_lt_add_of_lt_of_le {x y z t : ereal} (h : x < y) (h' : z ≤ t) (hz : z ≠ ⊥) (ht : t ≠ ⊤) :
  x + z < y + t :=
begin
  induction z using ereal.rec,
  { simpa only using hz },
  { calc x + z < y + z : add_lt_add_right_coe h _
           ... ≤ y + t : add_le_add le_rfl h' },
  { exact (ht (top_le_iff.1 h')).elim }
end

lemma add_lt_add_left_coe {x y : ereal} (h : x < y) (z : ℝ) : (z : ereal) + x < z + y :=
by simpa [add_comm] using add_lt_add_right_coe h z

lemma add_lt_add {x y z t : ereal} (h1 : x < y) (h2 : z < t) : x + z < y + t :=
begin
  induction x using ereal.rec,
  { simp [bot_lt_iff_ne_bot, h1.ne', (bot_le.trans_lt h2).ne'] },
  { calc (x : ereal) + z < x + t : add_lt_add_left_coe h2 _
    ... ≤ y + t : add_le_add h1.le le_rfl },
  { exact (lt_irrefl _ (h1.trans_le le_top)).elim }
end

@[simp] lemma add_eq_bot_iff {x y : ereal} : x + y = ⊥ ↔ x = ⊥ ∨ y = ⊥ :=
begin
  induction x using ereal.rec; induction y using ereal.rec;
  simp [← ereal.coe_add],
end

@[simp] lemma bot_lt_add_iff {x y : ereal} : ⊥ < x + y ↔ ⊥ < x ∧ ⊥ < y :=
by simp [bot_lt_iff_ne_bot, not_or_distrib]

/-! ### Negation -/

/-- negation on `ereal` -/
protected def neg : ereal → ereal
| ⊥       := ⊤
| ⊤       := ⊥
| (x : ℝ) := (-x : ℝ)

instance : has_neg ereal := ⟨ereal.neg⟩

instance : sub_neg_zero_monoid ereal :=
{ neg_zero := by { change ((-0 : ℝ) : ereal) = 0, simp },
  ..ereal.add_monoid, ..ereal.has_neg }

@[norm_cast] protected lemma neg_def (x : ℝ) : ((-x : ℝ) : ereal) = -x := rfl

@[simp] lemma neg_top : - (⊤ : ereal) = ⊥ := rfl
@[simp] lemma neg_bot : - (⊥ : ereal) = ⊤ := rfl

@[simp, norm_cast] lemma coe_neg (x : ℝ) : (↑(-x) : ereal) = -x := rfl
@[simp, norm_cast] lemma coe_sub (x y : ℝ) : (↑(x - y) : ereal) = x - y := rfl
@[norm_cast] lemma coe_zsmul (n : ℤ) (x : ℝ) : (↑(n • x) : ereal) = n • x :=
map_zsmul' (⟨coe, coe_zero, coe_add⟩ : ℝ →+ ereal) coe_neg _ _

instance : has_involutive_neg ereal :=
{ neg := has_neg.neg,
  neg_neg := λ a, match a with
    | ⊥ := rfl
    | ⊤ := rfl
    | (a : ℝ) := by { norm_cast, simp [neg_neg a] }
    end }

@[simp] lemma to_real_neg : ∀ {a : ereal}, to_real (-a) = - to_real a
| ⊤ := by simp
| ⊥ := by simp
| (x : ℝ) := rfl

@[simp] lemma neg_eq_top_iff {x : ereal} : - x = ⊤ ↔ x = ⊥ :=
by { rw neg_eq_iff_neg_eq, simp [eq_comm] }

@[simp] lemma neg_eq_bot_iff {x : ereal} : - x = ⊥ ↔ x = ⊤ :=
by { rw neg_eq_iff_neg_eq, simp [eq_comm] }

@[simp] lemma neg_eq_zero_iff {x : ereal} : - x = 0 ↔ x = 0 :=
by { rw neg_eq_iff_neg_eq, simp [eq_comm] }

/-- if `-a ≤ b` then `-b ≤ a` on `ereal`. -/
protected theorem neg_le_of_neg_le {a b : ereal} (h : -a ≤ b) : -b ≤ a :=
begin
  induction a using ereal.rec; induction b using ereal.rec,
  { exact h },
  { simpa only [coe_ne_top, neg_bot, top_le_iff] using h },
  { exact bot_le },
  { simpa only [coe_ne_top, le_bot_iff] using h },
  { norm_cast at h ⊢, exact neg_le.1 h },
  { exact bot_le },
  { exact le_top },
  { exact le_top },
  { exact le_top },
end

/-- `-a ≤ b ↔ -b ≤ a` on `ereal`. -/
protected theorem neg_le {a b : ereal} : -a ≤ b ↔ -b ≤ a :=
⟨ereal.neg_le_of_neg_le, ereal.neg_le_of_neg_le⟩

/-- `a ≤ -b → b ≤ -a` on ereal -/
theorem le_neg_of_le_neg {a b : ereal} (h : a ≤ -b) : b ≤ -a :=
by rwa [←neg_neg b, ereal.neg_le, neg_neg]

@[simp] lemma neg_le_neg_iff {a b : ereal} : - a ≤ - b ↔ b ≤ a :=
by conv_lhs { rw [ereal.neg_le, neg_neg] }

/-- Negation as an order reversing isomorphism on `ereal`. -/
def neg_order_iso : ereal ≃o erealᵒᵈ :=
{ to_fun := λ x, order_dual.to_dual (-x),
  inv_fun := λ x, -x.of_dual,
  map_rel_iff' := λ x y, neg_le_neg_iff,
  ..equiv.neg ereal }

lemma neg_lt_of_neg_lt {a b : ereal} (h : -a < b) : -b < a :=
begin
  apply lt_of_le_of_ne (ereal.neg_le_of_neg_le h.le),
  assume H,
  rw [← H, neg_neg] at h,
  exact lt_irrefl _ h
end

lemma neg_lt_iff_neg_lt {a b : ereal} : -a < b ↔ -b < a :=
⟨λ h, ereal.neg_lt_of_neg_lt h, λ h, ereal.neg_lt_of_neg_lt h⟩

/-!
### Subtraction

Subtraction on `ereal` is defined by `x - y = x + (-y)`. Since addition is badly behaved at some
points, so is subtraction. There is no standard algebraic typeclass involving subtraction that is
registered on `ereal`, beyond `sub_neg_zero_monoid`, because of this bad behavior.
-/

@[simp] lemma top_sub (x : ereal) : ⊤ - x = ⊤ := top_add x
@[simp] lemma sub_bot (x : ereal) : x - ⊥ = ⊤ := add_top x

@[simp] lemma bot_sub_top : (⊥ : ereal) - ⊤ = ⊥ := rfl
@[simp] lemma bot_sub_coe (x : ℝ) : (⊥ : ereal) - x = ⊥ := rfl
@[simp] lemma coe_sub_bot (x : ℝ) : (x : ereal) - ⊤ = ⊥ := rfl

lemma sub_le_sub {x y z t : ereal} (h : x ≤ y) (h' : t ≤ z) : x - z ≤ y - t :=
add_le_add h (neg_le_neg_iff.2 h')

lemma sub_lt_sub_of_lt_of_le {x y z t : ereal} (h : x < y) (h' : z ≤ t) (hz : z ≠ ⊥) (ht : t ≠ ⊤) :
  x - t < y - z :=
add_lt_add_of_lt_of_le h (neg_le_neg_iff.2 h') (by simp [ht]) (by simp [hz])

lemma coe_real_ereal_eq_coe_to_nnreal_sub_coe_to_nnreal (x : ℝ) :
  (x : ereal) = real.to_nnreal x - real.to_nnreal (-x) :=
begin
  rcases le_or_lt 0 x with h|h,
  { have : real.to_nnreal x = ⟨x, h⟩, by { ext, simp [h] },
    simp only [real.to_nnreal_of_nonpos (neg_nonpos.mpr h), this, sub_zero, ennreal.coe_zero,
      coe_ennreal_zero, coe_coe],
    refl },
  { have : (x : ereal) = - (- x : ℝ), by simp,
    conv_lhs { rw this },
    have : real.to_nnreal (-x) = ⟨-x, neg_nonneg.mpr h.le⟩, by { ext, simp [neg_nonneg.mpr h.le], },
    simp only [real.to_nnreal_of_nonpos h.le, this, zero_sub, neg_inj, coe_neg,
      ennreal.coe_zero, coe_ennreal_zero, coe_coe],
    refl }
end

lemma to_real_sub {x y : ereal} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) (hy : y ≠ ⊤) (h'y : y ≠ ⊥) :
  to_real (x - y) = to_real x - to_real y :=
begin
  rw [sub_eq_add_neg, to_real_add hx h'x, to_real_neg],
  { refl },
  { simpa using hy },
  { simpa using h'y }
end

/-! ### Multiplication -/


@[simp] lemma mul_top (x : ereal) (h : x ≠ 0) : x * ⊤ = ⊤ := with_top.mul_top h
@[simp] lemma top_mul (x : ereal) (h : x ≠ 0) : ⊤ * x = ⊤ := with_top.top_mul h

@[simp] lemma bot_mul_bot : (⊥ : ereal) * ⊥ = ⊥ := rfl
@[simp] lemma bot_mul_coe (x : ℝ) (h : x ≠ 0) : (⊥ : ereal) * x = ⊥ :=
with_top.coe_mul.symm.trans $
  with_bot.coe_eq_coe.mpr $ with_bot.bot_mul $ function.injective.ne (@option.some.inj _) h
@[simp] lemma coe_mul_bot (x : ℝ) (h : x ≠ 0) : (x : ereal) * ⊥ = ⊥ :=
with_top.coe_mul.symm.trans $
  with_bot.coe_eq_coe.mpr $ with_bot.mul_bot $ function.injective.ne (@option.some.inj _) h

@[simp] lemma to_real_one : to_real 1 = 1 := rfl

lemma to_real_mul : ∀ {x y : ereal}, to_real (x * y) = to_real x * to_real y
| ⊤ y := by by_cases hy : y = 0; simp [hy]
| x ⊤ := by by_cases hx : x = 0; simp [hx]
| (x : ℝ) (y : ℝ) := by simp [← ereal.coe_mul]
| ⊥ (y : ℝ) := by by_cases hy : y = 0; simp [hy]
| (x : ℝ) ⊥ := by by_cases hx : x = 0; simp [hx]
| ⊥ ⊥ := by simp

end ereal

namespace tactic
open positivity

private lemma ereal_coe_ne_zero {r : ℝ} : r ≠ 0 → (r : ereal) ≠ 0 := ereal.coe_ne_zero.2
private lemma ereal_coe_nonneg {r : ℝ} : 0 ≤ r → 0 ≤ (r : ereal) := ereal.coe_nonneg.2
private lemma ereal_coe_pos {r : ℝ} : 0 < r → 0 < (r : ereal) := ereal.coe_pos.2
private lemma ereal_coe_ennreal_pos {r : ℝ≥0∞} : 0 < r → 0 < (r : ereal) := ereal.coe_ennreal_pos.2

/-- Extension for the `positivity` tactic: cast from `ℝ` to `ereal`. -/
@[positivity]
meta def positivity_coe_real_ereal : expr → tactic strictness
| `(@coe _ _ %%inst %%a) := do
  unify inst `(@coe_to_lift _ _ $ @coe_base _ _ ereal.has_coe),
  strictness_a ← core a,
  match strictness_a with
  | positive p := positive <$> mk_app ``ereal_coe_pos [p]
  | nonnegative p := nonnegative <$> mk_mapp ``ereal_coe_nonneg [a, p]
  | nonzero p := nonzero <$> mk_mapp ``ereal_coe_ne_zero [a, p]
  end
| e := pp e >>= fail ∘ format.bracket "The expression "
         " is not of the form `(r : ereal)` for `r : ℝ`"

/-- Extension for the `positivity` tactic: cast from `ℝ≥0∞` to `ereal`. -/
@[positivity]
meta def positivity_coe_ennreal_ereal : expr → tactic strictness
| `(@coe _ _ %%inst %%a) := do
  unify inst `(@coe_to_lift _ _ $ @coe_base _ _ ereal.has_coe_ennreal),
  strictness_a ← core a,
  match strictness_a with
  | positive p := positive <$> mk_app ``ereal_coe_ennreal_pos [p]
  | _ := nonnegative <$> mk_mapp `ereal.coe_ennreal_nonneg [a]
  end
| e := pp e >>= fail ∘ format.bracket "The expression "
         " is not of the form `(r : ereal)` for `r : ℝ≥0∞`"

end tactic
