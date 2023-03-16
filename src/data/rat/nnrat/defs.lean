/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import algebra.order.nonneg.ring
import data.int.lemmas
import data.rat.order

/-!
# Nonnegative rationals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the nonnegative rationals as a subtype of `rat` and provides its algebraic order
structure.

We also define an instance `can_lift ℚ ℚ≥0`. This instance can be used by the `lift` tactic to
replace `x : ℚ` and `hx : 0 ≤ x` in the proof context with `x : ℚ≥0` while replacing all occurences
of `x` with `↑x`. This tactic also works for a function `f : α → ℚ` with a hypothesis
`hf : ∀ x, 0 ≤ f x`.

## Notation

`ℚ≥0` is notation for `nnrat` in locale `nnrat`.
-/

open function

variables {α : Type*}

/-- Nonnegative rational numbers. -/
@[derive [canonically_ordered_comm_semiring, canonically_linear_ordered_add_monoid, has_sub,
  has_ordered_sub, inhabited]]
def nnrat := {q : ℚ // 0 ≤ q}

localized "notation (name := nnrat) `ℚ≥0` := nnrat" in nnrat

/-- Type class for the canonical homomorphism `ℚ≥0 → α`. -/
@[protect_proj]
class has_nnrat_cast (α : Type*) :=
(nnrat_cast : ℚ≥0 → α)

namespace nnrat
variables {p q : ℚ≥0}

/-- Construct the canonical injection from `ℚ≥0` into an arbitrary division semiring. If the
semifield has positive characteristic `p`, we define `1 / p = 1 / 0 = 0` for consistency with our
division by zero convention. -/
@[priority 900] -- see Note [coercion into rings]
instance cast_coe [has_nnrat_cast α] : has_coe_t ℚ≥0 α := ⟨has_nnrat_cast.nnrat_cast⟩

instance : has_nnrat_cast ℚ := ⟨subtype.val⟩

/- Simp lemma to put back `n.val` into the normal form given by the coercion. -/
@[simp] lemma val_eq_coe (q : ℚ≥0) : q.val = q := rfl

instance can_lift : can_lift ℚ ℚ≥0 coe (λ q, 0 ≤ q) :=
{ prf := λ q hq, ⟨⟨q, hq⟩, rfl⟩ }

@[ext] lemma ext : (p : ℚ) = (q : ℚ) → p = q := subtype.ext

protected lemma coe_injective : injective (coe : ℚ≥0 → ℚ) := subtype.coe_injective

@[simp, norm_cast] lemma coe_inj : (p : ℚ) = q ↔ p = q := subtype.coe_inj

lemma ext_iff : p = q ↔ (p : ℚ) = q := subtype.ext_iff

lemma ne_iff {x y : ℚ≥0} : (x : ℚ) ≠ (y : ℚ) ↔ x ≠ y := nnrat.coe_inj.not

@[norm_cast] lemma coe_mk (q : ℚ) (hq) : ((⟨q, hq⟩ : ℚ≥0) : ℚ) = q := rfl

/-- Reinterpret a rational number `q` as a non-negative rational number. Returns `0` if `q ≤ 0`. -/
def _root_.rat.to_nnrat (q : ℚ) : ℚ≥0 := ⟨max q 0, le_max_right _ _⟩

lemma _root_.rat.coe_to_nnrat (q : ℚ) (hq : 0 ≤ q) : (q.to_nnrat : ℚ) = q := max_eq_left hq

lemma _root_.rat.le_coe_to_nnrat (q : ℚ) : q ≤ q.to_nnrat := le_max_left _ _

open _root_.rat (to_nnrat)

@[simp] lemma coe_nonneg (q : ℚ≥0) : (0 : ℚ) ≤ q := q.2

@[simp, norm_cast] lemma coe_zero : ((0 : ℚ≥0) : ℚ) = 0 := rfl
@[simp, norm_cast] lemma coe_one  : ((1 : ℚ≥0) : ℚ) = 1 := rfl
@[simp, norm_cast] lemma coe_add (p q : ℚ≥0) : ((p + q : ℚ≥0) : ℚ) = p + q := rfl
@[simp, norm_cast] lemma coe_mul (p q : ℚ≥0) : ((p * q : ℚ≥0) : ℚ) = p * q := rfl
@[simp, norm_cast] lemma coe_bit0 (q : ℚ≥0) : ((bit0 q : ℚ≥0) : ℚ) = bit0 q := rfl
@[simp, norm_cast] lemma coe_bit1 (q : ℚ≥0) : ((bit1 q : ℚ≥0) : ℚ) = bit1 q := rfl
@[simp, norm_cast] lemma coe_sub (h : q ≤ p) : ((p - q : ℚ≥0) : ℚ) = p - q :=
max_eq_left $ le_sub_comm.2 $ by simp [show (q : ℚ) ≤ p, from h]

@[simp, norm_cast] lemma coe_eq_zero : (q : ℚ) = 0 ↔ q = 0 := by norm_cast
lemma coe_ne_zero : (q : ℚ) ≠ 0 ↔ q ≠ 0 := coe_eq_zero.not

@[simp, norm_cast] lemma coe_eq_one : (q : ℚ) = 1 ↔ q = 1 := by norm_cast
lemma coe_ne_one : (q : ℚ) ≠ 1 ↔ q ≠ 1 := coe_eq_one.not

@[simp, norm_cast] lemma coe_le_coe : (p : ℚ) ≤ q ↔ p ≤ q := iff.rfl
@[simp, norm_cast] lemma coe_lt_coe : (p : ℚ) < q ↔ p < q := iff.rfl
@[simp, norm_cast] lemma coe_pos : (0 : ℚ) < q ↔ 0 < q := iff.rfl

lemma coe_mono : monotone (coe : ℚ≥0 → ℚ) := λ _ _, coe_le_coe.2

lemma to_nnrat_mono : monotone to_nnrat := λ x y h, max_le_max h le_rfl

@[simp] lemma to_nnrat_coe (q : ℚ≥0) : to_nnrat q = q := ext $ max_eq_left q.2

@[simp] lemma to_nnrat_coe_nat (n : ℕ) : to_nnrat n = n :=
ext $ by simp [rat.coe_to_nnrat]

/-- `to_nnrat` and `coe : ℚ≥0 → ℚ` form a Galois insertion. -/
protected def gi : galois_insertion to_nnrat coe :=
galois_insertion.monotone_intro coe_mono to_nnrat_mono rat.le_coe_to_nnrat to_nnrat_coe

lemma bdd_above_coe {s : set ℚ≥0} : bdd_above (coe '' s : set ℚ) ↔ bdd_above s :=
⟨λ ⟨b, hb⟩, ⟨to_nnrat b, λ ⟨y, hy⟩ hys, show y ≤ max b 0, from
    (hb $ set.mem_image_of_mem _ hys).trans $ le_max_left _ _⟩,
  λ ⟨b, hb⟩, ⟨b, λ y ⟨x, hx, eq⟩, eq ▸ hb hx⟩⟩

lemma bdd_below_coe (s : set ℚ≥0) : bdd_below ((coe : ℚ≥0 → ℚ) '' s) := ⟨0, λ r ⟨q, _, h⟩, h ▸ q.2⟩

@[simp, norm_cast] lemma coe_max (x y : ℚ≥0) : ((max x y : ℚ≥0) : ℚ) = max (x : ℚ) (y : ℚ) := rfl
@[simp, norm_cast] lemma coe_min (x y : ℚ≥0) : ((min x y : ℚ≥0) : ℚ) = min (x : ℚ) (y : ℚ) := rfl

lemma sub_def (p q : ℚ≥0) : p - q = to_nnrat (p - q) := rfl

@[simp] lemma abs_coe (q : ℚ≥0) : |(q : ℚ)| = q := abs_of_nonneg q.2

end nnrat

open nnrat

namespace rat
variables {p q : ℚ}

@[simp] lemma to_nnrat_zero : to_nnrat 0 = 0 := by simp [to_nnrat]; refl
@[simp] lemma to_nnrat_one : to_nnrat 1 = 1 := by simp [to_nnrat, max_eq_left zero_le_one]

@[simp] lemma to_nnrat_pos : 0 < to_nnrat q ↔ 0 < q := by simp [to_nnrat, ←coe_lt_coe]

@[simp] lemma to_nnrat_eq_zero : to_nnrat q = 0 ↔ q ≤ 0 :=
by simpa [-to_nnrat_pos] using (@to_nnrat_pos q).not

alias to_nnrat_eq_zero ↔ _ to_nnrat_of_nonpos

@[simp] lemma to_nnrat_le_to_nnrat_iff (hp : 0 ≤ p) : to_nnrat q ≤ to_nnrat p ↔ q ≤ p :=
by simp [←coe_le_coe, to_nnrat, hp]

@[simp] lemma to_nnrat_lt_to_nnrat_iff' : to_nnrat q < to_nnrat p ↔ q < p ∧ 0 < p :=
by { simp [←coe_lt_coe, to_nnrat, lt_irrefl], exact lt_trans' }

lemma to_nnrat_lt_to_nnrat_iff (h : 0 < p) : to_nnrat q < to_nnrat p ↔ q < p :=
to_nnrat_lt_to_nnrat_iff'.trans (and_iff_left h)

lemma to_nnrat_lt_to_nnrat_iff_of_nonneg (hq : 0 ≤ q) : to_nnrat q < to_nnrat p ↔ q < p :=
to_nnrat_lt_to_nnrat_iff'.trans ⟨and.left, λ h, ⟨h, hq.trans_lt h⟩⟩

@[simp] lemma to_nnrat_add (hq : 0 ≤ q) (hp : 0 ≤ p) : to_nnrat (q + p) = to_nnrat q + to_nnrat p :=
nnrat.ext $ by simp [to_nnrat, hq, hp, add_nonneg]

lemma to_nnrat_add_le : to_nnrat (q + p) ≤ to_nnrat q + to_nnrat p :=
coe_le_coe.1 $ max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) $ coe_nonneg _

lemma to_nnrat_le_iff_le_coe {p : ℚ≥0} : to_nnrat q ≤ p ↔ q ≤ ↑p := nnrat.gi.gc q p

lemma le_to_nnrat_iff_coe_le {q : ℚ≥0} (hp : 0 ≤ p) : q ≤ to_nnrat p ↔ ↑q ≤ p :=
by rw [←coe_le_coe, rat.coe_to_nnrat p hp]

lemma le_to_nnrat_iff_coe_le' {q : ℚ≥0} (hq : 0 < q) : q ≤ to_nnrat p ↔ ↑q ≤ p :=
(le_or_lt 0 p).elim le_to_nnrat_iff_coe_le $ λ hp,
  by simp only [(hp.trans_le q.coe_nonneg).not_le, to_nnrat_eq_zero.2 hp.le, hq.not_le]

lemma to_nnrat_lt_iff_lt_coe {p : ℚ≥0} (hq : 0 ≤ q) : to_nnrat q < p ↔ q < ↑p :=
by rw [←coe_lt_coe, rat.coe_to_nnrat q hq]

lemma lt_to_nnrat_iff_coe_lt {q : ℚ≥0} : q < to_nnrat p ↔ ↑q < p := nnrat.gi.gc.lt_iff_lt

@[simp] lemma to_nnrat_bit0 (hq : 0 ≤ q) : to_nnrat (bit0 q) = bit0 (to_nnrat q) :=
to_nnrat_add hq hq

@[simp] lemma to_nnrat_bit1 (hq : 0 ≤ q) : to_nnrat (bit1 q) = bit1 (to_nnrat q) :=
(to_nnrat_add (by simp [hq]) zero_le_one).trans $ by simp [to_nnrat_one, bit1, hq]

lemma to_nnrat_mul (hp : 0 ≤ p) : to_nnrat (p * q) = to_nnrat p * to_nnrat q :=
begin
  cases le_total 0 q with hq hq,
  { ext; simp [to_nnrat, hp, hq, max_eq_left, mul_nonneg] },
  { have hpq := mul_nonpos_of_nonneg_of_nonpos hp hq,
    rw [to_nnrat_eq_zero.2 hq, to_nnrat_eq_zero.2 hpq, mul_zero] }
end

end rat

/-- The absolute value on `ℚ` as a map to `ℚ≥0`. -/
@[pp_nodot] def rat.nnabs (x : ℚ) : ℚ≥0 := ⟨abs x, abs_nonneg x⟩

@[norm_cast, simp] lemma rat.coe_nnabs (x : ℚ) : (rat.nnabs x : ℚ) = abs x := by simp [rat.nnabs]

/-! ### Numerator and denominator -/

namespace nnrat
variables {p q : ℚ≥0}

/-- The numerator of a nonnegative rational. -/
def num (q : ℚ≥0) : ℕ := (q : ℚ).num.nat_abs

/-- The denominator of a nonnegative rational. -/
def denom (q : ℚ≥0) : ℕ := (q : ℚ).denom

@[simp] lemma nat_abs_num_coe : (q : ℚ).num.nat_abs = q.num := rfl
@[simp] lemma denom_coe : (q : ℚ).denom = q.denom := rfl

lemma ext_num_denom (hn : p.num = q.num) (hd : p.denom = q.denom) : p = q :=
ext $ rat.ext ((int.nat_abs_inj_of_nonneg_of_nonneg
  (rat.num_nonneg_iff_zero_le.2 p.2) $ rat.num_nonneg_iff_zero_le.2 q.2).1 hn) hd

lemma ext_num_denom_iff : p = q ↔ p.num = q.num ∧ p.denom = q.denom :=
⟨by { rintro rfl, exact ⟨rfl, rfl⟩ }, λ h, ext_num_denom h.1 h.2⟩

@[simp, norm_cast] lemma num_coe_nat (n : ℕ) : (n : ℚ≥0).num = n := by simp [num]
@[simp, norm_cast] lemma denom_coe_nat (n : ℕ) : (n : ℚ≥0).denom = 1 := by simp [denom]

/-- The default definition of the coercion `ℚ≥0 → α` for a division semiring `α` is defined
as `(a / b : α) = (a : α) * (b : α)⁻¹`. Use `coe` instead of `nnrat.cast_rec` for better
definitional behaviour. -/
def cast_rec [has_lift_t ℕ α] [has_mul α] [has_inv α] : ℚ≥0 → α := λ q, ↑q.num * (↑q.denom)⁻¹

end nnrat
