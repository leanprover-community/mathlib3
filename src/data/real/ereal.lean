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
referred to as ⊤ and ⊥. It is implemented as `with_top (with_bot ℝ)`

Addition and multiplication are problematic in the presence of ±∞, but
negation has a natural definition and satisfies the usual properties.
An addition is derived, but `ereal` is not even a monoid (there is no identity).

`ereal` is a `complete_lattice`; this is now deduced by type class inference from
the fact that `with_top (with_bot L)` is a complete lattice if `L` is
a conditionally complete lattice.

## Tags

real, ereal, complete lattice

## TODO

abs : ereal → ℝ≥0∞

In Isabelle they define + - * and / (making junk choices for things like -∞ + ∞)
and then prove whatever bits of the ordered ring/field axioms still hold. They
also do some limits stuff (liminf/limsup etc).
See https://isabelle.in.tum.de/dist/library/HOL/HOL-Library/Extended_Real.html
-/

open_locale ennreal nnreal

/-- ereal : The type `[-∞, ∞]` -/
@[derive [order_bot, order_top,
  has_Sup, has_Inf, complete_lattice, linear_ordered_add_comm_monoid_with_top]]
def ereal := with_top (with_bot ℝ)

namespace ereal
instance : has_coe ℝ ereal := ⟨some ∘ some⟩
@[simp, norm_cast] protected lemma coe_le_coe_iff {x y : ℝ} : (x : ereal) ≤ (y : ereal) ↔ x ≤ y :=
by { unfold_coes, norm_num }
@[simp, norm_cast] protected lemma coe_lt_coe_iff {x y : ℝ} : (x : ereal) < (y : ereal) ↔ x < y :=
by { unfold_coes, norm_num }
@[simp, norm_cast] protected lemma coe_real_inj' {x y : ℝ} : (x : ereal) = (y : ereal) ↔ x = y :=
by { unfold_coes, simp [option.some_inj] }

def _root_.ennreal.to_ereal : ℝ≥0∞ → ereal
| ⊤ := ⊤
| (some x) := x.1

instance has_coe_ennreal : has_coe ℝ≥0∞ ereal := ⟨ennreal.to_ereal⟩

instance : has_zero ereal := ⟨(0 : ℝ)⟩
instance : inhabited ereal := ⟨0⟩

/-- A way to case on an element of `ereal`, separating the bot, real and top cases.
A typical invocation looks like `rcases x.cases with rfl|⟨x, rfl⟩|rfl` -/
protected lemma cases : ∀ (a : ereal), a = ⊥ ∨ (∃ (x : ℝ), a = x) ∨ a = ⊤
| ⊤ := by simp
| ⊥ := by simp
| (a : ℝ) := by simp

/-! ### Real coercion -/

def to_real : ereal → ℝ
| ⊥       := 0
| ⊤       := 0
| (x : ℝ) := x

@[simp] lemma to_real_top : to_real ⊤ = 0 := rfl
@[simp] lemma to_real_bot : to_real ⊥ = 0 := rfl
@[simp] lemma to_real_coe (x : ℝ) : to_real (x : ereal) = x := rfl

@[simp] lemma bot_lt_coe (x : ℝ) : (⊥ : ereal) < x :=
by { apply with_top.coe_lt_coe.2, exact with_bot.bot_lt_coe _ }
@[simp] lemma coe_ne_bot (x : ℝ) : (x : ereal) ≠ ⊥  := (bot_lt_coe x).ne.symm
@[simp] lemma bot_lt_top : (⊥ : ereal) < ⊤ := with_top.coe_lt_top _
lemma bot_ne_top : (⊥ : ereal) ≠ ⊤ := bot_lt_top.ne
@[simp] lemma coe_lt_top (x : ℝ) : (x : ereal) < ⊤ := with_top.coe_lt_top _
@[simp] lemma coe_ne_top (x : ℝ) : (x : ereal) ≠ ⊤ := (coe_lt_top x).ne

@[simp, norm_cast] lemma coe_add (x y : ℝ) : ((x + y : ℝ) : ereal) = (x : ereal) + (y : ereal) :=
rfl

@[simp] lemma coe_zero : ((0 : ℝ) : ereal) = 0 := rfl

/-! ### ennreal coercion -/

@[simp] lemma coe_ennreal_top : ((⊤ : ℝ≥0∞) : ereal) = ⊤ := rfl
lemma coe_ennreal_nonneg : ∀ (x : ℝ≥0∞), (0 : ereal) ≤ x
| ⊤ := le_top
| (some x) :=
    begin
      change ((0 : ℝ) : ereal) ≤ x.1,
      rw ereal.coe_le_coe_iff,
      exact x.2
    end

@[simp] lemma coe_nnreal_ne_top (x : ℝ≥0) : ((x : ℝ≥0∞) : ereal) ≠ ⊤ := dec_trivial

@[simp, norm_cast] lemma coe_ennreal_add : ∀ (x y : ennreal), ((x + y : ℝ≥0∞) : ereal) = x + y
| ⊤ y := rfl
| x ⊤ := by simp
| (some x) (some y) := rfl

@[simp] lemma coe_ennreal_zero : ((0 : ℝ≥0∞) : ereal) = 0 := rfl

@[simp, norm_cast] lemma coe_ennreal_le_coe_ennreal_iff : ∀ {x y : ℝ≥0∞}, (x : ereal) ≤ y ↔ x ≤ y
| x ⊤ := by simp
| ⊤ (some y) := by simp
| (some x) (some y) :=
  begin
     simp only [ennreal.coe_le_coe, ennreal.some_eq_coe],
     change (x.1 : ereal) ≤ (y.1 : ereal) ↔ x ≤ y,
     simp,
  end

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

/-! ### Addition -/

@[simp] lemma add_top (x : ereal) : x + ⊤ = ⊤ := add_top _
@[simp] lemma top_add (x : ereal) : ⊤ + x = ⊤ := top_add _

@[simp] lemma bot_add_bot : (⊥ : ereal) + ⊥ = ⊥ := rfl
@[simp] lemma bot_add_coe (x : ℝ) : (⊥ : ereal) + x = ⊥ := rfl
@[simp] lemma coe_add_bot (x : ℝ) : (x : ereal) + ⊥ = ⊥ := rfl

lemma add_lt_add_right_coe {x y : ereal} (h : x < y) (z : ℝ) : x + z < y + z :=
begin
  rcases x.cases with rfl|⟨x, rfl⟩|rfl; rcases y.cases with rfl|⟨y, rfl⟩|rfl,
  { exact (lt_irrefl _ h).elim },
  { simp only [bot_lt_coe, bot_add_coe, ← coe_add] },
  { simp },
  { exact (lt_irrefl _ (h.trans (bot_lt_coe x))).elim },
  { norm_cast at h ⊢, exact add_lt_add_right h _ },
  { simp only [← coe_add, top_add, coe_lt_top] },
  { exact (lt_irrefl _ (h.trans_le le_top)).elim },
  { exact (lt_irrefl _ (h.trans_le le_top)).elim },
  { exact (lt_irrefl _ (h.trans_le le_top)).elim },
end

lemma add_lt_add_left_coe {x y : ereal} (h : x < y) (z : ℝ) : (z : ereal) + x < z + y :=
by simpa [add_comm] using add_lt_add_right_coe h z

lemma add_lt_add {x y z t : ereal} (h1 : x < y) (h2 : z < t) : x + z < y + t :=
begin
  rcases y.cases with rfl|⟨y, rfl⟩|rfl,
  { exact (lt_irrefl _ (bot_le.trans_lt h1)).elim },
  { calc x + z ≤ y + z : add_le_add h1.le (le_refl _)
    ... < y + t : add_lt_add_left_coe h2 _ },
  { simp [lt_top_iff_ne_top, with_top.add_eq_top, h1.ne, (h2.trans_le le_top).ne] }
end

/-! ### Negation -/

/-- negation on ereal -/
protected def neg : ereal → ereal
| ⊥       := ⊤
| ⊤       := ⊥
| (x : ℝ) := (-x : ℝ)

instance : has_neg ereal := ⟨ereal.neg⟩

@[norm_cast] protected lemma neg_def (x : ℝ) : ((-x : ℝ) : ereal) = -x := rfl

@[simp] lemma neg_top : - (⊤ : ereal) = ⊥ := rfl
@[simp] lemma neg_bot : - (⊥ : ereal) = ⊤ := rfl
@[simp] lemma neg_zero : - (0 : ereal) = 0 := by { change ((-0 : ℝ) : ereal) = 0, simp }

/-- - -a = a on ereal -/
@[simp] protected theorem neg_neg : ∀ (a : ereal), - (- a) = a
| ⊥ := rfl
| ⊤ := rfl
| (a : ℝ) := by { norm_cast, simp [neg_neg a] }

theorem neg_inj {a b : ereal} (h : -a = -b) : a = b := by rw [←ereal.neg_neg a, h, ereal.neg_neg b]

@[simp] theorem neg_eq_neg_iff (a b : ereal) : - a = - b ↔ a = b :=
⟨λ h, neg_inj h, λ h, by rw [h]⟩

/-- Even though ereal is not an additive group, -a = b ↔ -b = a still holds -/
theorem neg_eq_iff_neg_eq {a b : ereal} : -a = b ↔ -b = a :=
⟨by {intro h, rw ←h, exact ereal.neg_neg a},
 by {intro h, rw ←h, exact ereal.neg_neg b}⟩

/-- if -a ≤ b then -b ≤ a on ereal -/
protected theorem neg_le_of_neg_le : ∀ {a b : ereal} (h : -a ≤ b), -b ≤ a
| ⊥ ⊥ h := h
| ⊥ (some b) h := by cases (top_le_iff.1 h)
| ⊤ l h := le_top
| (a : ℝ) ⊥ h := by cases (le_bot_iff.1 h)
| l ⊤ h := bot_le
| (a : ℝ) (b : ℝ) h := by { norm_cast at h ⊢, exact _root_.neg_le_of_neg_le h }

/-- -a ≤ b ↔ -b ≤ a on ereal-/
protected theorem neg_le {a b : ereal} : -a ≤ b ↔ -b ≤ a :=
⟨ereal.neg_le_of_neg_le, ereal.neg_le_of_neg_le⟩

/-- a ≤ -b → b ≤ -a on ereal -/
theorem le_neg_of_le_neg {a b : ereal} (h : a ≤ -b) : b ≤ -a :=
by rwa [←ereal.neg_neg b, ereal.neg_le, ereal.neg_neg]

@[simp] lemma neg_le_neg_iff {a b : ereal} : - a ≤ - b ↔ b ≤ a :=
by conv_lhs { rw [ereal.neg_le, ereal.neg_neg] }

@[simp, norm_cast] lemma coe_neg (x : ℝ) : ((- x : ℝ) : ereal) = - (x : ereal) := rfl

protected noncomputable def sub (x y : ereal) : ereal := x + (-y)
noncomputable instance : has_sub ereal := ⟨ereal.sub⟩

@[simp] lemma sub_zero (x : ereal) : x - 0 = x := by { change x + (-0) = x, simp }
@[simp] lemma zero_sub (x : ereal) : 0 - x = - x := by { change 0 + (-x) = - x, simp }

lemma sub_le_sub {x y z t : ereal} (h : x ≤ y) (h' : t ≤ z) : x - z ≤ y - t :=
add_le_add h (neg_le_neg_iff.2 h')

lemma coe_eq_coe_ennreal_sub_coe_ennreal (x : ℝ) :
  (x : ereal) = nnreal.of_real x - nnreal.of_real (-x) :=
begin
  rcases le_or_lt 0 x with h|h,
  { have : nnreal.of_real x = ⟨x, h⟩, by { ext, simp [h] },
    simp only [nnreal.of_real_of_nonpos (neg_nonpos.mpr h), this, sub_zero, ennreal.coe_zero,
      coe_ennreal_zero, coe_coe],
    refl },
  { have : (x : ereal) = - (- x : ℝ), by simp,
    conv_lhs { rw this },
    have : nnreal.of_real (-x) = ⟨-x, neg_nonneg.mpr h.le⟩, by { ext, simp [neg_nonneg.mpr h.le], },
    simp only [nnreal.of_real_of_nonpos h.le, this, zero_sub, neg_eq_neg_iff, coe_neg,
      ennreal.coe_zero, coe_ennreal_zero, coe_coe],
    refl }
end

end ereal
