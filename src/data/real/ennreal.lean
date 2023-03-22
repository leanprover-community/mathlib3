/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import data.real.nnreal
import algebra.order.sub.with_top

/-!
# Extended non-negative reals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define `ennreal = ℝ≥0∞ := with_top ℝ≥0` to be the type of extended nonnegative real numbers,
i.e., the interval `[0, +∞]`. This type is used as the codomain of a `measure_theory.measure`,
and of the extended distance `edist` in a `emetric_space`.
In this file we define some algebraic operations and a linear order on `ℝ≥0∞`
and prove basic properties of these operations, order, and conversions to/from `ℝ`, `ℝ≥0`, and `ℕ`.

## Main definitions

* `ℝ≥0∞`: the extended nonnegative real numbers `[0, ∞]`; defined as `with_top ℝ≥0`; it is
  equipped with the following structures:

  - coercion from `ℝ≥0` defined in the natural way;

  - the natural structure of a complete dense linear order: `↑p ≤ ↑q ↔ p ≤ q` and `∀ a, a ≤ ∞`;

  - `a + b` is defined so that `↑p + ↑q = ↑(p + q)` for `(p q : ℝ≥0)` and `a + ∞ = ∞ + a = ∞`;

  - `a * b` is defined so that `↑p * ↑q = ↑(p * q)` for `(p q : ℝ≥0)`, `0 * ∞ = ∞ * 0 = 0`, and `a *
    ∞ = ∞ * a = ∞` for `a ≠ 0`;

  - `a - b` is defined as the minimal `d` such that `a ≤ d + b`; this way we have
    `↑p - ↑q = ↑(p - q)`, `∞ - ↑p = ∞`, `↑p - ∞ = ∞ - ∞ = 0`; note that there is no negation, only
    subtraction;

  - `a⁻¹` is defined as `Inf {b | 1 ≤ a * b}`. This way we have `(↑p)⁻¹ = ↑(p⁻¹)` for
    `p : ℝ≥0`, `p ≠ 0`, `0⁻¹ = ∞`, and `∞⁻¹ = 0`.

  - `a / b` is defined as `a * b⁻¹`.

  The addition and multiplication defined this way together with `0 = ↑0` and `1 = ↑1` turn
  `ℝ≥0∞` into a canonically ordered commutative semiring of characteristic zero.

* Coercions to/from other types:

  - coercion `ℝ≥0 → ℝ≥0∞` is defined as `has_coe`, so one can use `(p : ℝ≥0)` in a context that
    expects `a : ℝ≥0∞`, and Lean will apply `coe` automatically;

  - `ennreal.to_nnreal` sends `↑p` to `p` and `∞` to `0`;

  - `ennreal.to_real := coe ∘ ennreal.to_nnreal` sends `↑p`, `p : ℝ≥0` to `(↑p : ℝ)` and `∞` to `0`;

  - `ennreal.of_real := coe ∘ real.to_nnreal` sends `x : ℝ` to `↑⟨max x 0, _⟩`

  - `ennreal.ne_top_equiv_nnreal` is an equivalence between `{a : ℝ≥0∞ // a ≠ 0}` and `ℝ≥0`.

## Implementation notes

We define a `can_lift ℝ≥0∞ ℝ≥0` instance, so one of the ways to prove theorems about an `ℝ≥0∞`
number `a` is to consider the cases `a = ∞` and `a ≠ ∞`, and use the tactic `lift a to ℝ≥0 using ha`
in the second case. This instance is even more useful if one already has `ha : a ≠ ∞` in the
context, or if we have `(f : α → ℝ≥0∞) (hf : ∀ x, f x ≠ ∞)`.

## Notations

* `ℝ≥0∞`: the type of the extended nonnegative real numbers;
* `ℝ≥0`: the type of nonnegative real numbers `[0, ∞)`; defined in `data.real.nnreal`;
* `∞`: a localized notation in `ℝ≥0∞` for `⊤ : ℝ≥0∞`.

-/
open classical set

open_locale classical big_operators nnreal
variables {α : Type*} {β : Type*}

/-- The extended nonnegative real numbers. This is usually denoted [0, ∞],
  and is relevant as the codomain of a measure. -/
@[derive [
  has_zero, add_comm_monoid_with_one,
  semilattice_sup, distrib_lattice, order_bot, bounded_order,
  canonically_ordered_comm_semiring, complete_linear_order, densely_ordered, nontrivial,
  canonically_linear_ordered_add_monoid, has_sub, has_ordered_sub,
  linear_ordered_add_comm_monoid_with_top, char_zero]]
def ennreal := with_top ℝ≥0

localized "notation (name := ennreal) `ℝ≥0∞` := ennreal" in ennreal
localized "notation (name := ennreal.top) `∞` := (⊤ : ennreal)" in ennreal

namespace ennreal
variables {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

-- TODO: why are the two covariant instances necessary? why aren't they inferred?
instance covariant_class_mul_le : covariant_class ℝ≥0∞ ℝ≥0∞ (*) (≤) :=
canonically_ordered_comm_semiring.to_covariant_mul_le

instance covariant_class_add_le : covariant_class ℝ≥0∞ ℝ≥0∞ (+) (≤) :=
ordered_add_comm_monoid.to_covariant_class_left ℝ≥0∞

noncomputable instance : linear_ordered_comm_monoid_with_zero ℝ≥0∞ :=
{ mul_le_mul_left := λ a b, mul_le_mul_left',
  zero_le_one := zero_le 1,
  .. ennreal.linear_ordered_add_comm_monoid_with_top,
  .. (show comm_semiring ℝ≥0∞, from infer_instance) }

instance : inhabited ℝ≥0∞ := ⟨0⟩

instance : has_coe ℝ≥0 ℝ≥0∞ := ⟨ option.some ⟩

instance can_lift : can_lift ℝ≥0∞ ℝ≥0 coe (λ r, r ≠ ∞) :=
{ prf := λ x hx, ⟨option.get $ option.ne_none_iff_is_some.1 hx, option.some_get _⟩ }

@[simp] lemma none_eq_top : (none : ℝ≥0∞) = ∞ := rfl
@[simp] lemma some_eq_coe (a : ℝ≥0) : (some a : ℝ≥0∞) = (↑a : ℝ≥0∞) := rfl

/-- `to_nnreal x` returns `x` if it is real, otherwise 0. -/
protected def to_nnreal : ℝ≥0∞ → ℝ≥0 := with_top.untop' 0

/-- `to_real x` returns `x` if it is real, `0` otherwise. -/
protected def to_real (a : ℝ≥0∞) : real := coe (a.to_nnreal)

/-- `of_real x` returns `x` if it is nonnegative, `0` otherwise. -/
protected noncomputable def of_real (r : real) : ℝ≥0∞ := coe (real.to_nnreal r)

@[simp, norm_cast] lemma to_nnreal_coe : (r : ℝ≥0∞).to_nnreal = r := rfl

@[simp] lemma coe_to_nnreal : ∀{a:ℝ≥0∞}, a ≠ ∞ → ↑(a.to_nnreal) = a
| (some r) h := rfl
| none     h := (h rfl).elim

@[simp] lemma of_real_to_real {a : ℝ≥0∞} (h : a ≠ ∞) : ennreal.of_real (a.to_real) = a :=
by simp [ennreal.to_real, ennreal.of_real, h]

@[simp] lemma to_real_of_real {r : ℝ} (h : 0 ≤ r) : ennreal.to_real (ennreal.of_real r) = r :=
by simp [ennreal.to_real, ennreal.of_real, real.coe_to_nnreal _ h]

lemma to_real_of_real' {r : ℝ} : ennreal.to_real (ennreal.of_real r) = max r 0 := rfl

lemma coe_to_nnreal_le_self : ∀{a:ℝ≥0∞}, ↑(a.to_nnreal) ≤ a
| (some r) := by rw [some_eq_coe, to_nnreal_coe]; exact le_rfl
| none     := le_top

lemma coe_nnreal_eq (r : ℝ≥0) : (r : ℝ≥0∞) = ennreal.of_real r :=
by { rw [ennreal.of_real, real.to_nnreal], cases r with r h, congr, dsimp, rw max_eq_left h }

lemma of_real_eq_coe_nnreal {x : ℝ} (h : 0 ≤ x) :
  ennreal.of_real x = @coe ℝ≥0 ℝ≥0∞ _ (⟨x, h⟩ : ℝ≥0) :=
by { rw [coe_nnreal_eq], refl }

@[simp] lemma of_real_coe_nnreal : ennreal.of_real p = p := (coe_nnreal_eq p).symm

@[simp, norm_cast] lemma coe_zero : ↑(0 : ℝ≥0) = (0 : ℝ≥0∞) := rfl
@[simp, norm_cast] lemma coe_one : ↑(1 : ℝ≥0) = (1 : ℝ≥0∞) := rfl

@[simp] lemma to_real_nonneg {a : ℝ≥0∞} : 0 ≤ a.to_real := by simp [ennreal.to_real]

@[simp] lemma top_to_nnreal : ∞.to_nnreal = 0 := rfl
@[simp] lemma top_to_real : ∞.to_real = 0 := rfl
@[simp] lemma one_to_real : (1 : ℝ≥0∞).to_real = 1 := rfl
@[simp] lemma one_to_nnreal : (1 : ℝ≥0∞).to_nnreal = 1 := rfl
@[simp] lemma coe_to_real (r : ℝ≥0) : (r : ℝ≥0∞).to_real = r := rfl
@[simp] lemma zero_to_nnreal : (0 : ℝ≥0∞).to_nnreal = 0 := rfl
@[simp] lemma zero_to_real : (0 : ℝ≥0∞).to_real = 0 := rfl
@[simp] lemma of_real_zero : ennreal.of_real (0 : ℝ) = 0 :=
by simp [ennreal.of_real]; refl
@[simp] lemma of_real_one : ennreal.of_real (1 : ℝ) = (1 : ℝ≥0∞) :=
by simp [ennreal.of_real]

lemma of_real_to_real_le {a : ℝ≥0∞} : ennreal.of_real (a.to_real) ≤ a :=
if ha : a = ∞ then ha.symm ▸ le_top else le_of_eq (of_real_to_real ha)

lemma forall_ennreal {p : ℝ≥0∞ → Prop} : (∀a, p a) ↔ (∀r:ℝ≥0, p r) ∧ p ∞ :=
⟨assume h, ⟨assume r, h _, h _⟩,
  assume ⟨h₁, h₂⟩ a, match a with some r := h₁ _ | none := h₂ end⟩

lemma forall_ne_top {p : ℝ≥0∞ → Prop} : (∀ a ≠ ∞, p a) ↔ ∀ r : ℝ≥0, p r :=
option.ball_ne_none

lemma exists_ne_top {p : ℝ≥0∞ → Prop} : (∃ a ≠ ∞, p a) ↔ ∃ r : ℝ≥0, p r :=
option.bex_ne_none

lemma to_nnreal_eq_zero_iff (x : ℝ≥0∞) : x.to_nnreal = 0 ↔ x = 0 ∨ x = ∞ :=
⟨begin
  cases x,
  { simp [none_eq_top] },
  { rintro (rfl : x = 0),
    exact or.inl rfl },
end,
by rintro (h | h); simp [h]⟩

lemma to_real_eq_zero_iff (x : ℝ≥0∞) : x.to_real = 0 ↔ x = 0 ∨ x = ∞ :=
by simp [ennreal.to_real, to_nnreal_eq_zero_iff]

lemma to_nnreal_eq_one_iff (x : ℝ≥0∞) : x.to_nnreal = 1 ↔ x = 1 :=
begin
  refine ⟨λ h, _, congr_arg _⟩,
  cases x,
  { exact false.elim (zero_ne_one $ ennreal.top_to_nnreal.symm.trans h) },
  { exact congr_arg _ h }
end

lemma to_real_eq_one_iff (x : ℝ≥0∞) : x.to_real = 1 ↔ x = 1 :=
by rw [ennreal.to_real, nnreal.coe_eq_one, ennreal.to_nnreal_eq_one_iff]

@[simp] lemma coe_ne_top : (r : ℝ≥0∞) ≠ ∞ := with_top.coe_ne_top
@[simp] lemma top_ne_coe : ∞ ≠ (r : ℝ≥0∞) := with_top.top_ne_coe
@[simp] lemma of_real_ne_top {r : ℝ} : ennreal.of_real r ≠ ∞ := by simp [ennreal.of_real]
@[simp] lemma of_real_lt_top {r : ℝ} : ennreal.of_real r < ∞ := lt_top_iff_ne_top.2 of_real_ne_top
@[simp] lemma top_ne_of_real {r : ℝ} : ∞ ≠ ennreal.of_real r := by simp [ennreal.of_real]

@[simp] lemma zero_ne_top : 0 ≠ ∞ := coe_ne_top
@[simp] lemma top_ne_zero : ∞ ≠ 0 := top_ne_coe

@[simp] lemma one_ne_top : 1 ≠ ∞ := coe_ne_top
@[simp] lemma top_ne_one : ∞ ≠ 1 := top_ne_coe

@[simp, norm_cast] lemma coe_eq_coe : (↑r : ℝ≥0∞) = ↑q ↔ r = q := with_top.coe_eq_coe
@[simp, norm_cast] lemma coe_le_coe : (↑r : ℝ≥0∞) ≤ ↑q ↔ r ≤ q := with_top.coe_le_coe
@[simp, norm_cast] lemma coe_lt_coe : (↑r : ℝ≥0∞) < ↑q ↔ r < q := with_top.coe_lt_coe
lemma coe_mono : monotone (coe : ℝ≥0 → ℝ≥0∞) := λ _ _, coe_le_coe.2

@[simp, norm_cast] lemma coe_eq_zero : (↑r : ℝ≥0∞) = 0 ↔ r = 0 := coe_eq_coe
@[simp, norm_cast] lemma zero_eq_coe : 0 = (↑r : ℝ≥0∞) ↔ 0 = r := coe_eq_coe
@[simp, norm_cast] lemma coe_eq_one : (↑r : ℝ≥0∞) = 1 ↔ r = 1 := coe_eq_coe
@[simp, norm_cast] lemma one_eq_coe : 1 = (↑r : ℝ≥0∞) ↔ 1 = r := coe_eq_coe
@[simp, norm_cast] lemma coe_pos : 0 < (↑r : ℝ≥0∞) ↔ 0 < r := coe_lt_coe
lemma coe_ne_zero : (r : ℝ≥0∞) ≠ 0 ↔ r ≠ 0 := not_congr coe_eq_coe

@[simp, norm_cast] lemma coe_add : ↑(r + p) = (r + p : ℝ≥0∞) := with_top.coe_add
@[simp, norm_cast] lemma coe_mul : ↑(r * p) = (r * p : ℝ≥0∞) := with_top.coe_mul

@[simp, norm_cast] lemma coe_bit0 : (↑(bit0 r) : ℝ≥0∞) = bit0 r := coe_add
@[simp, norm_cast] lemma coe_bit1 : (↑(bit1 r) : ℝ≥0∞) = bit1 r := by simp [bit1]
lemma coe_two : ((2:ℝ≥0) : ℝ≥0∞) = 2 := by norm_cast

lemma to_nnreal_eq_to_nnreal_iff (x y : ℝ≥0∞) :
  x.to_nnreal = y.to_nnreal ↔ x = y ∨ x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0 :=
begin
  cases x,
  { simp only [@eq_comm ℝ≥0 _ y.to_nnreal, @eq_comm ℝ≥0∞ _ y, to_nnreal_eq_zero_iff,
      none_eq_top, top_to_nnreal, top_ne_zero, false_and, eq_self_iff_true,
        true_and, false_or, or_comm (y = ⊤)] },
  { cases y; simp }
end

lemma to_real_eq_to_real_iff (x y : ℝ≥0∞) :
  x.to_real = y.to_real ↔ x = y ∨ (x = 0 ∧ y = ⊤) ∨ (x = ⊤ ∧ y = 0) :=
by simp only [ennreal.to_real, nnreal.coe_eq, to_nnreal_eq_to_nnreal_iff]

lemma to_nnreal_eq_to_nnreal_iff' {x y : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
  x.to_nnreal = y.to_nnreal ↔ x = y :=
by simp only [ennreal.to_nnreal_eq_to_nnreal_iff x y, hx, hy, and_false, false_and, or_false]

lemma to_real_eq_to_real_iff' {x y : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
  x.to_real = y.to_real ↔ x = y :=
by simp only [ennreal.to_real, nnreal.coe_eq, to_nnreal_eq_to_nnreal_iff' hx hy]

@[simp] lemma one_lt_two : (1 : ℝ≥0∞) < 2 :=
coe_one ▸ coe_two ▸ by exact_mod_cast (one_lt_two : 1 < 2)

lemma two_ne_top : (2 : ℝ≥0∞) ≠ ∞ := coe_two ▸ coe_ne_top

/-- `(1 : ℝ≥0∞) ≤ 1`, recorded as a `fact` for use with `Lp` spaces. -/
instance _root_.fact_one_le_one_ennreal : fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩

/-- `(1 : ℝ≥0∞) ≤ 2`, recorded as a `fact` for use with `Lp` spaces. -/
instance _root_.fact_one_le_two_ennreal : fact ((1 : ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩

/-- `(1 : ℝ≥0∞) ≤ ∞`, recorded as a `fact` for use with `Lp` spaces. -/
instance _root_.fact_one_le_top_ennreal : fact ((1 : ℝ≥0∞) ≤ ∞) := ⟨le_top⟩

/-- The set of numbers in `ℝ≥0∞` that are not equal to `∞` is equivalent to `ℝ≥0`. -/
def ne_top_equiv_nnreal : {a | a ≠ ∞} ≃ ℝ≥0 :=
{ to_fun := λ x, ennreal.to_nnreal x,
  inv_fun := λ x, ⟨x, coe_ne_top⟩,
  left_inv := λ ⟨x, hx⟩, subtype.eq $ coe_to_nnreal hx,
  right_inv := λ x, to_nnreal_coe }

lemma cinfi_ne_top [has_Inf α] (f : ℝ≥0∞ → α) : (⨅ x : {x // x ≠ ∞}, f x) = ⨅ x : ℝ≥0, f x :=
eq.symm $ ne_top_equiv_nnreal.symm.surjective.infi_congr _$ λ x, rfl

lemma infi_ne_top [complete_lattice α] (f : ℝ≥0∞ → α) : (⨅ x ≠ ∞, f x) = ⨅ x : ℝ≥0, f x :=
by rw [infi_subtype', cinfi_ne_top]

lemma csupr_ne_top [has_Sup α] (f : ℝ≥0∞ → α) : (⨆ x : {x // x ≠ ∞}, f x) = ⨆ x : ℝ≥0, f x :=
@cinfi_ne_top αᵒᵈ _ _

lemma supr_ne_top [complete_lattice α] (f : ℝ≥0∞ → α) : (⨆ x ≠ ∞, f x) = ⨆ x : ℝ≥0, f x :=
@infi_ne_top αᵒᵈ _ _

lemma infi_ennreal {α : Type*} [complete_lattice α] {f : ℝ≥0∞ → α} :
  (⨅ n, f n) = (⨅ n : ℝ≥0, f n) ⊓ f ∞ :=
le_antisymm
  (le_inf (le_infi $ assume i, infi_le _ _) (infi_le _ _))
  (le_infi $ forall_ennreal.2 ⟨λ r, inf_le_of_left_le $ infi_le _ _, inf_le_right⟩)

lemma supr_ennreal {α : Type*} [complete_lattice α] {f : ℝ≥0∞ → α} :
  (⨆ n, f n) = (⨆ n : ℝ≥0, f n) ⊔ f ∞ :=
@infi_ennreal αᵒᵈ _ _

/-- Coercion `ℝ≥0 → ℝ≥0∞` as a `ring_hom`. -/
def of_nnreal_hom : ℝ≥0 →+* ℝ≥0∞ :=
⟨coe, coe_one, λ _ _, coe_mul, coe_zero, λ _ _, coe_add⟩

@[simp] lemma coe_of_nnreal_hom : ⇑of_nnreal_hom = coe := rfl

section actions

/-- A `mul_action` over `ℝ≥0∞` restricts to a `mul_action` over `ℝ≥0`. -/
noncomputable instance {M : Type*} [mul_action ℝ≥0∞ M] : mul_action ℝ≥0 M :=
mul_action.comp_hom M of_nnreal_hom.to_monoid_hom

lemma smul_def {M : Type*} [mul_action ℝ≥0∞ M] (c : ℝ≥0) (x : M) :
  c • x = (c : ℝ≥0∞) • x := rfl

instance {M N : Type*} [mul_action ℝ≥0∞ M] [mul_action ℝ≥0∞ N] [has_smul M N]
  [is_scalar_tower ℝ≥0∞ M N] : is_scalar_tower ℝ≥0 M N :=
{ smul_assoc := λ r, (smul_assoc (r : ℝ≥0∞) : _)}

instance smul_comm_class_left {M N : Type*} [mul_action ℝ≥0∞ N] [has_smul M N]
  [smul_comm_class ℝ≥0∞ M N] : smul_comm_class ℝ≥0 M N :=
{ smul_comm := λ r, (smul_comm (r : ℝ≥0∞) : _)}

instance smul_comm_class_right {M N : Type*} [mul_action ℝ≥0∞ N] [has_smul M N]
  [smul_comm_class M ℝ≥0∞ N] : smul_comm_class M ℝ≥0 N :=
{ smul_comm := λ m r, (smul_comm m (r : ℝ≥0∞) : _)}

/-- A `distrib_mul_action` over `ℝ≥0∞` restricts to a `distrib_mul_action` over `ℝ≥0`. -/
noncomputable instance {M : Type*} [add_monoid M] [distrib_mul_action ℝ≥0∞ M] :
  distrib_mul_action ℝ≥0 M :=
distrib_mul_action.comp_hom M of_nnreal_hom.to_monoid_hom

/-- A `module` over `ℝ≥0∞` restricts to a `module` over `ℝ≥0`. -/
noncomputable instance {M : Type*} [add_comm_monoid M] [module ℝ≥0∞ M] : module ℝ≥0 M :=
module.comp_hom M of_nnreal_hom

/-- An `algebra` over `ℝ≥0∞` restricts to an `algebra` over `ℝ≥0`. -/
noncomputable instance {A : Type*} [semiring A] [algebra ℝ≥0∞ A] : algebra ℝ≥0 A :=
{ smul := (•),
  commutes' := λ r x, by simp [algebra.commutes],
  smul_def' := λ r x, by simp [←algebra.smul_def (r : ℝ≥0∞) x, smul_def],
  to_ring_hom := ((algebra_map ℝ≥0∞ A).comp (of_nnreal_hom : ℝ≥0 →+* ℝ≥0∞)) }

-- verify that the above produces instances we might care about
noncomputable example : algebra ℝ≥0 ℝ≥0∞ := infer_instance
noncomputable example : distrib_mul_action ℝ≥0ˣ ℝ≥0∞ := infer_instance

lemma coe_smul {R} (r : R) (s : ℝ≥0) [has_smul R ℝ≥0] [has_smul R ℝ≥0∞]
  [is_scalar_tower R ℝ≥0 ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ≥0∞] :
  (↑(r • s) : ℝ≥0∞) = r • ↑s :=
by rw [←smul_one_smul ℝ≥0 r (s: ℝ≥0∞), smul_def, smul_eq_mul, ←ennreal.coe_mul, smul_mul_assoc,
    one_mul]

end actions

@[simp, norm_cast] lemma coe_indicator {α} (s : set α) (f : α → ℝ≥0) (a : α) :
  ((s.indicator f a : ℝ≥0) : ℝ≥0∞) = s.indicator (λ x, f x) a :=
(of_nnreal_hom : ℝ≥0 →+ ℝ≥0∞).map_indicator _ _ _

@[simp, norm_cast] lemma coe_pow (n : ℕ) : (↑(r^n) : ℝ≥0∞) = r^n :=
of_nnreal_hom.map_pow r n

@[simp] lemma add_eq_top : a + b = ∞ ↔ a = ∞ ∨ b = ∞ := with_top.add_eq_top
@[simp] lemma add_lt_top : a + b < ∞ ↔ a < ∞ ∧ b < ∞ := with_top.add_lt_top

lemma to_nnreal_add {r₁ r₂ : ℝ≥0∞} (h₁ : r₁ ≠ ∞) (h₂ : r₂ ≠ ∞) :
  (r₁ + r₂).to_nnreal = r₁.to_nnreal + r₂.to_nnreal :=
by { lift r₁ to ℝ≥0 using h₁, lift r₂ to ℝ≥0 using h₂, refl }

lemma not_lt_top {x : ℝ≥0∞} : ¬ x < ∞ ↔ x = ∞ := by rw [lt_top_iff_ne_top, not_not]

lemma add_ne_top : a + b ≠ ∞ ↔ a ≠ ∞ ∧ b ≠ ∞ :=
by simpa only [lt_top_iff_ne_top] using add_lt_top

lemma mul_top : a * ∞ = (if a = 0 then 0 else ∞) :=
begin split_ifs, { simp [h] }, { exact with_top.mul_top h } end

lemma top_mul : ∞ * a = (if a = 0 then 0 else ∞) :=
begin split_ifs, { simp [h] }, { exact with_top.top_mul h } end

@[simp] lemma top_mul_top : ∞ * ∞ = ∞ := with_top.top_mul_top

lemma top_pow {n:ℕ} (h : 0 < n) : ∞^n = ∞ :=
nat.le_induction (pow_one _) (λ m hm hm', by rw [pow_succ, hm', top_mul_top])
  _ (nat.succ_le_of_lt h)

lemma mul_eq_top : a * b = ∞ ↔ (a ≠ 0 ∧ b = ∞) ∨ (a = ∞ ∧ b ≠ 0) :=
with_top.mul_eq_top_iff

lemma mul_lt_top  : a ≠ ∞ → b ≠ ∞ → a * b < ∞ :=
with_top.mul_lt_top

lemma mul_ne_top : a ≠ ∞ → b ≠ ∞ → a * b ≠ ∞ :=
by simpa only [lt_top_iff_ne_top] using mul_lt_top

lemma lt_top_of_mul_ne_top_left (h : a * b ≠ ∞) (hb : b ≠ 0) : a < ∞ :=
lt_top_iff_ne_top.2 $ λ ha, h $ mul_eq_top.2 (or.inr ⟨ha, hb⟩)

lemma lt_top_of_mul_ne_top_right (h : a * b ≠ ∞) (ha : a ≠ 0) : b < ∞ :=
lt_top_of_mul_ne_top_left (by rwa [mul_comm]) ha

lemma mul_lt_top_iff {a b : ℝ≥0∞} : a * b < ∞ ↔ (a < ∞ ∧ b < ∞) ∨ a = 0 ∨ b = 0 :=
begin
  split,
  { intro h, rw [← or_assoc, or_iff_not_imp_right, or_iff_not_imp_right], intros hb ha,
    exact ⟨lt_top_of_mul_ne_top_left h.ne hb, lt_top_of_mul_ne_top_right h.ne ha⟩ },
  { rintro (⟨ha, hb⟩|rfl|rfl); [exact mul_lt_top ha.ne hb.ne, simp, simp] }
end

lemma mul_self_lt_top_iff {a : ℝ≥0∞} : a * a < ⊤ ↔ a < ⊤ :=
by { rw [ennreal.mul_lt_top_iff, and_self, or_self, or_iff_left_iff_imp], rintro rfl, norm_num }

lemma mul_pos_iff : 0 < a * b ↔ 0 < a ∧ 0 < b := canonically_ordered_comm_semiring.mul_pos

lemma mul_pos (ha : a ≠ 0) (hb : b ≠ 0) : 0 < a * b :=
mul_pos_iff.2 ⟨pos_iff_ne_zero.2 ha, pos_iff_ne_zero.2 hb⟩

@[simp] lemma pow_eq_top_iff {n : ℕ} : a ^ n = ∞ ↔ a = ∞ ∧ n ≠ 0 :=
begin
  induction n with n ihn, { simp },
  rw [pow_succ, mul_eq_top, ihn],
  fsplit,
  { rintro (⟨-,rfl,h0⟩|⟨rfl,h0⟩); exact ⟨rfl, n.succ_ne_zero⟩ },
  { rintro ⟨rfl, -⟩, exact or.inr ⟨rfl, pow_ne_zero n top_ne_zero⟩ }
end

lemma pow_eq_top (n : ℕ) (h : a ^ n = ∞) : a = ∞ :=
(pow_eq_top_iff.1 h).1

lemma pow_ne_top (h : a ≠ ∞) {n:ℕ} : a^n ≠ ∞ :=
mt (pow_eq_top n) h

lemma pow_lt_top : a < ∞ → ∀ n:ℕ, a^n < ∞ :=
by simpa only [lt_top_iff_ne_top] using pow_ne_top

@[simp, norm_cast] lemma coe_finset_sum {s : finset α} {f : α → ℝ≥0} :
  ↑(∑ a in s, f a) = (∑ a in s, f a : ℝ≥0∞) :=
of_nnreal_hom.map_sum f s

@[simp, norm_cast] lemma coe_finset_prod {s : finset α} {f : α → ℝ≥0} :
  ↑(∏ a in s, f a) = ((∏ a in s, f a) : ℝ≥0∞) :=
of_nnreal_hom.map_prod f s

section order

@[simp] lemma bot_eq_zero : (⊥ : ℝ≥0∞) = 0 := rfl

@[simp] lemma coe_lt_top : coe r < ∞ := with_top.coe_lt_top r
@[simp] lemma not_top_le_coe : ¬ ∞ ≤ ↑r := with_top.not_top_le_coe r
@[simp, norm_cast] lemma one_le_coe_iff : (1:ℝ≥0∞) ≤ ↑r ↔ 1 ≤ r := coe_le_coe
@[simp, norm_cast] lemma coe_le_one_iff : ↑r ≤ (1:ℝ≥0∞) ↔ r ≤ 1 := coe_le_coe
@[simp, norm_cast] lemma coe_lt_one_iff : (↑p : ℝ≥0∞) < 1 ↔ p < 1 := coe_lt_coe
@[simp, norm_cast] lemma one_lt_coe_iff : 1 < (↑p : ℝ≥0∞) ↔ 1 < p := coe_lt_coe
@[simp, norm_cast] lemma coe_nat (n : ℕ) : ((n : ℝ≥0) : ℝ≥0∞) = n := with_top.coe_nat n
@[simp] lemma of_real_coe_nat (n : ℕ) : ennreal.of_real n = n := by simp [ennreal.of_real]
@[simp] lemma nat_ne_top (n : ℕ) : (n : ℝ≥0∞) ≠ ∞ := with_top.nat_ne_top n
@[simp] lemma top_ne_nat (n : ℕ) : ∞ ≠ n := with_top.top_ne_nat n
@[simp] lemma one_lt_top : 1 < ∞ := coe_lt_top

@[simp, norm_cast] lemma to_nnreal_nat (n : ℕ) : (n : ℝ≥0∞).to_nnreal = n :=
by conv_lhs { rw [← ennreal.coe_nat n, ennreal.to_nnreal_coe] }

@[simp, norm_cast] lemma to_real_nat (n : ℕ) : (n : ℝ≥0∞).to_real = n :=
by conv_lhs { rw [← ennreal.of_real_coe_nat n, ennreal.to_real_of_real (nat.cast_nonneg _)] }

lemma le_coe_iff : a ≤ ↑r ↔ (∃p:ℝ≥0, a = p ∧ p ≤ r) := with_top.le_coe_iff
lemma coe_le_iff : ↑r ≤ a ↔ (∀p:ℝ≥0, a = p → r ≤ p) := with_top.coe_le_iff

lemma lt_iff_exists_coe : a < b ↔ (∃p:ℝ≥0, a = p ∧ ↑p < b) := with_top.lt_iff_exists_coe

lemma to_real_le_coe_of_le_coe {a : ℝ≥0∞} {b : ℝ≥0} (h : a ≤ b) : a.to_real ≤ b :=
show ↑a.to_nnreal ≤ ↑b,
begin
  have : ↑a.to_nnreal = a := ennreal.coe_to_nnreal (lt_of_le_of_lt h coe_lt_top).ne,
  rw ← this at h,
  exact_mod_cast h
end

@[simp, norm_cast] lemma coe_finset_sup {s : finset α} {f : α → ℝ≥0} :
  ↑(s.sup f) = s.sup (λ x, (f x : ℝ≥0∞)) :=
finset.comp_sup_eq_sup_comp_of_is_total _ coe_mono rfl

@[simp] lemma max_eq_zero_iff : max a b = 0 ↔ a = 0 ∧ b = 0 :=
by simp only [nonpos_iff_eq_zero.symm, max_le_iff]

@[simp] lemma max_zero_left : max 0 a = a := max_eq_right (zero_le a)
@[simp] lemma max_zero_right : max a 0 = a := max_eq_left (zero_le a)

@[simp] lemma sup_eq_max : a ⊔ b = max a b :=
rfl

protected lemma pow_pos : 0 < a → ∀ n : ℕ, 0 < a^n :=
canonically_ordered_comm_semiring.pow_pos

protected lemma pow_ne_zero : a ≠ 0 → ∀ n : ℕ, a^n ≠ 0 :=
by simpa only [pos_iff_ne_zero] using ennreal.pow_pos

@[simp] lemma not_lt_zero : ¬ a < 0 := by simp

protected lemma le_of_add_le_add_left : a ≠ ∞ → a + b ≤ a + c → b ≤ c :=
with_top.le_of_add_le_add_left
protected lemma le_of_add_le_add_right : a ≠ ∞ → b + a ≤ c + a → b ≤ c :=
with_top.le_of_add_le_add_right
protected lemma add_lt_add_left : a ≠ ∞ → b < c → a + b < a + c := with_top.add_lt_add_left
protected lemma add_lt_add_right : a ≠ ∞ → b < c → b + a < c + a := with_top.add_lt_add_right
protected lemma add_le_add_iff_left : a ≠ ∞ → (a + b ≤ a + c ↔ b ≤ c) :=
with_top.add_le_add_iff_left
protected lemma add_le_add_iff_right : a ≠ ∞ → (b + a ≤ c + a ↔ b ≤ c) :=
with_top.add_le_add_iff_right
protected lemma add_lt_add_iff_left : a ≠ ∞ → (a + b < a + c ↔ b < c) :=
with_top.add_lt_add_iff_left
protected lemma add_lt_add_iff_right : a ≠ ∞ → (b + a < c + a ↔ b < c) :=
with_top.add_lt_add_iff_right
protected lemma add_lt_add_of_le_of_lt : a ≠ ∞ → a ≤ b → c < d → a + c < b + d :=
with_top.add_lt_add_of_le_of_lt
protected lemma add_lt_add_of_lt_of_le : c ≠ ∞ → a < b → c ≤ d → a + c < b + d :=
with_top.add_lt_add_of_lt_of_le

instance contravariant_class_add_lt : contravariant_class ℝ≥0∞ ℝ≥0∞ (+) (<) :=
with_top.contravariant_class_add_lt

lemma lt_add_right (ha : a ≠ ∞) (hb : b ≠ 0) : a < a + b :=
by rwa [← pos_iff_ne_zero, ←ennreal.add_lt_add_iff_left ha, add_zero] at hb

lemma le_of_forall_pos_le_add : ∀{a b : ℝ≥0∞}, (∀ε : ℝ≥0, 0 < ε → b < ∞ → a ≤ b + ε) → a ≤ b
| a    none     h := le_top
| none (some a) h :=
  have ∞ ≤ ↑a + ↑(1:ℝ≥0), from h 1 zero_lt_one coe_lt_top,
  by rw [← coe_add] at this; exact (not_top_le_coe this).elim
| (some a) (some b) h :=
    by simp only [none_eq_top, some_eq_coe, coe_add.symm, coe_le_coe, coe_lt_top, true_implies_iff]
      at *; exact nnreal.le_of_forall_pos_le_add h

lemma lt_iff_exists_rat_btwn :
  a < b ↔ (∃q:ℚ, 0 ≤ q ∧ a < real.to_nnreal q ∧ (real.to_nnreal q:ℝ≥0∞) < b) :=
⟨λ h,
  begin
    rcases lt_iff_exists_coe.1 h with ⟨p, rfl, _⟩,
    rcases exists_between h with ⟨c, pc, cb⟩,
    rcases lt_iff_exists_coe.1 cb with ⟨r, rfl, _⟩,
    rcases (nnreal.lt_iff_exists_rat_btwn _ _).1 (coe_lt_coe.1 pc) with ⟨q, hq0, pq, qr⟩,
    exact ⟨q, hq0, coe_lt_coe.2 pq, lt_trans (coe_lt_coe.2 qr) cb⟩
  end,
λ ⟨q, q0, qa, qb⟩, lt_trans qa qb⟩

lemma lt_iff_exists_real_btwn :
  a < b ↔ (∃r:ℝ, 0 ≤ r ∧ a < ennreal.of_real r ∧ (ennreal.of_real r:ℝ≥0∞) < b) :=
⟨λ h, let ⟨q, q0, aq, qb⟩ := ennreal.lt_iff_exists_rat_btwn.1 h in
  ⟨q, rat.cast_nonneg.2 q0, aq, qb⟩,
λ ⟨q, q0, qa, qb⟩, lt_trans qa qb⟩

lemma lt_iff_exists_nnreal_btwn :
  a < b ↔ (∃r:ℝ≥0, a < r ∧ (r : ℝ≥0∞) < b) :=
with_top.lt_iff_exists_coe_btwn

lemma lt_iff_exists_add_pos_lt : a < b ↔ (∃ r : ℝ≥0, 0 < r ∧ a + r < b) :=
begin
  refine ⟨λ hab, _, λ ⟨r, rpos, hr⟩, lt_of_le_of_lt (le_self_add) hr⟩,
  cases a, { simpa using hab },
  rcases lt_iff_exists_real_btwn.1 hab with ⟨c, c_nonneg, ac, cb⟩,
  let d : ℝ≥0 := ⟨c, c_nonneg⟩,
  have ad : a < d,
  { rw of_real_eq_coe_nnreal c_nonneg at ac,
    exact coe_lt_coe.1 ac },
  refine ⟨d-a, tsub_pos_iff_lt.2 ad, _⟩,
  rw [some_eq_coe, ← coe_add],
  convert cb,
  have : real.to_nnreal c = d,
    by { rw [← nnreal.coe_eq, real.coe_to_nnreal _ c_nonneg], refl },
  rw [add_comm, this],
  exact tsub_add_cancel_of_le ad.le
end

@[simp, norm_cast] lemma coe_nat_lt_coe {n : ℕ} : (n : ℝ≥0∞) < r ↔ ↑n < r :=
ennreal.coe_nat n ▸ coe_lt_coe

@[simp, norm_cast] lemma coe_lt_coe_nat {n : ℕ} : (r : ℝ≥0∞) < n ↔ r < n :=
ennreal.coe_nat n ▸ coe_lt_coe

protected lemma exists_nat_gt {r : ℝ≥0∞} (h : r ≠ ∞) : ∃n:ℕ, r < n :=
begin
  lift r to ℝ≥0 using h,
  rcases exists_nat_gt r with ⟨n, hn⟩,
  exact ⟨n, coe_lt_coe_nat.2 hn⟩,
end

@[simp] lemma Union_Iio_coe_nat : (⋃ n : ℕ, Iio (n : ℝ≥0∞)) = {∞}ᶜ :=
begin
  ext x,
  rw [mem_Union],
  exact ⟨λ ⟨n, hn⟩, ne_top_of_lt hn, ennreal.exists_nat_gt⟩
end

@[simp] lemma Union_Iic_coe_nat : (⋃ n : ℕ, Iic (n : ℝ≥0∞)) = {∞}ᶜ :=
subset.antisymm (Union_subset $ λ n x hx, ne_top_of_le_ne_top (nat_ne_top n) hx) $
  Union_Iio_coe_nat ▸ Union_mono (λ n, Iio_subset_Iic_self)

@[simp] lemma Union_Ioc_coe_nat : (⋃ n : ℕ, Ioc a n) = Ioi a \ {∞} :=
by simp only [← Ioi_inter_Iic, ← inter_Union, Union_Iic_coe_nat, diff_eq]

@[simp] lemma Union_Ioo_coe_nat : (⋃ n : ℕ, Ioo a n) = Ioi a \ {∞} :=
by simp only [← Ioi_inter_Iio, ← inter_Union, Union_Iio_coe_nat, diff_eq]

@[simp] lemma Union_Icc_coe_nat : (⋃ n : ℕ, Icc a n) = Ici a \ {∞} :=
by simp only [← Ici_inter_Iic, ← inter_Union, Union_Iic_coe_nat, diff_eq]

@[simp] lemma Union_Ico_coe_nat : (⋃ n : ℕ, Ico a n) = Ici a \ {∞} :=
by simp only [← Ici_inter_Iio, ← inter_Union, Union_Iio_coe_nat, diff_eq]

@[simp] lemma Inter_Ici_coe_nat : (⋂ n : ℕ, Ici (n : ℝ≥0∞)) = {∞} :=
by simp only [← compl_Iio, ← compl_Union, Union_Iio_coe_nat, compl_compl]

@[simp] lemma Inter_Ioi_coe_nat : (⋂ n : ℕ, Ioi (n : ℝ≥0∞)) = {∞} :=
by simp only [← compl_Iic, ← compl_Union, Union_Iic_coe_nat, compl_compl]

lemma add_lt_add (ac : a < c) (bd : b < d) : a + b < c + d :=
begin
  lift a to ℝ≥0 using ne_top_of_lt ac,
  lift b to ℝ≥0 using ne_top_of_lt bd,
  cases c, { simp }, cases d, { simp },
  simp only [← coe_add, some_eq_coe, coe_lt_coe] at *,
  exact add_lt_add ac bd
end

@[norm_cast] lemma coe_min : ((min r p:ℝ≥0):ℝ≥0∞) = min r p :=
coe_mono.map_min

@[norm_cast] lemma coe_max : ((max r p:ℝ≥0):ℝ≥0∞) = max r p :=
coe_mono.map_max

lemma le_of_top_imp_top_of_to_nnreal_le {a b : ℝ≥0∞} (h : a = ⊤ → b = ⊤)
  (h_nnreal : a ≠ ⊤ → b ≠ ⊤ → a.to_nnreal ≤ b.to_nnreal) :
  a ≤ b :=
begin
  by_cases ha : a = ⊤,
  { rw h ha,
    exact le_top, },
  by_cases hb : b = ⊤,
  { rw hb,
    exact le_top, },
  rw [←coe_to_nnreal hb, ←coe_to_nnreal ha, coe_le_coe],
  exact h_nnreal ha hb,
end

end order

section complete_lattice

lemma coe_Sup {s : set ℝ≥0} : bdd_above s → (↑(Sup s) : ℝ≥0∞) = (⨆a∈s, ↑a) := with_top.coe_Sup
lemma coe_Inf {s : set ℝ≥0} : s.nonempty → (↑(Inf s) : ℝ≥0∞) = (⨅a∈s, ↑a) := with_top.coe_Inf

lemma coe_mem_upper_bounds {s : set ℝ≥0} :
  ↑r ∈ upper_bounds ((coe : ℝ≥0 → ℝ≥0∞) '' s) ↔ r ∈ upper_bounds s :=
by simp [upper_bounds, ball_image_iff, -mem_image, *] {contextual := tt}

end complete_lattice

section mul

@[mono] lemma mul_lt_mul (ac : a < c) (bd : b < d) : a * b < c * d :=
begin
  rcases lt_iff_exists_nnreal_btwn.1 ac with ⟨a', aa', a'c⟩,
  lift a to ℝ≥0 using ne_top_of_lt aa',
  rcases lt_iff_exists_nnreal_btwn.1 bd with ⟨b', bb', b'd⟩,
  lift b to ℝ≥0 using ne_top_of_lt bb',
  norm_cast at *,
  calc ↑(a * b) < ↑(a' * b') :
    coe_lt_coe.2 (mul_lt_mul' aa'.le bb' (zero_le _) ((zero_le a).trans_lt aa'))
  ... = ↑a' * ↑b' : coe_mul
  ... ≤ c * d : mul_le_mul' a'c.le b'd.le
end

-- TODO: generalize to `covariant_class α α (*) (≤)`
lemma mul_left_mono : monotone ((*) a) := λ b c, mul_le_mul' le_rfl

-- TODO: generalize to `covariant_class α α (swap (*)) (≤)`
lemma mul_right_mono : monotone (λ x, x * a) := λ b c h, mul_le_mul' h le_rfl

lemma pow_strict_mono {n : ℕ} (hn : n ≠ 0) : strict_mono (λ (x : ℝ≥0∞), x^n) :=
begin
  assume x y hxy,
  obtain ⟨n, rfl⟩ := nat.exists_eq_succ_of_ne_zero hn,
  induction n with n IH,
  { simp only [hxy, pow_one] },
  { simp only [pow_succ _ n.succ, mul_lt_mul hxy (IH (nat.succ_pos _).ne')] }
end

lemma max_mul : max a b * c = max (a * c) (b * c) :=
mul_right_mono.map_max

lemma mul_max : a * max b c = max (a * b) (a * c) :=
mul_left_mono.map_max

theorem mul_left_strictMono (h0 : a ≠ 0) (hinf : a ≠ ∞) : strict_mono ((*) a) :=
begin
  lift a to ℝ≥0 using hinf,
  rw [coe_ne_zero] at h0,
  intros x y h,
  contrapose! h,
  simpa only [← mul_assoc, ← coe_mul, inv_mul_cancel h0, coe_one, one_mul]
    using mul_le_mul_left' h (↑a⁻¹)
end

lemma mul_eq_mul_left (h₀ : a ≠ 0) (hinf : a ≠ ∞) : a * b = a * c ↔ b = c :=
(mul_left_strictMono h₀ hinf).injective.eq_iff

lemma mul_eq_mul_right : c ≠ 0 → c ≠ ∞ → (a * c = b * c ↔ a = b) :=
mul_comm c a ▸ mul_comm c b ▸ mul_eq_mul_left

lemma mul_le_mul_left (h₀ : a ≠ 0) (hinf : a ≠ ∞) : a * b ≤ a * c ↔ b ≤ c :=
(mul_left_strictMono h₀ hinf).le_iff_le

lemma mul_le_mul_right : c ≠ 0 → c ≠ ∞ → (a * c ≤ b * c ↔ a ≤ b) :=
mul_comm c a ▸ mul_comm c b ▸ mul_le_mul_left

lemma mul_lt_mul_left (h₀ : a ≠ 0) (hinf : a ≠ ∞) : a * b < a * c ↔ b < c :=
(mul_left_strictMono h₀ hinf).lt_iff_lt

lemma mul_lt_mul_right : c ≠ 0 → c ≠ ∞ → (a * c < b * c ↔ a < b) :=
mul_comm c a ▸ mul_comm c b ▸ mul_lt_mul_left

end mul

section cancel

/-- An element `a` is `add_le_cancellable` if `a + b ≤ a + c` implies `b ≤ c` for all `b` and `c`.
  This is true in `ℝ≥0∞` for all elements except `∞`. -/
lemma add_le_cancellable_iff_ne {a : ℝ≥0∞} : add_le_cancellable a ↔ a ≠ ∞ :=
begin
  split,
  { rintro h rfl, refine zero_lt_one.not_le (h _), simp, },
  { rintro h b c hbc, apply ennreal.le_of_add_le_add_left h hbc }
end

/-- This lemma has an abbreviated name because it is used frequently. -/
lemma cancel_of_ne {a : ℝ≥0∞} (h : a ≠ ∞) : add_le_cancellable a :=
add_le_cancellable_iff_ne.mpr h

/-- This lemma has an abbreviated name because it is used frequently. -/
lemma cancel_of_lt {a : ℝ≥0∞} (h : a < ∞) : add_le_cancellable a :=
cancel_of_ne h.ne

/-- This lemma has an abbreviated name because it is used frequently. -/
lemma cancel_of_lt' {a b : ℝ≥0∞} (h : a < b) : add_le_cancellable a :=
cancel_of_ne h.ne_top

/-- This lemma has an abbreviated name because it is used frequently. -/
lemma cancel_coe {a : ℝ≥0} : add_le_cancellable (a : ℝ≥0∞) :=
cancel_of_ne coe_ne_top

lemma add_right_inj (h : a ≠ ∞) : a + b = a + c ↔ b = c :=
(cancel_of_ne h).inj

lemma add_left_inj (h : a ≠ ∞) : b + a = c + a ↔ b = c :=
(cancel_of_ne h).inj_left

end cancel

section sub

lemma sub_eq_Inf {a b : ℝ≥0∞} : a - b = Inf {d | a ≤ d + b} :=
le_antisymm (le_Inf $ λ c, tsub_le_iff_right.mpr) $ Inf_le le_tsub_add

/-- This is a special case of `with_top.coe_sub` in the `ennreal` namespace -/
lemma coe_sub : (↑(r - p) : ℝ≥0∞) = ↑r - ↑p :=
with_top.coe_sub

/-- This is a special case of `with_top.top_sub_coe` in the `ennreal` namespace -/
lemma top_sub_coe : ∞ - ↑r = ∞ :=
with_top.top_sub_coe

/-- This is a special case of `with_top.sub_top` in the `ennreal` namespace -/
lemma sub_top : a - ∞ = 0 :=
with_top.sub_top

lemma sub_eq_top_iff : a - b = ∞ ↔ a = ∞ ∧ b ≠ ∞ :=
by { cases a; cases b; simp [← with_top.coe_sub] }

lemma sub_ne_top (ha : a ≠ ∞) : a - b ≠ ∞ :=
mt sub_eq_top_iff.mp $ mt and.left ha

@[simp, norm_cast] lemma nat_cast_sub (m n : ℕ) : ↑(m - n) = (m - n : ℝ≥0∞) :=
by rw [← coe_nat, nat.cast_tsub, coe_sub, coe_nat, coe_nat]

protected lemma sub_eq_of_eq_add (hb : b ≠ ∞) : a = c + b → a - b = c :=
(cancel_of_ne hb).tsub_eq_of_eq_add

protected lemma eq_sub_of_add_eq (hc : c ≠ ∞) : a + c = b → a = b - c :=
(cancel_of_ne hc).eq_tsub_of_add_eq

protected lemma sub_eq_of_eq_add_rev (hb : b ≠ ∞) : a = b + c → a - b = c :=
(cancel_of_ne hb).tsub_eq_of_eq_add_rev

lemma sub_eq_of_add_eq (hb : b ≠ ∞) (hc : a + b = c) : c - b = a :=
ennreal.sub_eq_of_eq_add hb hc.symm

@[simp] protected lemma add_sub_cancel_left (ha : a ≠ ∞) : a + b - a = b :=
(cancel_of_ne ha).add_tsub_cancel_left

@[simp] protected lemma add_sub_cancel_right (hb : b ≠ ∞) : a + b - b = a :=
(cancel_of_ne hb).add_tsub_cancel_right

protected lemma lt_add_of_sub_lt_left (h : a ≠ ∞ ∨ b ≠ ∞) : a - b < c → a < b + c :=
begin
  obtain rfl | hb := eq_or_ne b ∞,
  { rw [top_add, lt_top_iff_ne_top],
    exact λ _, h.resolve_right (not_not.2 rfl) },
  { exact (cancel_of_ne hb).lt_add_of_tsub_lt_left }
end

protected lemma lt_add_of_sub_lt_right (h : a ≠ ∞ ∨ c ≠ ∞) : a - c < b → a < b + c :=
add_comm c b ▸ ennreal.lt_add_of_sub_lt_left h

lemma le_sub_of_add_le_left (ha : a ≠ ∞) : a + b ≤ c → b ≤ c - a :=
(cancel_of_ne ha).le_tsub_of_add_le_left

lemma le_sub_of_add_le_right (hb : b ≠ ∞) : a + b ≤ c → a ≤ c - b :=
(cancel_of_ne hb).le_tsub_of_add_le_right

protected lemma sub_lt_of_lt_add (hac : c ≤ a) (h : a < b + c) : a - c < b :=
((cancel_of_lt' $ hac.trans_lt h).tsub_lt_iff_right hac).mpr h

protected lemma sub_lt_iff_lt_right (hb : b ≠ ∞) (hab : b ≤ a) : a - b < c ↔ a < c + b :=
(cancel_of_ne hb).tsub_lt_iff_right hab

protected lemma sub_lt_self (ha : a ≠ ∞) (ha₀ : a ≠ 0) (hb : b ≠ 0) : a - b < a :=
(cancel_of_ne ha).tsub_lt_self (pos_iff_ne_zero.2 ha₀) (pos_iff_ne_zero.2 hb)

protected lemma sub_lt_self_iff (ha : a ≠ ∞) : a - b < a ↔ 0 < a ∧ 0 < b :=
(cancel_of_ne ha).tsub_lt_self_iff

lemma sub_lt_of_sub_lt (h₂ : c ≤ a) (h₃ : a ≠ ∞ ∨ b ≠ ∞) (h₁ : a - b < c) : a - c < b :=
ennreal.sub_lt_of_lt_add h₂ (add_comm c b ▸ ennreal.lt_add_of_sub_lt_right h₃ h₁)

lemma sub_sub_cancel (h : a ≠ ∞) (h2 : b ≤ a) : a - (a - b) = b :=
(cancel_of_ne $ sub_ne_top h).tsub_tsub_cancel_of_le h2

lemma sub_right_inj {a b c : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≤ a) (hc : c ≤ a) :
  a - b = a - c ↔ b = c :=
(cancel_of_ne ha).tsub_right_inj (cancel_of_ne $ ne_top_of_le_ne_top ha hb)
  (cancel_of_ne $ ne_top_of_le_ne_top ha hc) hb hc

lemma sub_mul (h : 0 < b → b < a → c ≠ ∞) : (a - b) * c = a * c - b * c :=
begin
  cases le_or_lt a b with hab hab, { simp [hab, mul_right_mono hab] },
  rcases eq_or_lt_of_le (zero_le b) with rfl|hb, { simp },
  exact (cancel_of_ne $ mul_ne_top hab.ne_top (h hb hab)).tsub_mul
end

lemma mul_sub (h : 0 < c → c < b → a ≠ ∞) : a * (b - c) = a * b - a * c :=
by { simp only [mul_comm a], exact sub_mul h }

end sub

section sum

open finset

/-- A product of finite numbers is still finite -/
lemma prod_lt_top {s : finset α} {f : α → ℝ≥0∞} (h : ∀ a ∈ s, f a ≠ ∞) : (∏ a in s, f a) < ∞ :=
with_top.prod_lt_top h

/-- A sum of finite numbers is still finite -/
lemma sum_lt_top {s : finset α} {f : α → ℝ≥0∞} (h : ∀ a ∈ s, f a ≠ ∞) : ∑ a in s, f a < ∞ :=
with_top.sum_lt_top h

/-- A sum of finite numbers is still finite -/
lemma sum_lt_top_iff {s : finset α} {f : α → ℝ≥0∞} :
  ∑ a in s, f a < ∞ ↔ (∀ a ∈ s, f a < ∞) :=
with_top.sum_lt_top_iff

/-- A sum of numbers is infinite iff one of them is infinite -/
lemma sum_eq_top_iff {s : finset α} {f : α → ℝ≥0∞} :
  (∑ x in s, f x) = ∞ ↔ (∃ a ∈ s, f a = ∞) :=
with_top.sum_eq_top_iff

lemma lt_top_of_sum_ne_top {s : finset α} {f : α → ℝ≥0∞} (h : (∑ x in s, f x) ≠ ∞) {a : α}
  (ha : a ∈ s) : f a < ∞ :=
sum_lt_top_iff.1 h.lt_top a ha

/-- seeing `ℝ≥0∞` as `ℝ≥0` does not change their sum, unless one of the `ℝ≥0∞` is
infinity -/
lemma to_nnreal_sum {s : finset α} {f : α → ℝ≥0∞} (hf : ∀a∈s, f a ≠ ∞) :
  ennreal.to_nnreal (∑ a in s, f a) = ∑ a in s, ennreal.to_nnreal (f a) :=
begin
  rw [← coe_eq_coe, coe_to_nnreal, coe_finset_sum, sum_congr rfl],
  { intros x hx, exact (coe_to_nnreal (hf x hx)).symm },
  { exact (sum_lt_top hf).ne }
end

/-- seeing `ℝ≥0∞` as `real` does not change their sum, unless one of the `ℝ≥0∞` is infinity -/
lemma to_real_sum {s : finset α} {f : α → ℝ≥0∞} (hf : ∀ a ∈ s, f a ≠ ∞) :
  ennreal.to_real (∑ a in s, f a) = ∑ a in s, ennreal.to_real (f a) :=
by { rw [ennreal.to_real, to_nnreal_sum hf, nnreal.coe_sum], refl }

lemma of_real_sum_of_nonneg {s : finset α} {f : α → ℝ} (hf : ∀ i, i ∈ s → 0 ≤ f i) :
  ennreal.of_real (∑ i in s, f i) = ∑ i in s, ennreal.of_real (f i) :=
begin
  simp_rw [ennreal.of_real, ←coe_finset_sum, coe_eq_coe],
  exact real.to_nnreal_sum_of_nonneg hf,
end

theorem sum_lt_sum_of_nonempty {s : finset α} (hs : s.nonempty)
  {f g : α → ℝ≥0∞} (Hlt : ∀ i ∈ s, f i < g i) :
  ∑ i in s, f i < ∑ i in s, g i :=
begin
  induction hs using finset.nonempty.cons_induction with a a s as hs IH,
  { simp [Hlt _ (finset.mem_singleton_self _)] },
  { simp only [as, finset.sum_cons, not_false_iff],
    exact ennreal.add_lt_add (Hlt _ (finset.mem_cons_self _ _))
      (IH (λ i hi, Hlt _ (finset.mem_cons.2 $ or.inr hi))) }
end

theorem exists_le_of_sum_le {s : finset α} (hs : s.nonempty)
  {f g : α → ℝ≥0∞} (Hle : ∑ i in s, f i ≤ ∑ i in s, g i) :
  ∃ i ∈ s, f i ≤ g i :=
begin
  contrapose! Hle,
  apply ennreal.sum_lt_sum_of_nonempty hs Hle,
end

end sum

section interval

variables {x y z : ℝ≥0∞} {ε ε₁ ε₂ : ℝ≥0∞} {s : set ℝ≥0∞}

protected lemma Ico_eq_Iio : (Ico 0 y) = (Iio y) := Ico_bot

lemma mem_Iio_self_add : x ≠ ∞ → ε ≠ 0 → x ∈ Iio (x + ε) :=
assume xt ε0, lt_add_right xt ε0

lemma mem_Ioo_self_sub_add : x ≠ ∞ → x ≠ 0 → ε₁ ≠ 0 → ε₂ ≠ 0 → x ∈ Ioo (x - ε₁) (x + ε₂) :=
assume xt x0 ε0 ε0', ⟨ennreal.sub_lt_self xt x0 ε0, lt_add_right xt ε0'⟩

end interval

section bit

@[mono] lemma bit0_strict_mono : strict_mono (bit0 : ℝ≥0∞ → ℝ≥0∞) := λ a b h, add_lt_add h h
lemma bit0_injective : function.injective (bit0 : ℝ≥0∞ → ℝ≥0∞) := bit0_strict_mono.injective

@[simp] lemma bit0_lt_bit0 : bit0 a < bit0 b ↔ a < b := bit0_strict_mono.lt_iff_lt
@[simp, mono] lemma bit0_le_bit0 : bit0 a ≤ bit0 b ↔ a ≤ b := bit0_strict_mono.le_iff_le
@[simp] lemma bit0_inj : bit0 a = bit0 b ↔ a = b := bit0_injective.eq_iff

@[simp] lemma bit0_eq_zero_iff : bit0 a = 0 ↔ a = 0 := bit0_injective.eq_iff' bit0_zero
@[simp] lemma bit0_top : bit0 ∞ = ∞ := add_top _
@[simp] lemma bit0_eq_top_iff : bit0 a = ∞ ↔ a = ∞ := bit0_injective.eq_iff' bit0_top

@[mono] lemma bit1_strict_mono : strict_mono (bit1 : ℝ≥0∞ → ℝ≥0∞) :=
λ a b h, ennreal.add_lt_add_right one_ne_top (bit0_strict_mono h)

lemma bit1_injective : function.injective (bit1 : ℝ≥0∞ → ℝ≥0∞) := bit1_strict_mono.injective

@[simp] lemma bit1_lt_bit1 : bit1 a < bit1 b ↔ a < b := bit1_strict_mono.lt_iff_lt
@[simp, mono] lemma bit1_le_bit1 : bit1 a ≤ bit1 b ↔ a ≤ b := bit1_strict_mono.le_iff_le
@[simp] lemma bit1_inj : bit1 a = bit1 b ↔ a = b := bit1_injective.eq_iff
@[simp] lemma bit1_ne_zero : bit1 a ≠ 0 := by simp [bit1]
@[simp] lemma bit1_top : bit1 ∞ = ∞ := by rw [bit1, bit0_top, top_add]
@[simp] lemma bit1_eq_top_iff : bit1 a = ∞ ↔ a = ∞ := bit1_injective.eq_iff' bit1_top
@[simp] lemma bit1_eq_one_iff : bit1 a = 1 ↔ a = 0 := bit1_injective.eq_iff' bit1_zero

end bit

section inv
noncomputable theory

instance : has_inv ℝ≥0∞ := ⟨λa, Inf {b | 1 ≤ a * b}⟩

instance : div_inv_monoid ℝ≥0∞ :=
{ inv := has_inv.inv,
  .. (infer_instance : monoid ℝ≥0∞) }

lemma div_eq_inv_mul : a / b = b⁻¹ * a := by rw [div_eq_mul_inv, mul_comm]

@[simp] lemma inv_zero : (0 : ℝ≥0∞)⁻¹ = ∞ :=
show Inf {b : ℝ≥0∞ | 1 ≤ 0 * b} = ∞, by simp; refl

@[simp] lemma inv_top : ∞⁻¹ = 0 :=
bot_unique $ le_of_forall_le_of_dense $ λ a (h : a > 0), Inf_le $ by simp [*, ne_of_gt h, top_mul]

lemma coe_inv_le : (↑r⁻¹ : ℝ≥0∞) ≤ (↑r)⁻¹ :=
le_Inf $ assume b (hb : 1 ≤ ↑r * b), coe_le_iff.2 $
  by { rintro b rfl, apply nnreal.inv_le_of_le_mul, rwa [← coe_mul, ← coe_one, coe_le_coe] at hb }

@[simp, norm_cast] lemma coe_inv (hr : r ≠ 0) : (↑r⁻¹ : ℝ≥0∞) = (↑r)⁻¹ :=
coe_inv_le.antisymm $ Inf_le $ le_of_eq $ by rw [← coe_mul, mul_inv_cancel hr, coe_one]

@[norm_cast] lemma coe_inv_two : ((2⁻¹ : ℝ≥0) : ℝ≥0∞) = 2⁻¹ :=
by rw [coe_inv _root_.two_ne_zero, coe_two]

@[simp, norm_cast] lemma coe_div (hr : r ≠ 0) : (↑(p / r) : ℝ≥0∞) = p / r :=
by rw [div_eq_mul_inv, div_eq_mul_inv, coe_mul, coe_inv hr]

lemma div_zero (h : a ≠ 0) : a / 0 = ∞ := by simp [div_eq_mul_inv, h]

instance : div_inv_one_monoid ℝ≥0∞ :=
{ inv_one := by simpa only [coe_inv one_ne_zero, coe_one] using coe_eq_coe.2 inv_one,
  ..ennreal.div_inv_monoid }

protected lemma inv_pow {n : ℕ} : (a^n)⁻¹ = (a⁻¹)^n :=
begin
  cases n, { simp only [pow_zero, inv_one] },
  induction a using with_top.rec_top_coe, { simp [top_pow n.succ_pos] },
  rcases eq_or_ne a 0 with rfl|ha, { simp [top_pow, zero_pow, n.succ_pos] },
  rw [← coe_inv ha, ← coe_pow, ← coe_inv (pow_ne_zero _ ha), ← inv_pow, coe_pow]
end

protected lemma mul_inv_cancel (h0 : a ≠ 0) (ht : a ≠ ∞) : a * a⁻¹ = 1 :=
begin
  lift a to ℝ≥0 using ht,
  norm_cast at *,
  exact mul_inv_cancel h0
end

protected lemma inv_mul_cancel (h0 : a ≠ 0) (ht : a ≠ ∞) : a⁻¹ * a = 1 :=
mul_comm a a⁻¹ ▸ ennreal.mul_inv_cancel h0 ht

protected lemma div_mul_cancel (h0 : a ≠ 0) (hI : a ≠ ∞) : (b / a) * a = b :=
by rw [div_eq_mul_inv, mul_assoc, ennreal.inv_mul_cancel h0 hI, mul_one]

protected lemma mul_div_cancel' (h0 : a ≠ 0) (hI : a ≠ ∞) : a * (b / a) = b :=
by rw [mul_comm, ennreal.div_mul_cancel h0 hI]

instance : has_involutive_inv ℝ≥0∞ :=
{ inv := has_inv.inv,
  inv_inv := λ a, by
    by_cases a = 0; cases a; simp [*, none_eq_top, some_eq_coe, -coe_inv, (coe_inv _).symm] at * }

@[simp] lemma inv_eq_top : a⁻¹ = ∞ ↔ a = 0 :=
inv_zero ▸ inv_inj

lemma inv_ne_top : a⁻¹ ≠ ∞ ↔ a ≠ 0 := by simp

@[simp] lemma inv_lt_top {x : ℝ≥0∞} : x⁻¹ < ∞ ↔ 0 < x :=
by { simp only [lt_top_iff_ne_top, inv_ne_top, pos_iff_ne_zero] }

lemma div_lt_top {x y : ℝ≥0∞} (h1 : x ≠ ∞) (h2 : y ≠ 0) : x / y < ∞ :=
mul_lt_top h1 (inv_ne_top.mpr h2)

@[simp] protected lemma inv_eq_zero : a⁻¹ = 0 ↔ a = ∞ :=
inv_top ▸ inv_inj

protected lemma inv_ne_zero : a⁻¹ ≠ 0 ↔ a ≠ ∞ := by simp

protected lemma mul_inv {a b : ℝ≥0∞} (ha : a ≠ 0 ∨ b ≠ ∞) (hb : a ≠ ∞ ∨ b ≠ 0) :
  (a * b)⁻¹ = a⁻¹ * b⁻¹ :=
begin
  induction b using with_top.rec_top_coe,
  { replace ha : a ≠ 0 := ha.neg_resolve_right rfl,
    simp [ha], },
  induction a using with_top.rec_top_coe,
  { replace hb : b ≠ 0 := coe_ne_zero.1 (hb.neg_resolve_left rfl),
    simp [hb] },
  by_cases h'a : a = 0,
  { simp only [h'a, with_top.top_mul, ennreal.inv_zero, ennreal.coe_ne_top, zero_mul, ne.def,
               not_false_iff, ennreal.coe_zero, ennreal.inv_eq_zero] },
  by_cases h'b : b = 0,
  { simp only [h'b, ennreal.inv_zero, ennreal.coe_ne_top, with_top.mul_top, ne.def, not_false_iff,
               mul_zero, ennreal.coe_zero, ennreal.inv_eq_zero] },
  rw [← ennreal.coe_mul, ← ennreal.coe_inv, ← ennreal.coe_inv h'a, ← ennreal.coe_inv h'b,
      ← ennreal.coe_mul, mul_inv_rev, mul_comm],
  simp [h'a, h'b],
end

protected lemma mul_div_mul_left (a b : ℝ≥0∞) (hc : c ≠ 0) (hc' : c ≠ ⊤) :
  c * a / (c * b) = a / b :=
by rw [div_eq_mul_inv, div_eq_mul_inv, ennreal.mul_inv (or.inl hc) (or.inl hc'), mul_mul_mul_comm,
  ennreal.mul_inv_cancel hc hc', one_mul]

protected lemma mul_div_mul_right (a b : ℝ≥0∞) (hc : c ≠ 0) (hc' : c ≠ ⊤) :
  a * c / (b * c) = a / b :=
by rw [div_eq_mul_inv, div_eq_mul_inv, ennreal.mul_inv (or.inr hc') (or.inr hc), mul_mul_mul_comm,
  ennreal.mul_inv_cancel hc hc', mul_one]

protected lemma sub_div (h : 0 < b → b < a → c ≠ 0) : (a - b) / c = a / c - b / c :=
by { simp_rw div_eq_mul_inv, exact ennreal.sub_mul (by simpa using h) }

@[simp] protected lemma inv_pos : 0 < a⁻¹ ↔ a ≠ ∞ := pos_iff_ne_zero.trans ennreal.inv_ne_zero

lemma inv_strict_anti : strict_anti (has_inv.inv : ℝ≥0∞ → ℝ≥0∞) :=
begin
  intros a b h,
  lift a to ℝ≥0 using h.ne_top,
  induction b using with_top.rec_top_coe, { simp },
  rw [coe_lt_coe] at h,
  rcases eq_or_ne a 0 with rfl|ha, { simp [h] },
  rw [← coe_inv h.ne_bot, ← coe_inv ha, coe_lt_coe],
  exact nnreal.inv_lt_inv ha h
end

@[simp] protected lemma inv_lt_inv : a⁻¹ < b⁻¹ ↔ b < a := inv_strict_anti.lt_iff_lt

lemma inv_lt_iff_inv_lt : a⁻¹ < b ↔ b⁻¹ < a :=
by simpa only [inv_inv] using @ennreal.inv_lt_inv a b⁻¹

lemma lt_inv_iff_lt_inv : a < b⁻¹ ↔ b < a⁻¹ :=
by simpa only [inv_inv] using @ennreal.inv_lt_inv a⁻¹ b

@[simp, priority 1100] -- higher than le_inv_iff_mul_le
protected lemma inv_le_inv : a⁻¹ ≤ b⁻¹ ↔ b ≤ a := inv_strict_anti.le_iff_le

lemma inv_le_iff_inv_le : a⁻¹ ≤ b ↔ b⁻¹ ≤ a :=
by simpa only [inv_inv] using @ennreal.inv_le_inv a b⁻¹

lemma le_inv_iff_le_inv : a ≤ b⁻¹ ↔ b ≤ a⁻¹ :=
by simpa only [inv_inv] using @ennreal.inv_le_inv a⁻¹ b

@[simp] protected lemma inv_le_one : a⁻¹ ≤ 1 ↔ 1 ≤ a := by rw [inv_le_iff_inv_le, inv_one]
protected lemma one_le_inv : 1 ≤ a⁻¹ ↔ a ≤ 1 := by rw [le_inv_iff_le_inv, inv_one]
@[simp] protected lemma inv_lt_one : a⁻¹ < 1 ↔ 1 < a := by rw [inv_lt_iff_inv_lt, inv_one]
@[simp] protected lemma one_lt_inv : 1 < a⁻¹ ↔ a < 1 := by rw [lt_inv_iff_lt_inv, inv_one]

/-- The inverse map `λ x, x⁻¹` is an order isomorphism between `ℝ≥0∞` and its `order_dual` -/
@[simps apply]
def _root_.order_iso.inv_ennreal : ℝ≥0∞ ≃o ℝ≥0∞ᵒᵈ :=
{ map_rel_iff' := λ a b, ennreal.inv_le_inv,
  to_equiv := (equiv.inv ℝ≥0∞).trans order_dual.to_dual }

@[simp]
lemma _root_.order_iso.inv_ennreal_symm_apply :
  order_iso.inv_ennreal.symm a = (order_dual.of_dual a)⁻¹ := rfl

@[simp] lemma div_top : a / ∞ = 0 := by rw [div_eq_mul_inv, inv_top, mul_zero]

@[simp] lemma top_div_coe : ∞ / p = ∞ := by simp [div_eq_mul_inv, top_mul]

lemma top_div_of_ne_top (h : a ≠ ∞) : ∞ / a = ∞ :=
by { lift a to ℝ≥0 using h, exact top_div_coe }

lemma top_div_of_lt_top (h : a < ∞) : ∞ / a = ∞ :=
top_div_of_ne_top h.ne

lemma top_div : ∞ / a = if a = ∞ then 0 else ∞ :=
by by_cases a = ∞; simp [top_div_of_ne_top, *]

@[simp] protected lemma zero_div : 0 / a = 0 := zero_mul a⁻¹

lemma div_eq_top : a / b = ∞ ↔ (a ≠ 0 ∧ b = 0) ∨ (a = ∞ ∧ b ≠ ∞) :=
by simp [div_eq_mul_inv, ennreal.mul_eq_top]

protected lemma le_div_iff_mul_le (h0 : b ≠ 0 ∨ c ≠ 0) (ht : b ≠ ∞ ∨ c ≠ ∞) :
  a ≤ c / b ↔ a * b ≤ c :=
begin
  induction b using with_top.rec_top_coe,
  { lift c to ℝ≥0 using ht.neg_resolve_left rfl,
    rw [div_top, nonpos_iff_eq_zero, mul_top],
    rcases eq_or_ne a 0 with rfl|ha; simp * },
  rcases eq_or_ne b 0 with (rfl | hb),
  { have hc : c ≠ 0, from h0.neg_resolve_left rfl,
    simp [div_zero hc] },
  { rw [← coe_ne_zero] at hb,
    rw [← ennreal.mul_le_mul_right hb coe_ne_top, ennreal.div_mul_cancel hb coe_ne_top] },
end

protected lemma div_le_iff_le_mul (hb0 : b ≠ 0 ∨ c ≠ ∞) (hbt : b ≠ ∞ ∨ c ≠ 0) :
  a / b ≤ c ↔ a ≤ c * b :=
begin
  suffices : a * b⁻¹ ≤ c ↔ a ≤ c / b⁻¹, by simpa [div_eq_mul_inv],
  refine (ennreal.le_div_iff_mul_le _ _).symm; simpa
end

protected lemma lt_div_iff_mul_lt (hb0 : b ≠ 0 ∨ c ≠ ∞) (hbt : b ≠ ∞ ∨ c ≠ 0) :
  c < a / b ↔ c * b < a :=
lt_iff_lt_of_le_iff_le (ennreal.div_le_iff_le_mul hb0 hbt)

lemma div_le_of_le_mul (h : a ≤ b * c) : a / c ≤ b :=
begin
  by_cases h0 : c = 0,
  { have : a = 0, by simpa [h0] using h, simp [*] },
  by_cases hinf : c = ∞, by simp [hinf],
  exact (ennreal.div_le_iff_le_mul (or.inl h0) (or.inl hinf)).2 h
end

lemma div_le_of_le_mul' (h : a ≤ b * c) : a / b ≤ c :=
div_le_of_le_mul $ mul_comm b c ▸ h

lemma mul_le_of_le_div (h : a ≤ b / c) : a * c ≤ b :=
begin
  rw [← inv_inv c],
  exact div_le_of_le_mul h,
end

lemma mul_le_of_le_div' (h : a ≤ b / c) : c * a ≤ b :=
mul_comm a c ▸ mul_le_of_le_div h

protected lemma div_lt_iff (h0 : b ≠ 0 ∨ c ≠ 0) (ht : b ≠ ∞ ∨ c ≠ ∞) :
  c / b < a ↔ c < a * b :=
lt_iff_lt_of_le_iff_le $ ennreal.le_div_iff_mul_le h0 ht

lemma mul_lt_of_lt_div (h : a < b / c) : a * c < b :=
by { contrapose! h, exact ennreal.div_le_of_le_mul h }

lemma mul_lt_of_lt_div' (h : a < b / c) : c * a < b := mul_comm a c ▸ mul_lt_of_lt_div h

lemma inv_le_iff_le_mul (h₁ : b = ∞ → a ≠ 0) (h₂ : a = ∞ → b ≠ 0) : a⁻¹ ≤ b ↔ 1 ≤ a * b :=
begin
  rw [← one_div, ennreal.div_le_iff_le_mul, mul_comm],
  exacts [or_not_of_imp h₁, not_or_of_imp h₂]
end

@[simp] lemma le_inv_iff_mul_le : a ≤ b⁻¹ ↔ a * b ≤ 1 :=
by rw [← one_div, ennreal.le_div_iff_mul_le]; { right, simp }

protected lemma div_le_div (hab : a ≤ b) (hdc : d ≤ c) : a / c ≤ b / d :=
div_eq_mul_inv b d ▸ div_eq_mul_inv a c ▸ mul_le_mul' hab (ennreal.inv_le_inv.mpr hdc)

protected lemma div_le_div_left (h : a ≤ b) (c : ℝ≥0∞) : c / b ≤ c / a :=
ennreal.div_le_div le_rfl h

protected lemma div_le_div_right (h : a ≤ b) (c : ℝ≥0∞) : a / c ≤ b / c :=
ennreal.div_le_div h le_rfl

protected lemma eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ :=
begin
  rw [←mul_one a, ←ennreal.mul_inv_cancel (right_ne_zero_of_mul_eq_one h), ←mul_assoc, h, one_mul],
  rintro rfl,
  simpa [left_ne_zero_of_mul_eq_one h] using h,
end

lemma mul_le_iff_le_inv {a b r : ℝ≥0∞} (hr₀ : r ≠ 0) (hr₁ : r ≠ ∞) : (r * a ≤ b ↔ a ≤ r⁻¹ * b) :=
by rw [←@ennreal.mul_le_mul_left _ a _ hr₀ hr₁, ←mul_assoc, ennreal.mul_inv_cancel hr₀ hr₁, one_mul]

lemma le_of_forall_nnreal_lt {x y : ℝ≥0∞} (h : ∀ r : ℝ≥0, ↑r < x → ↑r ≤ y) : x ≤ y :=
begin
  refine le_of_forall_ge_of_dense (λ r hr, _),
  lift r to ℝ≥0 using ne_top_of_lt hr,
  exact h r hr
end

lemma le_of_forall_pos_nnreal_lt {x y : ℝ≥0∞} (h : ∀ r : ℝ≥0, 0 < r → ↑r < x → ↑r ≤ y) : x ≤ y :=
le_of_forall_nnreal_lt $ λ r hr, (zero_le r).eq_or_lt.elim (λ h, h ▸ zero_le _) (λ h0, h r h0 hr)

lemma eq_top_of_forall_nnreal_le {x : ℝ≥0∞} (h : ∀ r : ℝ≥0, ↑r ≤ x) : x = ∞ :=
top_unique $ le_of_forall_nnreal_lt $ λ r hr, h r

protected lemma add_div : (a + b) / c = a / c + b / c := right_distrib a b (c⁻¹)

protected lemma div_add_div_same {a b c : ℝ≥0∞} : a / c + b / c = (a + b) / c :=
ennreal.add_div.symm

protected lemma div_self (h0 : a ≠ 0) (hI : a ≠ ∞) : a / a = 1 :=
ennreal.mul_inv_cancel h0 hI

lemma mul_div_le : a * (b / a) ≤ b := mul_le_of_le_div' le_rfl

-- TODO: add this lemma for an `is_unit` in any `division_monoid`
lemma eq_div_iff (ha : a ≠ 0) (ha' : a ≠ ∞) :
  b = c / a ↔ a * b = c :=
⟨λ h, by rw [h, ennreal.mul_div_cancel' ha ha'],
 λ h, by rw [← h, mul_div_assoc, ennreal.mul_div_cancel' ha ha']⟩

protected lemma div_eq_div_iff (ha : a ≠ 0) (ha' : a ≠ ∞) (hb : b ≠ 0) (hb' : b ≠ ∞) :
  c / b = d / a ↔ a * c = b * d :=
begin
  rw eq_div_iff ha ha',
  conv_rhs { rw eq_comm },
  rw [← eq_div_iff hb hb', mul_div_assoc, eq_comm],
end

lemma div_eq_one_iff {a b : ℝ≥0∞} (hb₀ : b ≠ 0) (hb₁ : b ≠ ∞) : a / b = 1 ↔ a = b :=
⟨λ h, by rw [← (eq_div_iff hb₀ hb₁).mp h.symm, mul_one], λ h, h.symm ▸ ennreal.div_self hb₀ hb₁⟩

lemma inv_two_add_inv_two : (2:ℝ≥0∞)⁻¹ + 2⁻¹ = 1 :=
by rw [← two_mul, ← div_eq_mul_inv, ennreal.div_self two_ne_zero two_ne_top]

lemma inv_three_add_inv_three : (3 : ℝ≥0∞)⁻¹ + 3⁻¹ + 3⁻¹ = 1 :=
begin
  rw [show (3 : ℝ≥0∞)⁻¹ + 3⁻¹ + 3⁻¹ = 3 * 3⁻¹, by ring, ← div_eq_mul_inv, ennreal.div_self];
  simp,
end

@[simp]
protected lemma add_halves (a : ℝ≥0∞) : a / 2 + a / 2 = a :=
by rw [div_eq_mul_inv, ← mul_add, inv_two_add_inv_two, mul_one]

@[simp]
lemma add_thirds (a : ℝ≥0∞) : a / 3 + a / 3 + a / 3 = a :=
by rw [div_eq_mul_inv, ← mul_add, ← mul_add, inv_three_add_inv_three, mul_one]

@[simp] lemma div_zero_iff : a / b = 0 ↔ a = 0 ∨ b = ∞ :=
by simp [div_eq_mul_inv]

@[simp] lemma div_pos_iff : 0 < a / b ↔ a ≠ 0 ∧ b ≠ ∞ :=
by simp [pos_iff_ne_zero, not_or_distrib]

protected lemma half_pos (h : a ≠ 0) : 0 < a / 2 := by simp [h]

protected lemma one_half_lt_one : (2⁻¹ : ℝ≥0∞) < 1 := ennreal.inv_lt_one.2 $ one_lt_two

protected lemma half_lt_self (hz : a ≠ 0) (ht : a ≠ ∞) : a / 2 < a :=
begin
  lift a to ℝ≥0 using ht,
  rw coe_ne_zero at hz,
  rw [← coe_two, ← coe_div, coe_lt_coe],
  exacts [nnreal.half_lt_self hz, two_ne_zero' _]
end

protected lemma half_le_self : a / 2 ≤ a := le_add_self.trans_eq $ ennreal.add_halves _

lemma sub_half (h : a ≠ ∞) : a - a / 2 = a / 2 :=
begin
  lift a to ℝ≥0 using h,
  exact sub_eq_of_add_eq (mul_ne_top coe_ne_top $ by simp) (ennreal.add_halves a)
end

@[simp] lemma one_sub_inv_two : (1:ℝ≥0∞) - 2⁻¹ = 2⁻¹ :=
by simpa only [div_eq_mul_inv, one_mul] using sub_half one_ne_top

/-- The birational order isomorphism between `ℝ≥0∞` and the unit interval `set.Iic (1 : ℝ≥0∞)`. -/
@[simps apply_coe] def order_iso_Iic_one_birational : ℝ≥0∞ ≃o Iic (1 : ℝ≥0∞) :=
begin
  refine strict_mono.order_iso_of_right_inverse
    (λ x, ⟨(x⁻¹ + 1)⁻¹, ennreal.inv_le_one.2 $ le_add_self⟩) (λ x y hxy, _) (λ x, (x⁻¹ - 1)⁻¹)
    (λ x, subtype.ext _),
  { simpa only [subtype.mk_lt_mk, ennreal.inv_lt_inv, ennreal.add_lt_add_iff_right one_ne_top] },
  { have : (1 : ℝ≥0∞) ≤ x⁻¹, from ennreal.one_le_inv.2 x.2,
    simp only [inv_inv, subtype.coe_mk, tsub_add_cancel_of_le this] }
end

@[simp] lemma order_iso_Iic_one_birational_symm_apply (x : Iic (1 : ℝ≥0∞)) :
  order_iso_Iic_one_birational.symm x = (x⁻¹ - 1)⁻¹ :=
rfl

/-- Order isomorphism between an initial interval in `ℝ≥0∞` and an initial interval in `ℝ≥0`. -/
@[simps apply_coe] def order_iso_Iic_coe (a : ℝ≥0) : Iic (a : ℝ≥0∞) ≃o Iic a :=
order_iso.symm
{ to_fun := λ x, ⟨x, coe_le_coe.2 x.2⟩,
  inv_fun := λ x, ⟨ennreal.to_nnreal x, coe_le_coe.1 $ coe_to_nnreal_le_self.trans x.2⟩,
  left_inv := λ x, subtype.ext $ to_nnreal_coe,
  right_inv := λ x, subtype.ext $ coe_to_nnreal (ne_top_of_le_ne_top coe_ne_top x.2),
  map_rel_iff' := λ x y, by simp only [equiv.coe_fn_mk, subtype.mk_le_mk, coe_coe, coe_le_coe,
    subtype.coe_le_coe] }

@[simp] lemma order_iso_Iic_coe_symm_apply_coe (a : ℝ≥0) (b : Iic a) :
  ((order_iso_Iic_coe a).symm b : ℝ≥0∞) = b := rfl

/-- An order isomorphism between the extended nonnegative real numbers and the unit interval. -/
def order_iso_unit_interval_birational : ℝ≥0∞ ≃o Icc (0 : ℝ) 1 :=
order_iso_Iic_one_birational.trans $ (order_iso_Iic_coe 1).trans $
  (nnreal.order_iso_Icc_zero_coe 1).symm

@[simp] lemma order_iso_unit_interval_birational_apply_coe (x : ℝ≥0∞) :
  (order_iso_unit_interval_birational x : ℝ) = (x⁻¹ + 1)⁻¹.to_real :=
rfl

lemma exists_inv_nat_lt {a : ℝ≥0∞} (h : a ≠ 0) :
  ∃n:ℕ, (n:ℝ≥0∞)⁻¹ < a :=
inv_inv a ▸ by simp only [ennreal.inv_lt_inv, ennreal.exists_nat_gt (inv_ne_top.2 h)]

lemma exists_nat_pos_mul_gt (ha : a ≠ 0) (hb : b ≠ ∞) :
  ∃ n > 0, b < (n : ℕ) * a :=
begin
  have : b / a ≠ ∞, from mul_ne_top hb (inv_ne_top.2 ha),
  refine (ennreal.exists_nat_gt this).imp (λ n hn, _),
  have : 0 < (n : ℝ≥0∞), from lt_of_le_of_lt (zero_le _) hn,
  refine ⟨nat.cast_pos.1 this, _⟩,
  rwa [← ennreal.div_lt_iff (or.inl ha) (or.inr hb)]
end

lemma exists_nat_mul_gt (ha : a ≠ 0) (hb : b ≠ ∞) :
  ∃ n : ℕ, b < n * a :=
(exists_nat_pos_mul_gt ha hb).imp $ λ n, Exists.snd

lemma exists_nat_pos_inv_mul_lt (ha : a ≠ ∞) (hb : b ≠ 0) :
  ∃ n > 0, ((n : ℕ) : ℝ≥0∞)⁻¹ * a < b :=
begin
  rcases exists_nat_pos_mul_gt hb ha with ⟨n, npos, hn⟩,
  have : (n : ℝ≥0∞) ≠ 0 := nat.cast_ne_zero.2 npos.lt.ne',
  use [n, npos],
  rwa [← one_mul b, ← ennreal.inv_mul_cancel this (nat_ne_top n), mul_assoc,
    mul_lt_mul_left (ennreal.inv_ne_zero.2 $ nat_ne_top _) (inv_ne_top.2 this)]
end

lemma exists_nnreal_pos_mul_lt (ha : a ≠ ∞) (hb : b ≠ 0) :
  ∃ n > 0, ↑(n : ℝ≥0) * a < b :=
begin
  rcases exists_nat_pos_inv_mul_lt ha hb with ⟨n, npos : 0 < n, hn⟩,
  use (n : ℝ≥0)⁻¹,
  simp [*, npos.ne', zero_lt_one]
end

lemma exists_inv_two_pow_lt (ha : a ≠ 0) :
  ∃ n : ℕ, 2⁻¹ ^ n < a :=
begin
  rcases exists_inv_nat_lt ha with ⟨n, hn⟩,
  refine ⟨n, lt_trans _ hn⟩,
  rw [← ennreal.inv_pow, ennreal.inv_lt_inv],
  norm_cast,
  exact n.lt_two_pow
end

@[simp, norm_cast] lemma coe_zpow (hr : r ≠ 0) (n : ℤ) : (↑(r^n) : ℝ≥0∞) = r^n :=
begin
  cases n,
  { simp only [int.of_nat_eq_coe, coe_pow, zpow_coe_nat] },
  { have : r ^ n.succ ≠ 0 := pow_ne_zero (n+1) hr,
    simp only [zpow_neg_succ_of_nat, coe_inv this, coe_pow] }
end

lemma zpow_pos (ha : a ≠ 0) (h'a : a ≠ ∞) (n : ℤ) : 0 < a ^ n :=
begin
  cases n,
  { exact ennreal.pow_pos ha.bot_lt n },
  { simp only [h'a, pow_eq_top_iff, zpow_neg_succ_of_nat, ne.def, not_false_iff,
               ennreal.inv_pos, false_and] }
end

lemma zpow_lt_top (ha : a ≠ 0) (h'a : a ≠ ∞) (n : ℤ) : a ^ n < ∞ :=
begin
  cases n,
  { exact ennreal.pow_lt_top h'a.lt_top _ },
  { simp only [ennreal.pow_pos ha.bot_lt (n + 1), zpow_neg_succ_of_nat, inv_lt_top] }
end

lemma exists_mem_Ico_zpow
  {x y : ℝ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (hy : 1 < y) (h'y : y ≠ ⊤) :
  ∃ n : ℤ, x ∈ Ico (y ^ n) (y ^ (n + 1)) :=
begin
  lift x to ℝ≥0 using h'x,
  lift y to ℝ≥0 using h'y,
  have A : y ≠ 0, { simpa only [ne.def, coe_eq_zero] using (zero_lt_one.trans hy).ne' },
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, y ^ n ≤ x ∧ x < y ^ (n + 1),
  { refine nnreal.exists_mem_Ico_zpow _ (one_lt_coe_iff.1 hy),
    simpa only [ne.def, coe_eq_zero] using hx },
  refine ⟨n, _, _⟩,
  { rwa [← ennreal.coe_zpow A, ennreal.coe_le_coe] },
  { rwa [← ennreal.coe_zpow A, ennreal.coe_lt_coe] }
end

lemma exists_mem_Ioc_zpow
  {x y : ℝ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (hy : 1 < y) (h'y : y ≠ ⊤) :
  ∃ n : ℤ, x ∈ Ioc (y ^ n) (y ^ (n + 1)) :=
begin
  lift x to ℝ≥0 using h'x,
  lift y to ℝ≥0 using h'y,
  have A : y ≠ 0, { simpa only [ne.def, coe_eq_zero] using (zero_lt_one.trans hy).ne' },
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, y ^ n < x ∧ x ≤ y ^ (n + 1),
  { refine nnreal.exists_mem_Ioc_zpow _ (one_lt_coe_iff.1 hy),
    simpa only [ne.def, coe_eq_zero] using hx },
  refine ⟨n, _, _⟩,
  { rwa [← ennreal.coe_zpow A, ennreal.coe_lt_coe] },
  { rwa [← ennreal.coe_zpow A, ennreal.coe_le_coe] }
end

lemma Ioo_zero_top_eq_Union_Ico_zpow {y : ℝ≥0∞} (hy : 1 < y) (h'y : y ≠ ⊤) :
  Ioo (0 : ℝ≥0∞) (∞ : ℝ≥0∞) = ⋃ (n : ℤ), Ico (y^n) (y^(n+1)) :=
begin
  ext x,
  simp only [mem_Union, mem_Ioo, mem_Ico],
  split,
  { rintros ⟨hx, h'x⟩,
    exact exists_mem_Ico_zpow hx.ne' h'x.ne hy h'y },
  { rintros ⟨n, hn, h'n⟩,
    split,
    { apply lt_of_lt_of_le _ hn,
      exact ennreal.zpow_pos (zero_lt_one.trans hy).ne' h'y _ },
    { apply lt_trans h'n _,
      exact ennreal.zpow_lt_top (zero_lt_one.trans hy).ne' h'y _ } }
end

lemma zpow_le_of_le {x : ℝ≥0∞} (hx : 1 ≤ x) {a b : ℤ} (h : a ≤ b) : x ^ a ≤ x ^ b :=
begin
  induction a with a a; induction b with b b,
  { simp only [int.of_nat_eq_coe, zpow_coe_nat],
    exact pow_le_pow hx (int.le_of_coe_nat_le_coe_nat h), },
  { apply absurd h (not_le_of_gt _),
    exact lt_of_lt_of_le (int.neg_succ_lt_zero _) (int.of_nat_nonneg _) },
  { simp only [zpow_neg_succ_of_nat, int.of_nat_eq_coe, zpow_coe_nat],
    refine (ennreal.inv_le_one.2 _).trans _;
    exact one_le_pow_of_one_le' hx _, },
  { simp only [zpow_neg_succ_of_nat, ennreal.inv_le_inv],
    apply pow_le_pow hx,
    simpa only [←int.coe_nat_le_coe_nat_iff, neg_le_neg_iff, int.coe_nat_add, int.coe_nat_one,
      int.neg_succ_of_nat_eq] using h }
end

lemma monotone_zpow {x : ℝ≥0∞} (hx : 1 ≤ x) : monotone ((^) x : ℤ → ℝ≥0∞) :=
λ a b h, zpow_le_of_le hx h

protected lemma zpow_add {x : ℝ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (m n : ℤ) :
  x ^ (m + n) = x ^ m * x ^ n :=
begin
  lift x to ℝ≥0 using h'x,
  replace hx : x ≠ 0, by simpa only [ne.def, coe_eq_zero] using hx,
  simp only [← coe_zpow hx, zpow_add₀ hx, coe_mul]
end

end inv

section real

lemma to_real_add (ha : a ≠ ∞) (hb : b ≠ ∞) : (a+b).to_real = a.to_real + b.to_real :=
begin
  lift a to ℝ≥0 using ha,
  lift b to ℝ≥0 using hb,
  refl
end

lemma to_real_sub_of_le {a b : ℝ≥0∞} (h : b ≤ a) (ha : a ≠ ∞):
  (a - b).to_real = a.to_real - b.to_real :=
begin
  lift b to ℝ≥0 using ne_top_of_le_ne_top ha h,
  lift a to ℝ≥0 using ha,
  simp only [← ennreal.coe_sub, ennreal.coe_to_real, nnreal.coe_sub (ennreal.coe_le_coe.mp h)],
end

lemma le_to_real_sub {a b : ℝ≥0∞} (hb : b ≠ ∞) : a.to_real - b.to_real ≤ (a - b).to_real :=
begin
  lift b to ℝ≥0 using hb,
  induction a using with_top.rec_top_coe,
  { simp },
  { simp only [←coe_sub, nnreal.sub_def, real.coe_to_nnreal', coe_to_real],
    exact le_max_left _ _ }
end

lemma to_real_add_le : (a+b).to_real ≤ a.to_real + b.to_real :=
if ha : a = ∞ then by simp only [ha, top_add, top_to_real, zero_add, to_real_nonneg]
else if hb : b = ∞ then by simp only [hb, add_top, top_to_real, add_zero, to_real_nonneg]
else le_of_eq (to_real_add ha hb)

lemma of_real_add {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
  ennreal.of_real (p + q) = ennreal.of_real p + ennreal.of_real q :=
by rw [ennreal.of_real, ennreal.of_real, ennreal.of_real, ← coe_add,
       coe_eq_coe, real.to_nnreal_add hp hq]

lemma of_real_add_le {p q : ℝ} : ennreal.of_real (p + q) ≤ ennreal.of_real p + ennreal.of_real q :=
coe_le_coe.2 real.to_nnreal_add_le

@[simp] lemma to_real_le_to_real (ha : a ≠ ∞) (hb : b ≠ ∞) : a.to_real ≤ b.to_real ↔ a ≤ b :=
begin
  lift a to ℝ≥0 using ha,
  lift b to ℝ≥0 using hb,
  norm_cast
end

lemma to_real_mono (hb : b ≠ ∞) (h : a ≤ b) : a.to_real ≤ b.to_real :=
(to_real_le_to_real (h.trans_lt (lt_top_iff_ne_top.2 hb)).ne hb).2 h

@[simp] lemma to_real_lt_to_real (ha : a ≠ ∞) (hb : b ≠ ∞) : a.to_real < b.to_real ↔ a < b :=
begin
  lift a to ℝ≥0 using ha,
  lift b to ℝ≥0 using hb,
  norm_cast
end

lemma to_real_strict_mono (hb : b ≠ ∞) (h : a < b) : a.to_real < b.to_real :=
(to_real_lt_to_real (h.trans (lt_top_iff_ne_top.2 hb)).ne hb).2 h

lemma to_nnreal_mono (hb : b ≠ ∞) (h : a ≤ b) : a.to_nnreal ≤ b.to_nnreal :=
by simpa [←ennreal.coe_le_coe, hb, (h.trans_lt hb.lt_top).ne]

@[simp] lemma to_nnreal_le_to_nnreal (ha : a ≠ ∞) (hb : b ≠ ∞) :
  a.to_nnreal ≤ b.to_nnreal ↔ a ≤ b :=
⟨λ h, by rwa [←coe_to_nnreal ha, ←coe_to_nnreal hb, coe_le_coe], to_nnreal_mono hb⟩

lemma to_nnreal_strict_mono (hb : b ≠ ∞) (h : a < b) : a.to_nnreal < b.to_nnreal :=
by simpa [←ennreal.coe_lt_coe, hb, (h.trans hb.lt_top).ne]

@[simp] lemma to_nnreal_lt_to_nnreal (ha : a ≠ ∞) (hb : b ≠ ∞) :
  a.to_nnreal < b.to_nnreal ↔ a < b :=
⟨λ h, by rwa [←coe_to_nnreal ha, ←coe_to_nnreal hb, coe_lt_coe], to_nnreal_strict_mono hb⟩

lemma to_real_max (hr : a ≠ ∞) (hp : b ≠ ∞) :
  ennreal.to_real (max a b) = max (ennreal.to_real a) (ennreal.to_real b) :=
(le_total a b).elim
  (λ h, by simp only [h, (ennreal.to_real_le_to_real hr hp).2 h, max_eq_right])
  (λ h, by simp only [h, (ennreal.to_real_le_to_real hp hr).2 h, max_eq_left])

lemma to_real_min {a b : ℝ≥0∞} (hr : a ≠ ∞) (hp : b ≠ ∞) :
  ennreal.to_real (min a b) = min (ennreal.to_real a) (ennreal.to_real b) :=
(le_total a b).elim
  (λ h, by simp only [h, (ennreal.to_real_le_to_real hr hp).2 h, min_eq_left])
  (λ h, by simp only [h, (ennreal.to_real_le_to_real hp hr).2 h, min_eq_right])

lemma to_real_sup {a b : ℝ≥0∞}
  : a ≠ ∞ → b ≠ ∞ → (a ⊔ b).to_real = a.to_real ⊔ b.to_real := to_real_max

lemma to_real_inf {a b : ℝ≥0∞}
  : a ≠ ∞ → b ≠ ∞ → (a ⊓ b).to_real = a.to_real ⊓ b.to_real := to_real_min

lemma to_nnreal_pos_iff : 0 < a.to_nnreal ↔ (0 < a ∧ a < ∞) :=
by { induction a using with_top.rec_top_coe; simp }

lemma to_nnreal_pos {a : ℝ≥0∞} (ha₀ : a ≠ 0) (ha_top : a ≠ ∞) : 0 < a.to_nnreal :=
to_nnreal_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr ha₀, lt_top_iff_ne_top.mpr ha_top⟩

lemma to_real_pos_iff : 0 < a.to_real ↔ (0 < a ∧ a < ∞):=
(nnreal.coe_pos).trans to_nnreal_pos_iff

lemma to_real_pos {a : ℝ≥0∞} (ha₀ : a ≠ 0) (ha_top : a ≠ ∞) : 0 < a.to_real :=
to_real_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr ha₀, lt_top_iff_ne_top.mpr ha_top⟩

lemma of_real_le_of_real {p q : ℝ} (h : p ≤ q) : ennreal.of_real p ≤ ennreal.of_real q :=
by simp [ennreal.of_real, real.to_nnreal_le_to_nnreal h]

lemma of_real_le_of_le_to_real {a : ℝ} {b : ℝ≥0∞} (h : a ≤ ennreal.to_real b) :
  ennreal.of_real a ≤ b :=
(of_real_le_of_real h).trans of_real_to_real_le

@[simp] lemma of_real_le_of_real_iff {p q : ℝ} (h : 0 ≤ q) :
  ennreal.of_real p ≤ ennreal.of_real q ↔ p ≤ q :=
by rw [ennreal.of_real, ennreal.of_real, coe_le_coe, real.to_nnreal_le_to_nnreal_iff h]

@[simp] lemma of_real_eq_of_real_iff {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
  ennreal.of_real p = ennreal.of_real q ↔ p = q :=
by rw [ennreal.of_real, ennreal.of_real, coe_eq_coe, real.to_nnreal_eq_to_nnreal_iff hp hq]

@[simp] lemma of_real_lt_of_real_iff {p q : ℝ} (h : 0 < q) :
  ennreal.of_real p < ennreal.of_real q ↔ p < q :=
by rw [ennreal.of_real, ennreal.of_real, coe_lt_coe, real.to_nnreal_lt_to_nnreal_iff h]

lemma of_real_lt_of_real_iff_of_nonneg {p q : ℝ} (hp : 0 ≤ p) :
  ennreal.of_real p < ennreal.of_real q ↔ p < q :=
by rw [ennreal.of_real, ennreal.of_real, coe_lt_coe, real.to_nnreal_lt_to_nnreal_iff_of_nonneg hp]

@[simp] lemma of_real_pos {p : ℝ} : 0 < ennreal.of_real p ↔ 0 < p :=
by simp [ennreal.of_real]

@[simp] lemma of_real_eq_zero {p : ℝ} : ennreal.of_real p = 0 ↔ p ≤ 0 :=
by simp [ennreal.of_real]

@[simp] lemma zero_eq_of_real {p : ℝ} : 0 = ennreal.of_real p ↔ p ≤ 0 :=
eq_comm.trans of_real_eq_zero

alias of_real_eq_zero ↔ _ of_real_of_nonpos

lemma of_real_sub (p : ℝ) {q : ℝ} (hq : 0 ≤ q) :
  ennreal.of_real (p - q) = ennreal.of_real p - ennreal.of_real q :=
begin
  obtain h | h := le_total p q,
  { rw [of_real_of_nonpos (sub_nonpos_of_le h), tsub_eq_zero_of_le (of_real_le_of_real h)] },
  refine ennreal.eq_sub_of_add_eq of_real_ne_top _,
  rw [←of_real_add (sub_nonneg_of_le h) hq, sub_add_cancel],
end

lemma of_real_le_iff_le_to_real {a : ℝ} {b : ℝ≥0∞} (hb : b ≠ ∞) :
  ennreal.of_real a ≤ b ↔ a ≤ ennreal.to_real b :=
begin
  lift b to ℝ≥0 using hb,
  simpa [ennreal.of_real, ennreal.to_real] using real.to_nnreal_le_iff_le_coe
end

lemma of_real_lt_iff_lt_to_real {a : ℝ} {b : ℝ≥0∞} (ha : 0 ≤ a) (hb : b ≠ ∞) :
  ennreal.of_real a < b ↔ a < ennreal.to_real b :=
begin
  lift b to ℝ≥0 using hb,
  simpa [ennreal.of_real, ennreal.to_real] using real.to_nnreal_lt_iff_lt_coe ha
end

lemma le_of_real_iff_to_real_le {a : ℝ≥0∞} {b : ℝ} (ha : a ≠ ∞) (hb : 0 ≤ b) :
  a ≤ ennreal.of_real b ↔ ennreal.to_real a ≤ b :=
begin
  lift a to ℝ≥0 using ha,
  simpa [ennreal.of_real, ennreal.to_real] using real.le_to_nnreal_iff_coe_le hb
end

lemma to_real_le_of_le_of_real {a : ℝ≥0∞} {b : ℝ} (hb : 0 ≤ b) (h : a ≤ ennreal.of_real b) :
  ennreal.to_real a ≤ b :=
have ha : a ≠ ∞, from ne_top_of_le_ne_top of_real_ne_top h,
(le_of_real_iff_to_real_le ha hb).1 h

lemma lt_of_real_iff_to_real_lt {a : ℝ≥0∞} {b : ℝ} (ha : a ≠ ∞) :
  a < ennreal.of_real b ↔ ennreal.to_real a < b :=
begin
  lift a to ℝ≥0 using ha,
  simpa [ennreal.of_real, ennreal.to_real] using real.lt_to_nnreal_iff_coe_lt
end

lemma of_real_mul {p q : ℝ} (hp : 0 ≤ p) :
  ennreal.of_real (p * q) = ennreal.of_real p * ennreal.of_real q :=
by simp only [ennreal.of_real, ← coe_mul, real.to_nnreal_mul hp]

lemma of_real_mul' {p q : ℝ} (hq : 0 ≤ q) :
  ennreal.of_real (p * q) = ennreal.of_real p * ennreal.of_real q :=
by rw [mul_comm, of_real_mul hq, mul_comm]

lemma of_real_pow {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
  ennreal.of_real (p ^ n) = ennreal.of_real p ^ n :=
by rw [of_real_eq_coe_nnreal hp, ← coe_pow, ← of_real_coe_nnreal, nnreal.coe_pow, nnreal.coe_mk]

lemma of_real_nsmul {x : ℝ} {n : ℕ} :
  ennreal.of_real (n • x) = n • ennreal.of_real x :=
by simp only [nsmul_eq_mul, ← of_real_coe_nat n, ← of_real_mul n.cast_nonneg]

lemma of_real_inv_of_pos {x : ℝ} (hx : 0 < x) :
  (ennreal.of_real x)⁻¹ = ennreal.of_real x⁻¹ :=
by rw [ennreal.of_real, ennreal.of_real, ←@coe_inv (real.to_nnreal x) (by simp [hx]), coe_eq_coe,
  real.to_nnreal_inv.symm]

lemma of_real_div_of_pos {x y : ℝ} (hy : 0 < y) :
  ennreal.of_real (x / y) = ennreal.of_real x / ennreal.of_real y :=
by rw [div_eq_mul_inv, div_eq_mul_inv, of_real_mul' (inv_nonneg.2 hy.le), of_real_inv_of_pos hy]

@[simp] lemma to_nnreal_mul {a b : ℝ≥0∞} : (a * b).to_nnreal = a.to_nnreal * b.to_nnreal :=
with_top.untop'_zero_mul a b

lemma to_nnreal_mul_top (a : ℝ≥0∞) : ennreal.to_nnreal (a * ∞) = 0 := by simp
lemma to_nnreal_top_mul (a : ℝ≥0∞) : ennreal.to_nnreal (∞ * a) = 0 := by simp

@[simp] lemma smul_to_nnreal (a : ℝ≥0) (b : ℝ≥0∞) :
  (a • b).to_nnreal = a * b.to_nnreal :=
begin
  change ((a : ℝ≥0∞) * b).to_nnreal = a * b.to_nnreal,
  simp only [ennreal.to_nnreal_mul, ennreal.to_nnreal_coe],
end

/-- `ennreal.to_nnreal` as a `monoid_hom`. -/
def to_nnreal_hom : ℝ≥0∞ →* ℝ≥0 :=
{ to_fun := ennreal.to_nnreal,
  map_one' := to_nnreal_coe,
  map_mul' := λ _ _, to_nnreal_mul }

@[simp] lemma to_nnreal_pow (a : ℝ≥0∞) (n : ℕ) : (a ^ n).to_nnreal = a.to_nnreal ^ n :=
to_nnreal_hom.map_pow a n

@[simp] lemma to_nnreal_prod {ι : Type*} {s : finset ι} {f : ι → ℝ≥0∞} :
  (∏ i in s, f i).to_nnreal = ∏ i in s, (f i).to_nnreal :=
to_nnreal_hom.map_prod _ _

/-- `ennreal.to_real` as a `monoid_hom`. -/
def to_real_hom : ℝ≥0∞ →* ℝ :=
(nnreal.to_real_hom : ℝ≥0 →* ℝ).comp to_nnreal_hom

@[simp] lemma to_real_mul : (a * b).to_real = a.to_real * b.to_real :=
to_real_hom.map_mul a b

@[simp] lemma to_real_pow (a : ℝ≥0∞) (n : ℕ) : (a ^ n).to_real = a.to_real ^ n :=
to_real_hom.map_pow a n

@[simp] lemma to_real_prod {ι : Type*} {s : finset ι} {f : ι → ℝ≥0∞} :
  (∏ i in s, f i).to_real = ∏ i in s, (f i).to_real :=
to_real_hom.map_prod _ _

lemma to_real_of_real_mul (c : ℝ) (a : ℝ≥0∞) (h : 0 ≤ c) :
  ennreal.to_real ((ennreal.of_real c) * a) = c * ennreal.to_real a :=
by rw [ennreal.to_real_mul, ennreal.to_real_of_real h]

lemma to_real_mul_top (a : ℝ≥0∞) : ennreal.to_real (a * ∞) = 0 :=
by rw [to_real_mul, top_to_real, mul_zero]

lemma to_real_top_mul (a : ℝ≥0∞) : ennreal.to_real (∞ * a) = 0 :=
by { rw mul_comm, exact to_real_mul_top _ }

lemma to_real_eq_to_real (ha : a ≠ ∞) (hb : b ≠ ∞) :
  ennreal.to_real a = ennreal.to_real b ↔ a = b :=
begin
  lift a to ℝ≥0 using ha,
  lift b to ℝ≥0 using hb,
  simp only [coe_eq_coe, nnreal.coe_eq, coe_to_real],
end

lemma to_real_smul (r : ℝ≥0) (s : ℝ≥0∞) :
  (r • s).to_real = r • s.to_real :=
by { rw [ennreal.smul_def, smul_eq_mul, to_real_mul, coe_to_real], refl }

protected lemma trichotomy (p : ℝ≥0∞) : p = 0 ∨ p = ∞ ∨ 0 < p.to_real :=
by simpa only [or_iff_not_imp_left] using to_real_pos

protected lemma trichotomy₂ {p q : ℝ≥0∞} (hpq : p ≤ q) :
  (p = 0 ∧ q = 0) ∨ (p = 0 ∧ q = ∞) ∨ (p = 0 ∧ 0 < q.to_real) ∨ (p = ∞ ∧ q = ∞)
  ∨ (0 < p.to_real ∧ q = ∞) ∨ (0 < p.to_real ∧ 0 < q.to_real ∧ p.to_real ≤ q.to_real) :=
begin
  rcases eq_or_lt_of_le (bot_le : 0 ≤ p) with (rfl : 0 = p) | (hp : 0 < p),
  { simpa using q.trichotomy },
  rcases eq_or_lt_of_le (le_top : q ≤ ∞) with rfl | hq,
  { simpa using p.trichotomy },
  repeat { right },
  have hq' : 0 < q := lt_of_lt_of_le hp hpq,
  have hp' : p < ∞ := lt_of_le_of_lt hpq hq,
  simp [ennreal.to_real_le_to_real hp'.ne hq.ne, ennreal.to_real_pos_iff, hpq, hp, hp', hq', hq],
end

protected lemma dichotomy (p : ℝ≥0∞) [fact (1 ≤ p)] : p = ∞ ∨ 1 ≤ p.to_real :=
begin
  have :  p = ⊤ ∨ 0 < p.to_real ∧ 1 ≤ p.to_real,
  { simpa using ennreal.trichotomy₂ (fact.out _ : 1 ≤ p) },
  exact this.imp_right (λ h, h.2)
end

lemma to_real_pos_iff_ne_top (p : ℝ≥0∞) [fact (1 ≤ p)] : 0 < p.to_real ↔ p ≠ ∞ :=
⟨λ h hp, let this : (0 : ℝ) ≠ 0 := top_to_real ▸ (hp ▸ h.ne : 0 ≠ ∞.to_real) in this rfl,
 λ h, zero_lt_one.trans_le (p.dichotomy.resolve_left h)⟩

lemma to_nnreal_inv (a : ℝ≥0∞) : (a⁻¹).to_nnreal = (a.to_nnreal)⁻¹ :=
begin
  induction a using with_top.rec_top_coe, { simp },
  rcases eq_or_ne a 0 with rfl|ha, { simp },
  rw [← coe_inv ha, to_nnreal_coe, to_nnreal_coe]
end

lemma to_nnreal_div (a b : ℝ≥0∞) : (a / b).to_nnreal = a.to_nnreal / b.to_nnreal :=
by rw [div_eq_mul_inv, to_nnreal_mul, to_nnreal_inv, div_eq_mul_inv]

lemma to_real_inv (a : ℝ≥0∞) : (a⁻¹).to_real = (a.to_real)⁻¹ :=
by { simp_rw ennreal.to_real, norm_cast, exact to_nnreal_inv a, }

lemma to_real_div (a b : ℝ≥0∞) : (a / b).to_real = a.to_real / b.to_real :=
by rw [div_eq_mul_inv, to_real_mul, to_real_inv, div_eq_mul_inv]

lemma of_real_prod_of_nonneg {s : finset α} {f : α → ℝ} (hf : ∀ i, i ∈ s → 0 ≤ f i) :
  ennreal.of_real (∏ i in s, f i) = ∏ i in s, ennreal.of_real (f i) :=
begin
  simp_rw [ennreal.of_real, ←coe_finset_prod, coe_eq_coe],
  exact real.to_nnreal_prod_of_nonneg hf,
end

@[simp] lemma to_nnreal_bit0 {x : ℝ≥0∞} : (bit0 x).to_nnreal = bit0 (x.to_nnreal) :=
begin
  induction x using with_top.rec_top_coe,
  { simp },
  { exact to_nnreal_add coe_ne_top coe_ne_top }
end

@[simp] lemma to_nnreal_bit1 {x : ℝ≥0∞} (hx_top : x ≠ ∞) :
  (bit1 x).to_nnreal = bit1 (x.to_nnreal) :=
by simp [bit1, bit1, to_nnreal_add (by rwa [ne.def, bit0_eq_top_iff]) ennreal.one_ne_top]

@[simp] lemma to_real_bit0 {x : ℝ≥0∞} : (bit0 x).to_real = bit0 (x.to_real) :=
by simp [ennreal.to_real]

@[simp] lemma to_real_bit1 {x : ℝ≥0∞} (hx_top : x ≠ ∞) :
  (bit1 x).to_real = bit1 (x.to_real) :=
by simp [ennreal.to_real, hx_top]

@[simp] lemma of_real_bit0 (r : ℝ) :
  ennreal.of_real (bit0 r) = bit0 (ennreal.of_real r) :=
by simp [ennreal.of_real]

@[simp] lemma of_real_bit1 {r : ℝ} (hr : 0 ≤ r) :
  ennreal.of_real (bit1 r) = bit1 (ennreal.of_real r) :=
(of_real_add (by simp [hr]) zero_le_one).trans (by simp [real.to_nnreal_one, bit1])

end real

section infi
variables {ι : Sort*} {f g : ι → ℝ≥0∞}

lemma infi_add : infi f + a = ⨅i, f i + a :=
le_antisymm
  (le_infi $ assume i, add_le_add (infi_le _ _) $ le_rfl)
  (tsub_le_iff_right.1 $ le_infi $ assume i, tsub_le_iff_right.2 $ infi_le _ _)

lemma supr_sub : (⨆i, f i) - a = (⨆i, f i - a) :=
le_antisymm
  (tsub_le_iff_right.2 $ supr_le $ assume i, tsub_le_iff_right.1 $ le_supr _ i)
  (supr_le $ assume i, tsub_le_tsub (le_supr _ _) (le_refl a))

lemma sub_infi : a - (⨅i, f i) = (⨆i, a - f i) :=
begin
  refine (eq_of_forall_ge_iff $ λ c, _),
  rw [tsub_le_iff_right, add_comm, infi_add],
  simp [tsub_le_iff_right, sub_eq_add_neg, add_comm],
end

lemma Inf_add {s : set ℝ≥0∞} : Inf s + a = ⨅b∈s, b + a :=
by simp [Inf_eq_infi, infi_add]

lemma add_infi {a : ℝ≥0∞} : a + infi f = ⨅b, a + f b :=
by rw [add_comm, infi_add]; simp [add_comm]

lemma infi_add_infi (h : ∀i j, ∃k, f k + g k ≤ f i + g j) : infi f + infi g = (⨅a, f a + g a) :=
suffices (⨅a, f a + g a) ≤ infi f + infi g,
  from le_antisymm (le_infi $ assume a, add_le_add (infi_le _ _) (infi_le _ _)) this,
calc (⨅a, f a + g a) ≤ (⨅ a a', f a + g a') :
    le_infi $ assume a, le_infi $ assume a',
      let ⟨k, h⟩ := h a a' in infi_le_of_le k h
  ... = infi f + infi g :
    by simp [add_infi, infi_add]

lemma infi_sum {f : ι → α → ℝ≥0∞} {s : finset α} [nonempty ι]
  (h : ∀(t : finset α) (i j : ι), ∃k, ∀a∈t, f k a ≤ f i a ∧ f k a ≤ f j a) :
  (⨅i, ∑ a in s, f i a) = ∑ a in s, ⨅i, f i a :=
begin
  induction s using finset.induction_on with a s ha ih,
  { simp },
  have : ∀ (i j : ι), ∃ (k : ι), f k a + ∑ b in s, f k b ≤ f i a + ∑ b in s, f j b,
  { intros i j,
    obtain ⟨k, hk⟩ := h (insert a s) i j,
    exact ⟨k, add_le_add (hk a (finset.mem_insert_self _ _)).left $ finset.sum_le_sum $
      λ a ha, (hk _ $ finset.mem_insert_of_mem ha).right⟩ },
  simp [ha, ih.symm, infi_add_infi this]
end

/-- If `x ≠ 0` and `x ≠ ∞`, then right multiplication by `x` maps infimum to infimum.
See also `ennreal.infi_mul` that assumes `[nonempty ι]` but does not require `x ≠ 0`. -/
lemma infi_mul_of_ne {ι} {f : ι → ℝ≥0∞} {x : ℝ≥0∞} (h0 : x ≠ 0) (h : x ≠ ∞) :
  infi f * x = ⨅ i, f i * x :=
le_antisymm
  mul_right_mono.map_infi_le
  ((ennreal.div_le_iff_le_mul (or.inl h0) $ or.inl h).mp $ le_infi $
    λ i, (ennreal.div_le_iff_le_mul (or.inl h0) $ or.inl h).mpr $ infi_le _ _)

/-- If `x ≠ ∞`, then right multiplication by `x` maps infimum over a nonempty type to infimum. See
also `ennreal.infi_mul_of_ne` that assumes `x ≠ 0` but does not require `[nonempty ι]`. -/
lemma infi_mul {ι} [nonempty ι] {f : ι → ℝ≥0∞} {x : ℝ≥0∞} (h : x ≠ ∞) :
  infi f * x = ⨅ i, f i * x :=
begin
  by_cases h0 : x = 0,
  { simp only [h0, mul_zero, infi_const] },
  { exact infi_mul_of_ne h0 h }
end

/-- If `x ≠ ∞`, then left multiplication by `x` maps infimum over a nonempty type to infimum. See
also `ennreal.mul_infi_of_ne` that assumes `x ≠ 0` but does not require `[nonempty ι]`. -/
lemma mul_infi {ι} [nonempty ι] {f : ι → ℝ≥0∞} {x : ℝ≥0∞} (h : x ≠ ∞) :
  x * infi f = ⨅ i, x * f i :=
by simpa only [mul_comm] using infi_mul h

/-- If `x ≠ 0` and `x ≠ ∞`, then left multiplication by `x` maps infimum to infimum.
See also `ennreal.mul_infi` that assumes `[nonempty ι]` but does not require `x ≠ 0`. -/
lemma mul_infi_of_ne {ι} {f : ι → ℝ≥0∞} {x : ℝ≥0∞} (h0 : x ≠ 0) (h : x ≠ ∞) :
  x * infi f = ⨅ i, x * f i :=
by simpa only [mul_comm] using infi_mul_of_ne h0 h

/-! `supr_mul`, `mul_supr` and variants are in `topology.instances.ennreal`. -/

end infi

section supr

@[simp] lemma supr_eq_zero {ι : Sort*} {f : ι → ℝ≥0∞} : (⨆ i, f i) = 0 ↔ ∀ i, f i = 0 :=
supr_eq_bot

@[simp] lemma supr_zero_eq_zero {ι : Sort*} : (⨆ i : ι, (0 : ℝ≥0∞)) = 0 :=
by simp

lemma sup_eq_zero {a b : ℝ≥0∞} : a ⊔ b = 0 ↔ a = 0 ∧ b = 0 := sup_eq_bot_iff

lemma supr_coe_nat : (⨆n:ℕ, (n : ℝ≥0∞)) = ∞ :=
(supr_eq_top _).2 $ assume b hb, ennreal.exists_nat_gt (lt_top_iff_ne_top.1 hb)

end supr

end ennreal

namespace set
namespace ord_connected

variables {s : set ℝ} {t : set ℝ≥0} {u : set ℝ≥0∞}

lemma preimage_coe_nnreal_ennreal (h : u.ord_connected) : (coe ⁻¹' u : set ℝ≥0).ord_connected :=
h.preimage_mono ennreal.coe_mono

lemma image_coe_nnreal_ennreal (h : t.ord_connected) : (coe '' t : set ℝ≥0∞).ord_connected :=
begin
  refine ⟨ball_image_iff.2 $ λ x hx, ball_image_iff.2 $ λ y hy z hz, _⟩,
  rcases ennreal.le_coe_iff.1 hz.2 with ⟨z, rfl, hzy⟩,
  exact mem_image_of_mem _ (h.out hx hy ⟨ennreal.coe_le_coe.1 hz.1, ennreal.coe_le_coe.1 hz.2⟩)
end

lemma preimage_ennreal_of_real (h : u.ord_connected) : (ennreal.of_real ⁻¹' u).ord_connected :=
h.preimage_coe_nnreal_ennreal.preimage_real_to_nnreal

lemma image_ennreal_of_real (h : s.ord_connected) : (ennreal.of_real '' s).ord_connected :=
by simpa only [image_image] using h.image_real_to_nnreal.image_coe_nnreal_ennreal

end ord_connected
end set

namespace tactic
open positivity

private lemma nnreal_coe_pos {r : ℝ≥0} : 0 < r → 0 < (r : ℝ≥0∞) := ennreal.coe_pos.2

/-- Extension for the `positivity` tactic: cast from `ℝ≥0` to `ℝ≥0∞`. -/
@[positivity]
meta def positivity_coe_nnreal_ennreal : expr → tactic strictness
| `(@coe _ _ %%inst %%a) := do
  unify inst `(@coe_to_lift _ _ $ @coe_base _ _ ennreal.has_coe),
  positive p ← core a, -- We already know `0 ≤ r` for all `r : ℝ≥0∞`
  positive <$> mk_app ``nnreal_coe_pos [p]
| e := pp e >>= fail ∘ format.bracket "The expression "
         " is not of the form `(r : ℝ≥0∞)` for `r : ℝ≥0`"

private lemma ennreal_of_real_pos {r : ℝ} : 0 < r → 0 < ennreal.of_real r := ennreal.of_real_pos.2

/-- Extension for the `positivity` tactic: `ennreal.of_real` is positive if its input is. -/
@[positivity]
meta def positivity_ennreal_of_real : expr → tactic strictness
| `(ennreal.of_real %%r) := do
    positive p ← core r,
    positive <$> mk_app ``ennreal_of_real_pos [p]
-- This case is handled by `tactic.positivity_canon`
| e := pp e >>= fail ∘ format.bracket "The expression `" "` is not of the form `ennreal.of_real r`"

end tactic
