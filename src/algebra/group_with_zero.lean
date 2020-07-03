/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import tactic.alias
import tactic.push_neg
import tactic.localized
import logic.unique
import algebra.group.commute
import algebra.group.units_hom

/-!
# Groups with an adjoined zero element

This file describes structures that are not usually studied on their own right in mathematics,
namely a special sort of monoid: apart from a distinguished “zero element” they form a group,
or in other words, they are groups with an adjoined zero element.

Examples are:

* division rings;
* the value monoid of a multiplicative valuation;
* in particular, the non-negative real numbers.

## Main definitions

* `group_with_zero`
* `comm_group_with_zero`

## Implementation details

As is usual in mathlib, we extend the inverse function to the zero element,
and require `0⁻¹ = 0`.

-/

set_option old_structure_cmd true
open_locale classical

variables {M₀ G₀ : Type*}

mk_simp_attribute field_simps "The simpset `field_simps` is used by the tactic `field_simp` to
reduce an expression in a field to an expression of the form `n / d` where `n` and `d` are
division-free."

section
set_option default_priority 100 -- see Note [default priority]

/-- Typeclass for expressing that a type `M₀` with multiplication and a zero satisfies
`0 * a = 0` and `a * 0 = 0` for all `a : M₀`. -/
@[protect_proj, ancestor has_mul has_zero]
class mul_zero_class (M₀ : Type*) extends has_mul M₀, has_zero M₀ :=
(zero_mul : ∀ a : M₀, 0 * a = 0)
(mul_zero : ∀ a : M₀, a * 0 = 0)

section mul_zero_class

variables [mul_zero_class M₀] {a b : M₀}

@[ematch, simp] lemma zero_mul (a : M₀) : 0 * a = 0 :=
mul_zero_class.zero_mul a

@[ematch, simp] lemma mul_zero (a : M₀) : a * 0 = 0 :=
mul_zero_class.mul_zero a

lemma mul_eq_zero_of_left (h : a = 0) (b : M₀) : a * b = 0 := h.symm ▸ zero_mul b

lemma mul_eq_zero_of_right (a : M₀) (h : b = 0) : a * b = 0 := h.symm ▸ mul_zero a

lemma left_ne_zero_of_mul : a * b ≠ 0 → a ≠ 0 := mt (λ h, mul_eq_zero_of_left h b)

lemma right_ne_zero_of_mul : a * b ≠ 0 → b ≠ 0 := mt (mul_eq_zero_of_right a)

lemma ne_zero_and_ne_zero_of_mul (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 :=
⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩

end mul_zero_class

/-- Predicate typeclass for expressing that a (semi)ring or similar algebraic structure
is nonzero. -/
@[protect_proj] class nonzero (M₀ : Type*) [has_zero M₀] [has_one M₀] : Prop :=
(zero_ne_one : 0 ≠ (1:M₀))

section

variables [has_zero M₀] [has_one M₀] [nonzero M₀]

@[simp] lemma zero_ne_one : 0 ≠ (1:M₀) := nonzero.zero_ne_one

@[simp] lemma one_ne_zero : (1:M₀) ≠ 0 := zero_ne_one.symm

lemma ne_zero_of_eq_one {a : M₀} (h : a = 1) : a ≠ 0 :=
calc a = 1 : h
   ... ≠ 0 : one_ne_zero

end

section

variables [mul_zero_class M₀] [has_one M₀] [nonzero M₀] {a b : M₀}

lemma left_ne_zero_of_mul_eq_one (h : a * b = 1) : a ≠ 0 :=
left_ne_zero_of_mul $ ne_zero_of_eq_one h

lemma right_ne_zero_of_mul_eq_one (h : a * b = 1) : b ≠ 0 :=
right_ne_zero_of_mul $ ne_zero_of_eq_one h

end

/-- Predicate typeclass for expressing that `a * b = 0` implies `a = 0` or `b = 0`
for all `a` and `b` of type `G₀`. -/
class no_zero_divisors (M₀ : Type*) [has_mul M₀] [has_zero M₀] : Prop :=
(eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {a b : M₀}, a * b = 0 → a = 0 ∨ b = 0)

export no_zero_divisors (eq_zero_or_eq_zero_of_mul_eq_zero)

lemma eq_zero_of_mul_self_eq_zero [has_mul M₀] [has_zero M₀] [no_zero_divisors M₀]
  {a : M₀} (h : a * a = 0) :
  a = 0 :=
(eq_zero_or_eq_zero_of_mul_eq_zero h).elim id id

section

variables [mul_zero_class M₀] [no_zero_divisors M₀] {a b : M₀}

/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp] theorem mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0 :=
⟨eq_zero_or_eq_zero_of_mul_eq_zero,
  λo, o.elim (λ h, mul_eq_zero_of_left h b) (mul_eq_zero_of_right a)⟩

/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp] theorem zero_eq_mul : 0 = a * b ↔ a = 0 ∨ b = 0 :=
by rw [eq_comm, mul_eq_zero]

/-- If `α` has no zero divisors, then the product of two elements is nonzero iff both of them
are nonzero. -/
theorem mul_ne_zero_iff : a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 :=
(not_congr mul_eq_zero).trans not_or_distrib

theorem mul_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
mul_ne_zero_iff.2 ⟨ha, hb⟩

/-- If `α` has no zero divisors, then for elements `a, b : α`, `a * b` equals zero iff so is
`b * a`. -/
theorem mul_eq_zero_comm : a * b = 0 ↔ b * a = 0 :=
mul_eq_zero.trans $ (or_comm _ _).trans mul_eq_zero.symm

/-- If `α` has no zero divisors, then for elements `a, b : α`, `a * b` is nonzero iff so is
`b * a`. -/
theorem mul_ne_zero_comm : a * b ≠ 0 ↔ b * a ≠ 0 :=
not_congr mul_eq_zero_comm

lemma mul_self_eq_zero : a * a = 0 ↔ a = 0 := by simp
lemma zero_eq_mul_self : 0 = a * a ↔ a = 0 := by simp

end

end -- default_priority 100

section prio
set_option default_priority 10 -- see Note [default priority]

/-- A type `M` is a “monoid with zero” if it is a monoid with zero element, and `0` is left
and right absorbing. -/
@[protect_proj] class monoid_with_zero (M₀ : Type*) extends monoid M₀, mul_zero_class M₀.

/-- A type `M` is a `cancel_monoid_with_zero` if it is a monoid with zero element, `0` is left
and right absorbing, and left/right multiplication by a non-zero element is injective. -/
@[protect_proj] class cancel_monoid_with_zero (M₀ : Type*) extends monoid_with_zero M₀ :=
(mul_left_cancel_of_ne_zero : ∀ {a b c : M₀}, a ≠ 0 → a * b = a * c → b = c)
(mul_right_cancel_of_ne_zero : ∀ {a b c : M₀}, b ≠ 0 → a * b = c * b → a = c)

/-- A type `M` is a commutative “monoid with zero” if it is a commutative monoid with zero
element, and `0` is left and right absorbing. -/
@[protect_proj]
class comm_monoid_with_zero (M₀ : Type*) extends comm_monoid M₀, monoid_with_zero M₀.

/-- A type `G₀` is a “group with zero” if it is a monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`.

Examples include division rings and the ordered monoids that are the
target of valuations in general valuation theory.-/
class group_with_zero (G₀ : Type*) extends monoid_with_zero G₀, has_inv G₀ :=
(inv_zero : (0 : G₀)⁻¹ = 0)
(mul_inv_cancel : ∀ a:G₀, a ≠ 0 → a * a⁻¹ = 1)
(zero_ne_one : (0 : G₀) ≠ 1)

instance group_with_zero.to_nonzero (G₀ : Type*) [group_with_zero G₀] : nonzero G₀ :=
⟨group_with_zero.zero_ne_one⟩

/-- A type `G₀` is a commutative “group with zero”
if it is a commutative monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`. -/
class comm_group_with_zero (G₀ : Type*) extends comm_monoid_with_zero G₀, group_with_zero G₀.

/-- The division operation on a group with zero element. -/
instance group_with_zero.has_div {G₀ : Type*} [group_with_zero G₀] :
  has_div G₀ := ⟨λ g h, g * h⁻¹⟩

end prio

section monoid_with_zero

variables [monoid_with_zero M₀]

namespace units

@[simp] lemma ne_zero [nonzero M₀] (u : units M₀) :
  (u : M₀) ≠ 0 :=
left_ne_zero_of_mul_eq_one u.mul_inv

-- We can't use `mul_eq_zero` + `units.ne_zero` in the next two lemmas because we don't assume
-- `nonzero M₀`.

@[simp] lemma mul_left_eq_zero (u : units M₀) {a : M₀} : a * u = 0 ↔ a = 0 :=
⟨λ h, by simpa using mul_eq_zero_of_left h ↑u⁻¹, λ h, mul_eq_zero_of_left h u⟩

@[simp] lemma mul_right_eq_zero (u : units M₀) {a : M₀} : ↑u * a = 0 ↔ a = 0 :=
⟨λ h, by simpa using mul_eq_zero_of_right ↑u⁻¹ h, mul_eq_zero_of_right u⟩

end units

namespace is_unit

lemma ne_zero [nonzero M₀] {a : M₀} (ha : is_unit a) : a ≠ 0 := let ⟨u, hu⟩ := ha in hu ▸ u.ne_zero

lemma mul_right_eq_zero {a b : M₀} (ha : is_unit a) : a * b = 0 ↔ b = 0 :=
let ⟨u, hu⟩ := ha in hu ▸ u.mul_right_eq_zero

lemma mul_left_eq_zero {a b : M₀} (hb : is_unit b) : a * b = 0 ↔ a = 0 :=
let ⟨u, hu⟩ := hb in hu ▸ u.mul_left_eq_zero

end is_unit

/-- In a monoid with zero, if zero equals one, then zero is the only element. -/
lemma eq_zero_of_zero_eq_one (h : (0 : M₀) = 1) (a : M₀) : a = 0 :=
by rw [← mul_one a, ← h, mul_zero]

/-- In a monoid with zero, if zero equals one, then zero is the unique element. -/
def unique_of_zero_eq_one (h : (0 : M₀) = 1) : unique M₀ :=
{ default := 0, uniq := eq_zero_of_zero_eq_one h }

/-- In a monoid with zero, if zero equals one, then all elements of that semiring are equal. -/
theorem subsingleton_of_zero_eq_one (h : (0 : M₀) = 1) : subsingleton M₀ :=
@unique.subsingleton _ (unique_of_zero_eq_one h)

lemma eq_of_zero_eq_one (h : (0 : M₀) = 1) (a b : M₀) : a = b :=
@subsingleton.elim _ (subsingleton_of_zero_eq_one h) a b

@[simp] theorem is_unit_zero_iff : is_unit (0 : M₀) ↔ (0:M₀) = 1 :=
⟨λ ⟨⟨_, a, (a0 : 0 * a = 1), _⟩, rfl⟩, by rwa zero_mul at a0,
 λ h, ⟨⟨0, 0, eq_of_zero_eq_one h _ _, eq_of_zero_eq_one h _ _⟩, rfl⟩⟩

@[simp] theorem not_is_unit_zero [nonzero M₀] : ¬ is_unit (0 : M₀) :=
mt is_unit_zero_iff.1 zero_ne_one

variable (M₀)

/-- A monoid with zero is either nonzero, or has a unique element. -/
noncomputable def nonzero_psum_unique : psum (nonzero M₀) (unique M₀) :=
if h : (0:M₀) = 1 then psum.inr (unique_of_zero_eq_one h) else psum.inl ⟨h⟩

/-- In a monoid with zero, either zero and one are nonequal, or zero is the only element. -/
lemma zero_ne_one_or_forall_eq_0 : (0 : M₀) ≠ 1 ∨ (∀a:M₀, a = 0) :=
not_or_of_imp eq_zero_of_zero_eq_one

end monoid_with_zero

section cancel_monoid_with_zero

variables [cancel_monoid_with_zero M₀] {a b c : M₀}

lemma mul_left_cancel' (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
cancel_monoid_with_zero.mul_left_cancel_of_ne_zero ha h

lemma mul_right_cancel' (hb : b ≠ 0) (h : a * b = c * b) : a = c :=
cancel_monoid_with_zero.mul_right_cancel_of_ne_zero hb h

lemma mul_left_inj' (hc : c ≠ 0) : a * c = b * c ↔ a = b := ⟨mul_right_cancel' hc, λ h, h ▸ rfl⟩

lemma mul_right_inj' (ha : a ≠ 0) : a * b = a * c ↔ b = c := ⟨mul_left_cancel' ha, λ h, h ▸ rfl⟩

/-- An element of a `cancel_monoid_with_zero` fixed by right multiplication by an element other
than one must be zero. -/
theorem eq_zero_of_mul_eq_self_right (h₁ : b ≠ 1) (h₂ : a * b = a) : a = 0 :=
classical.by_contradiction $ λ ha, h₁ $ mul_left_cancel' ha $ h₂.symm ▸ (mul_one a).symm

/-- An element of a `cancel_monoid_with_zero` fixed by left multiplication by an element other
than one must be zero. -/
theorem eq_zero_of_mul_eq_self_left (h₁ : b ≠ 1) (h₂ : b * a = a) : a = 0 :=
classical.by_contradiction $ λ ha, h₁ $ mul_right_cancel' ha $ h₂.symm ▸ (one_mul a).symm

end cancel_monoid_with_zero

section group_with_zero
variables [group_with_zero G₀]

lemma div_eq_mul_inv {a b : G₀} : a / b = a * b⁻¹ := rfl

alias div_eq_mul_inv ← division_def

@[simp] lemma inv_zero : (0 : G₀)⁻¹ = 0 :=
group_with_zero.inv_zero

@[simp] lemma mul_inv_cancel {a : G₀} (h : a ≠ 0) : a * a⁻¹ = 1 :=
group_with_zero.mul_inv_cancel a h

@[simp] lemma mul_inv_cancel_left' (a : G₀) {b : G₀} (h : b ≠ 0) :
  (a * b) * b⁻¹ = a :=
calc (a * b) * b⁻¹ = a * (b * b⁻¹) : mul_assoc _ _ _
               ... = a             : by simp [h]

@[simp] lemma mul_inv_cancel_right' {a : G₀} (h : a ≠ 0) (b : G₀) :
  a * (a⁻¹ * b) = b :=
calc a * (a⁻¹ * b) = (a * a⁻¹) * b : (mul_assoc _ _ _).symm
               ... = b             : by simp [h]

lemma inv_ne_zero {a : G₀} (h : a ≠ 0) : a⁻¹ ≠ 0 :=
assume a_eq_0, by simpa [a_eq_0] using mul_inv_cancel h

@[simp] lemma inv_mul_cancel {a : G₀} (h : a ≠ 0) : a⁻¹ * a = 1 :=
calc a⁻¹ * a = (a⁻¹ * a) * a⁻¹ * a⁻¹⁻¹ : by simp [inv_ne_zero h]
         ... = a⁻¹ * a⁻¹⁻¹             : by simp [h]
         ... = 1                       : by simp [inv_ne_zero h]

@[simp] lemma inv_mul_cancel_left' (a : G₀) {b : G₀} (h : b ≠ 0) :
  (a * b⁻¹) * b = a :=
calc (a * b⁻¹) * b = a * (b⁻¹ * b) : mul_assoc _ _ _
               ... = a             : by simp [h]

@[simp] lemma inv_mul_cancel_right' {a : G₀} (h : a ≠ 0) (b : G₀) :
  a⁻¹ * (a * b) = b :=
calc a⁻¹ * (a * b) = (a⁻¹ * a) * b : (mul_assoc _ _ _).symm
               ... = b             : by simp [h]

@[simp] lemma inv_one : 1⁻¹ = (1:G₀) :=
calc 1⁻¹ = 1 * 1⁻¹ : by rw [one_mul]
     ... = (1:G₀)  : by simp

@[simp] lemma inv_inv' (a : G₀) : a⁻¹⁻¹ = a :=
begin
  classical,
  by_cases h : a = 0, { simp [h] },
  calc a⁻¹⁻¹ = a * (a⁻¹ * a⁻¹⁻¹) : by simp [h]
         ... = a                 : by simp [inv_ne_zero h]
end

/-- Multiplying `a` by itself and then by its inverse results in `a`
(whether or not `a` is zero). -/
@[simp] lemma mul_self_mul_inv (a : G₀) : a * a * a⁻¹ = a :=
begin
  classical,
  by_cases h : a = 0,
  { rw [h, inv_zero, mul_zero] },
  { rw [mul_assoc, mul_inv_cancel h, mul_one] }
end

/-- Multiplying `a` by its inverse and then by itself results in `a`
(whether or not `a` is zero). -/
@[simp] lemma mul_inv_mul_self (a : G₀) : a * a⁻¹ * a = a :=
begin
  classical,
  by_cases h : a = 0,
  { rw [h, inv_zero, mul_zero] },
  { rw [mul_inv_cancel h, one_mul] }
end

/-- Multiplying `a⁻¹` by `a` twice results in `a` (whether or not `a`
is zero). -/
@[simp] lemma inv_mul_mul_self (a : G₀) : a⁻¹ * a * a = a :=
begin
  classical,
  by_cases h : a = 0,
  { rw [h, inv_zero, mul_zero] },
  { rw [inv_mul_cancel h, one_mul] }
end

/-- Multiplying `a` by itself and then dividing by itself results in
`a` (whether or not `a` is zero). -/
@[simp] lemma mul_self_div_self (a : G₀) : a * a / a = a :=
mul_self_mul_inv a

/-- Dividing `a` by itself and then multiplying by itself results in
`a` (whether or not `a` is zero). -/
@[simp] lemma div_self_mul_self (a : G₀) : a / a * a = a :=
mul_inv_mul_self a

lemma inv_involutive' : function.involutive (has_inv.inv : G₀ → G₀) :=
inv_inv'

lemma eq_inv_of_mul_right_eq_one {a b : G₀} (h : a * b = 1) :
  b = a⁻¹ :=
calc b = a⁻¹ * (a * b) : (inv_mul_cancel_right' (left_ne_zero_of_mul_eq_one h) _).symm
   ... = a⁻¹ : by simp [h]

lemma eq_inv_of_mul_left_eq_one {a b : G₀} (h : a * b = 1) :
  a = b⁻¹ :=
calc a = (a * b) * b⁻¹ : (mul_inv_cancel_left' _ (right_ne_zero_of_mul_eq_one h)).symm
   ... = b⁻¹ : by simp [h]

lemma inv_injective' : function.injective (@has_inv.inv G₀ _) :=
inv_involutive'.injective

@[simp] lemma inv_inj' {g h : G₀} : g⁻¹ = h⁻¹ ↔ g = h := inv_injective'.eq_iff

lemma inv_eq_iff {g h : G₀} : g⁻¹ = h ↔ h⁻¹ = g :=
by rw [← inv_inj', eq_comm, inv_inv']

end group_with_zero

namespace units
variables [group_with_zero G₀]
variables {a b : G₀}

/-- Embed a non-zero element of a `group_with_zero` into the unit group.
  By combining this function with the operations on units,
  or the `/ₚ` operation, it is possible to write a division
  as a partial function with three arguments. -/
def mk0 (a : G₀) (ha : a ≠ 0) : units G₀ :=
⟨a, a⁻¹, mul_inv_cancel ha, inv_mul_cancel ha⟩

@[simp] lemma coe_mk0 {a : G₀} (h : a ≠ 0) : (mk0 a h : G₀) = a := rfl

@[simp] lemma mk0_coe (u : units G₀) (h : (u : G₀) ≠ 0) : mk0 (u : G₀) h = u :=
units.ext rfl

@[simp, norm_cast] lemma coe_inv' (u : units G₀) : ((u⁻¹ : units G₀) : G₀) = u⁻¹ :=
eq_inv_of_mul_left_eq_one u.inv_mul

@[simp] lemma mul_inv' (u : units G₀) : (u : G₀) * u⁻¹ = 1 := mul_inv_cancel u.ne_zero

@[simp] lemma inv_mul' (u : units G₀) : (u⁻¹ : G₀) * u = 1 := inv_mul_cancel u.ne_zero

@[simp] lemma mk0_inj {a b : G₀} (ha : a ≠ 0) (hb : b ≠ 0) :
  units.mk0 a ha = units.mk0 b hb ↔ a = b :=
⟨λ h, by injection h, λ h, units.ext h⟩

@[simp] lemma exists_iff_ne_zero {x : G₀} : (∃ u : units G₀, ↑u = x) ↔ x ≠ 0 :=
⟨λ ⟨u, hu⟩, hu ▸ u.ne_zero, assume hx, ⟨mk0 x hx, rfl⟩⟩

end units

section group_with_zero
variables [group_with_zero G₀]

lemma is_unit.mk0 (x : G₀) (hx : x ≠ 0) : is_unit x := is_unit_unit (units.mk0 x hx)

lemma is_unit_iff_ne_zero {x : G₀} : is_unit x ↔ x ≠ 0 :=
units.exists_iff_ne_zero

section prio
set_option default_priority 10 -- see Note [default priority]

instance group_with_zero.no_zero_divisors : no_zero_divisors G₀ :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ a b h,
    begin
      classical, contrapose! h,
      exact ((units.mk0 a h.1) * (units.mk0 b h.2)).ne_zero
    end,
  .. (‹_› : group_with_zero G₀) }

instance group_with_zero.cancel_monoid_with_zero : cancel_monoid_with_zero G₀ :=
{ mul_left_cancel_of_ne_zero := λ x y z hx h,
    by rw [← inv_mul_cancel_right' hx y, h, inv_mul_cancel_right' hx z],
  mul_right_cancel_of_ne_zero := λ x y z hy h,
    by rw [← mul_inv_cancel_left' x hy, h, mul_inv_cancel_left' z hy],
  .. (‹_› : group_with_zero G₀) }

end prio

lemma mul_inv_rev' (x y : G₀) : (x * y)⁻¹ = y⁻¹ * x⁻¹ :=
begin
  classical,
  by_cases hx : x = 0, { simp [hx] },
  by_cases hy : y = 0, { simp [hy] },
  symmetry,
  apply eq_inv_of_mul_left_eq_one,
  simp [mul_assoc, hx, hy]
end

@[simp] lemma div_self {a : G₀} (h : a ≠ 0) : a / a = 1 := mul_inv_cancel h

@[simp] lemma div_one (a : G₀) : a / 1 = a := by simp [div_eq_mul_inv]

lemma one_div (a : G₀) : 1 / a = a⁻¹ := one_mul _

@[simp] lemma zero_div (a : G₀) : 0 / a = 0 := zero_mul _

@[simp] lemma div_zero (a : G₀) : a / 0 = 0 :=
show a * 0⁻¹ = 0, by rw [inv_zero, mul_zero]

@[simp] lemma div_mul_cancel (a : G₀) {b : G₀} (h : b ≠ 0) : a / b * b = a :=
inv_mul_cancel_left' a h

lemma div_mul_cancel_of_imp {a b : G₀} (h : b = 0 → a = 0) : a / b * b = a :=
classical.by_cases (λ hb : b = 0, by simp [*]) (div_mul_cancel a)

@[simp] lemma mul_div_cancel (a : G₀) {b : G₀} (h : b ≠ 0) : a * b / b = a :=
mul_inv_cancel_left' a h

lemma mul_div_cancel_of_imp {a b : G₀} (h : b = 0 → a = 0) : a * b / b = a :=
classical.by_cases (λ hb : b = 0, by simp [*]) (mul_div_cancel a)

lemma mul_div_assoc {a b c : G₀} : a * b / c = a * (b / c) :=
mul_assoc _ _ _

local attribute [simp] div_eq_mul_inv mul_comm mul_assoc mul_left_comm

lemma div_eq_mul_one_div (a b : G₀) : a / b = a * (1 / b) :=
by simp

lemma mul_one_div_cancel {a : G₀} (h : a ≠ 0) : a * (1 / a) = 1 :=
by simp [h]

lemma one_div_mul_cancel {a : G₀} (h : a ≠ 0) : (1 / a) * a = 1 :=
by simp [h]

lemma one_div_one : 1 / 1 = (1:G₀) :=
div_self (ne.symm zero_ne_one)

lemma one_div_ne_zero {a : G₀} (h : a ≠ 0) : 1 / a ≠ 0 :=
by simpa only [one_div] using inv_ne_zero h

lemma eq_one_div_of_mul_eq_one {a b : G₀} (h : a * b = 1) : b = 1 / a :=
by simpa only [one_div] using eq_inv_of_mul_right_eq_one h

lemma eq_one_div_of_mul_eq_one_left {a b : G₀} (h : b * a = 1) : b = 1 / a :=
by simpa only [one_div] using eq_inv_of_mul_left_eq_one h

@[simp] lemma one_div_div (a b : G₀) : 1 / (a / b) = b / a :=
by rw [one_div, div_eq_mul_inv, mul_inv_rev', inv_inv', div_eq_mul_inv]

@[simp] lemma one_div_one_div (a : G₀) : 1 / (1 / a) = a :=
by simp

lemma eq_of_one_div_eq_one_div {a b : G₀} (h : 1 / a = 1 / b) : a = b :=
by rw [← one_div_one_div a, h, one_div_one_div]

variables {a b c : G₀}

@[simp] lemma inv_eq_zero {a : G₀} : a⁻¹ = 0 ↔ a = 0 :=
by rw [inv_eq_iff, inv_zero, eq_comm]

lemma one_div_mul_one_div_rev (a b : G₀) : (1 / a) * (1 / b) =  1 / (b * a) :=
by simp only [div_eq_mul_inv, one_mul, mul_inv_rev']

theorem divp_eq_div (a : G₀) (u : units G₀) : a /ₚ u = a / u :=
congr_arg _ $ u.coe_inv'

@[simp] theorem divp_mk0 (a : G₀) {b : G₀} (hb : b ≠ 0) :
  a /ₚ units.mk0 b hb = a / b :=
divp_eq_div _ _

lemma inv_div : (a / b)⁻¹ = b / a :=
(mul_inv_rev' _ _).trans (by rw inv_inv'; refl)

lemma inv_div_left : a⁻¹ / b = (b * a)⁻¹ :=
(mul_inv_rev' _ _).symm

lemma div_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a / b ≠ 0 :=
mul_ne_zero ha (inv_ne_zero hb)

@[simp] lemma div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = 0:=
by simp [div_eq_mul_inv]

lemma div_ne_zero_iff : a / b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 :=
(not_congr div_eq_zero_iff).trans not_or_distrib

lemma div_left_inj' (hc : c ≠ 0) : a / c = b / c ↔ a = b :=
by rw [← divp_mk0 _ hc, ← divp_mk0 _ hc, divp_left_inj]

lemma div_eq_iff_mul_eq (hb : b ≠ 0) : a / b = c ↔ c * b = a :=
⟨λ h, by rw [← h, div_mul_cancel _ hb],
 λ h, by rw [← h, mul_div_cancel _ hb]⟩

lemma eq_div_iff_mul_eq (hc : c ≠ 0) : a = b / c ↔ a * c = b :=
by rw [eq_comm, div_eq_iff_mul_eq hc]

lemma div_eq_of_eq_mul {x : G₀} (hx : x ≠ 0) {y z : G₀} (h : y = z * x) : y / x = z :=
(div_eq_iff_mul_eq hx).2 h.symm

lemma eq_div_of_mul_eq {x : G₀} (hx : x ≠ 0) {y z : G₀} (h : z * x = y) : z = y / x :=
eq.symm $ div_eq_of_eq_mul hx h.symm

lemma eq_of_div_eq_one (h : a / b = 1) : a = b :=
begin
  classical,
  by_cases hb : b = 0,
  { rw [hb, div_zero] at h,
    exact eq_of_zero_eq_one h a b },
  { rwa [div_eq_iff_mul_eq hb, one_mul, eq_comm] at h }
end

lemma div_eq_one_iff_eq (hb : b ≠ 0) : a / b = 1 ↔ a = b :=
⟨eq_of_div_eq_one, λ h, h.symm ▸ div_self hb⟩

lemma div_mul_left {a b : G₀} (hb : b ≠ 0) : b / (a * b) = 1 / a :=
by simp only [div_eq_mul_inv, mul_inv_rev', mul_inv_cancel_right' hb, one_mul]

lemma mul_div_mul_right (a b : G₀) {c : G₀} (hc : c ≠ 0) :
  (a * c) / (b * c) = a / b :=
by simp only [div_eq_mul_inv, mul_inv_rev', mul_assoc, mul_inv_cancel_right' hc]

lemma mul_mul_div (a : G₀) {b : G₀} (hb : b ≠ 0) : a = a * b * (1 / b) :=
by simp [hb]

end group_with_zero

section comm_group_with_zero -- comm
variables [comm_group_with_zero G₀] {a b c : G₀}

lemma mul_inv' : (a * b)⁻¹ = a⁻¹ * b⁻¹ :=
by rw [mul_inv_rev', mul_comm]

lemma one_div_mul_one_div (a b : G₀) : (1 / a) * (1 / b) = 1 / (a * b) :=
by rw [one_div_mul_one_div_rev, mul_comm b]

lemma div_mul_right {a : G₀} (b : G₀) (ha : a ≠ 0) : a / (a * b) = 1 / b :=
by rw [mul_comm, div_mul_left ha]

lemma mul_div_cancel_left_of_imp {a b : G₀} (h : a = 0 → b = 0) : a * b / a = b :=
by rw [mul_comm, mul_div_cancel_of_imp h]

lemma mul_div_cancel_left {a : G₀} (b : G₀) (ha : a ≠ 0) : a * b / a = b :=
mul_div_cancel_left_of_imp $ λ h, (ha h).elim

lemma mul_div_cancel_of_imp' {a b : G₀} (h : b = 0 → a = 0) : b * (a / b) = a :=
by rw [mul_comm, div_mul_cancel_of_imp h]

lemma mul_div_cancel' (a : G₀) {b : G₀} (hb : b ≠ 0) : b * (a / b) = a :=
by rw [mul_comm, (div_mul_cancel _ hb)]

local attribute [simp] mul_assoc mul_comm mul_left_comm

lemma div_mul_div (a b c d : G₀) :
      (a / b) * (c / d) = (a * c) / (b * d) :=
by { simp [div_eq_mul_inv], rw [mul_inv_rev', mul_comm d⁻¹] }

lemma mul_div_mul_left (a b : G₀) {c : G₀} (hc : c ≠ 0) :
      (c * a) / (c * b) = a / b :=
by rw [mul_comm c, mul_comm c, mul_div_mul_right _ _ hc]

@[field_simps] lemma div_mul_eq_mul_div (a b c : G₀) : (b / c) * a = (b * a) / c :=
by simp [div_eq_mul_inv]

lemma div_mul_eq_mul_div_comm (a b c : G₀) :
      (b / c) * a = b * (a / c) :=
by rw [div_mul_eq_mul_div, ← one_mul c, ← div_mul_div, div_one, one_mul]

lemma mul_eq_mul_of_div_eq_div (a : G₀) {b : G₀} (c : G₀) {d : G₀} (hb : b ≠ 0)
      (hd : d ≠ 0) (h : a / b = c / d) : a * d = c * b :=
by rw [← mul_one (a*d), mul_assoc, mul_comm d, ← mul_assoc, ← div_self hb,
       ← div_mul_eq_mul_div_comm, h, div_mul_eq_mul_div, div_mul_cancel _ hd]

@[field_simps] lemma div_div_eq_mul_div (a b c : G₀) :
      a / (b / c) = (a * c) / b :=
by rw [div_eq_mul_one_div, one_div_div, ← mul_div_assoc]

@[field_simps] lemma div_div_eq_div_mul (a b c : G₀) :
      (a / b) / c = a / (b * c) :=
by rw [div_eq_mul_one_div, div_mul_div, mul_one]

lemma div_div_div_div_eq (a : G₀) {b c d : G₀} :
      (a / b) / (c / d) = (a * d) / (b * c) :=
by rw [div_div_eq_mul_div, div_mul_eq_mul_div, div_div_eq_div_mul]

lemma div_mul_eq_div_mul_one_div (a b c : G₀) :
      a / (b * c) = (a / b) * (1 / c) :=
by rw [← div_div_eq_div_mul, ← div_eq_mul_one_div]

/-- Dividing `a` by the result of dividing `a` by itself results in
`a` (whether or not `a` is zero). -/
@[simp] lemma div_div_self (a : G₀) : a / (a / a) = a :=
begin
  rw div_div_eq_mul_div,
  exact mul_self_div_self a
end

lemma ne_zero_of_one_div_ne_zero {a : G₀} (h : 1 / a ≠ 0) : a ≠ 0 :=
assume ha : a = 0, begin rw [ha, div_zero] at h, contradiction end

lemma eq_zero_of_one_div_eq_zero {a : G₀} (h : 1 / a = 0) : a = 0 :=
classical.by_cases
  (assume ha, ha)
  (assume ha, ((one_div_ne_zero ha) h).elim)

lemma div_helper {a : G₀} (b : G₀) (h : a ≠ 0) : (1 / (a * b)) * a = 1 / b :=
by rw [div_mul_eq_mul_div, one_mul, div_mul_right _ h]

end comm_group_with_zero

section comm_group_with_zero
variables [comm_group_with_zero G₀] {a b c d : G₀}

lemma div_eq_inv_mul : a / b = b⁻¹ * a := mul_comm _ _

lemma mul_div_right_comm (a b c : G₀) : (a * b) / c = (a / c) * b :=
by rw [div_eq_mul_inv, mul_assoc, mul_comm b, ← mul_assoc]; refl

lemma mul_comm_div' (a b c : G₀) : (a / b) * c = a * (c / b) :=
by rw [← mul_div_assoc, mul_div_right_comm]

lemma div_mul_comm' (a b c : G₀) : (a / b) * c = (c / b) * a :=
by rw [div_mul_eq_mul_div, mul_comm, mul_div_right_comm]

lemma mul_div_comm (a b c : G₀) : a * (b / c) = b * (a / c) :=
by rw [← mul_div_assoc, mul_comm, mul_div_assoc]

lemma div_right_comm (a : G₀) : (a / b) / c = (a / c) / b :=
by rw [div_div_eq_div_mul, div_div_eq_div_mul, mul_comm]

lemma div_div_div_cancel_right (a : G₀) (hc : c ≠ 0) : (a / c) / (b / c) = a / b :=
by rw [div_div_eq_mul_div, div_mul_cancel _ hc]

lemma div_mul_div_cancel (a : G₀) (hc : c ≠ 0) : (a / c) * (c / b) = a / b :=
by rw [← mul_div_assoc, div_mul_cancel _ hc]

@[field_simps] lemma div_eq_div_iff (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = c * b :=
calc a / b = c / d ↔ a / b * (b * d) = c / d * (b * d) :
by rw [mul_left_inj' (mul_ne_zero hb hd)]
               ... ↔ a * d = c * b :
by rw [← mul_assoc, div_mul_cancel _ hb,
      ← mul_assoc, mul_right_comm, div_mul_cancel _ hd]

@[field_simps] lemma div_eq_iff (hb : b ≠ 0) : a / b = c ↔ a = c * b :=
by simpa using @div_eq_div_iff _ _ a b c 1 hb one_ne_zero

@[field_simps] lemma eq_div_iff (hb : b ≠ 0) : c = a / b ↔ c * b = a :=
by simpa using @div_eq_div_iff _ _ c 1 a b one_ne_zero hb

lemma div_div_cancel' (ha : a ≠ 0) : a / (a / b) = b :=
by rw [div_eq_mul_inv, inv_div, mul_div_cancel' _ ha]

end comm_group_with_zero

namespace semiconj_by

@[simp] lemma zero_right [mul_zero_class G₀] (a : G₀) : semiconj_by a 0 0 :=
by simp only [semiconj_by, mul_zero, zero_mul]

@[simp] lemma zero_left [mul_zero_class G₀] (x y : G₀) : semiconj_by 0 x y :=
by simp only [semiconj_by, mul_zero, zero_mul]

variables [group_with_zero G₀] {a x y x' y' : G₀}

@[simp] lemma inv_symm_left_iff' : semiconj_by a⁻¹ x y ↔ semiconj_by a y x :=
classical.by_cases
  (λ ha : a = 0, by simp only [ha, inv_zero, semiconj_by.zero_left])
  (λ ha, @units_inv_symm_left_iff _ _ (units.mk0 a ha) _ _)

lemma inv_symm_left' (h : semiconj_by a x y) : semiconj_by a⁻¹ y x :=
semiconj_by.inv_symm_left_iff'.2 h

lemma inv_right' (h : semiconj_by a x y) : semiconj_by a x⁻¹ y⁻¹ :=
begin
  classical,
  by_cases ha : a = 0,
  { simp only [ha, zero_left] },
  by_cases hx : x = 0,
  { subst x,
    simp only [semiconj_by, mul_zero, @eq_comm _ _ (y * a), mul_eq_zero] at h,
    simp [h.resolve_right ha] },
  { have := mul_ne_zero ha hx,
    rw [h.eq, mul_ne_zero_iff] at this,
    exact @units_inv_right _ _ _ (units.mk0 x hx) (units.mk0 y this.1) h },
end

@[simp] lemma inv_right_iff' : semiconj_by a x⁻¹ y⁻¹ ↔ semiconj_by a x y :=
⟨λ h, inv_inv' x ▸ inv_inv' y ▸ h.inv_right', inv_right'⟩

lemma div_right (h : semiconj_by a x y) (h' : semiconj_by a x' y') :
  semiconj_by a (x / x') (y / y') :=
h.mul_right h'.inv_right'

end semiconj_by

namespace commute

@[simp] theorem zero_right [mul_zero_class G₀] (a : G₀) :commute a 0 := semiconj_by.zero_right a
@[simp] theorem zero_left [mul_zero_class G₀] (a : G₀) : commute 0 a := semiconj_by.zero_left a a

variables [group_with_zero G₀] {a b c : G₀}

@[simp] theorem inv_left_iff' : commute a⁻¹ b ↔ commute a b :=
semiconj_by.inv_symm_left_iff'

theorem inv_left' (h : commute a b) : commute a⁻¹ b := inv_left_iff'.2 h

@[simp] theorem inv_right_iff' : commute a b⁻¹ ↔ commute a b :=
semiconj_by.inv_right_iff'

theorem inv_right' (h : commute a b) : commute a b⁻¹ := inv_right_iff'.2 h

theorem inv_inv' (h : commute a b) : commute a⁻¹ b⁻¹ := h.inv_left'.inv_right'

@[simp] theorem div_right (hab : commute a b) (hac : commute a c) :
  commute a (b / c) :=
hab.div_right hac

@[simp] theorem div_left (hac : commute a c) (hbc : commute b c) :
  commute (a / b) c :=
hac.mul_left hbc.inv_left'

end commute

namespace monoid_hom

variables {G₀' : Type*} [group_with_zero G₀] [group_with_zero G₀'] (f : G₀ →* G₀') (h0 : f 0 = 0)
  {a : G₀}

include h0

lemma map_ne_zero : f a ≠ 0 ↔ a ≠ 0 :=
⟨λ hfa ha, hfa $ ha.symm ▸ h0, λ ha, ((is_unit.mk0 a ha).map f).ne_zero⟩

lemma map_eq_zero : f a = 0 ↔ a = 0 :=
by { classical, exact not_iff_not.1 (f.map_ne_zero h0) }

variables (a) (b : G₀)

/-- A monoid homomorphism between groups with zeros sending `0` to `0` sends `a⁻¹` to `(f a)⁻¹`. -/
lemma map_inv' : f a⁻¹ = (f a)⁻¹ :=
begin
  classical, by_cases h : a = 0, by simp [h, h0],
  apply eq_inv_of_mul_left_eq_one,
  rw [← f.map_mul, inv_mul_cancel h, f.map_one]
end

lemma map_div : f (a / b) = f a / f b := (f.map_mul _ _).trans $ congr_arg _ $ f.map_inv' h0 b

end monoid_hom
