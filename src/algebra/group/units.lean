/-
Copyright (c) 2017 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johannes Hölzl, Chris Hughes, Jens Wagemaker, Jon Eugster
-/
import algebra.group.basic
import logic.unique
import tactic.nontriviality

/-!
# Units (i.e., invertible elements) of a monoid

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An element of a `monoid` is a unit if it has a two-sided inverse.

## Main declarations

* `units M`: the group of units (i.e., invertible elements) of a monoid.
* `is_unit x`: a predicate asserting that `x` is a unit (i.e., invertible element) of a monoid.

For both declarations, there is an additive counterpart: `add_units` and `is_add_unit`.

## Notation

We provide `Mˣ` as notation for `units M`,
resembling the notation $R^{\times}$ for the units of a ring, which is common in mathematics.

-/

open function

universe u
variable {α : Type u}

/-- Units of a `monoid`, bundled version. Notation: `αˣ`.

An element of a `monoid` is a unit if it has a two-sided inverse.
This version bundles the inverse element so that it can be computed.
For a predicate see `is_unit`. -/
structure units (α : Type u) [monoid α] :=
(val : α)
(inv : α)
(val_inv : val * inv = 1)
(inv_val : inv * val = 1)

postfix `ˣ`:1025 := units
-- We don't provide notation for the additive version, because its use is somewhat rare.

/-- Units of an `add_monoid`, bundled version.

An element of an `add_monoid` is a unit if it has a two-sided additive inverse.
This version bundles the inverse element so that it can be computed.
For a predicate see `is_add_unit`. -/
structure add_units (α : Type u) [add_monoid α] :=
(val : α)
(neg : α)
(val_neg : val + neg = 0)
(neg_val : neg + val = 0)

attribute [to_additive] units

section has_elem

@[to_additive] lemma unique_has_one {α : Type*} [unique α] [has_one α] :
  default = (1 : α) :=
unique.default_eq 1

end has_elem

namespace units

variables [monoid α]

@[to_additive] instance : has_coe αˣ α := ⟨val⟩

@[to_additive] instance : has_inv αˣ := ⟨λ u, ⟨u.2, u.1, u.4, u.3⟩⟩

/-- See Note [custom simps projection] -/
@[to_additive /-" See Note [custom simps projection] "-/]
def simps.coe (u : αˣ) : α := u

/-- See Note [custom simps projection] -/
@[to_additive /-" See Note [custom simps projection] "-/]
def simps.coe_inv (u : αˣ) : α := ↑(u⁻¹)

initialize_simps_projections units (val → coe as_prefix, inv → coe_inv as_prefix)
initialize_simps_projections add_units (val → coe as_prefix, neg → coe_neg as_prefix)

@[simp, to_additive] lemma coe_mk (a : α) (b h₁ h₂) : ↑(units.mk a b h₁ h₂) = a := rfl

@[ext, to_additive] theorem ext :
  function.injective (coe : αˣ → α)
| ⟨v, i₁, vi₁, iv₁⟩ ⟨v', i₂, vi₂, iv₂⟩ e :=
  by change v = v' at e; subst v'; congr;
      simpa only [iv₂, vi₁, one_mul, mul_one] using mul_assoc i₂ v i₁

@[norm_cast, to_additive] theorem eq_iff {a b : αˣ} :
  (a : α) = b ↔ a = b := ext.eq_iff

@[to_additive] theorem ext_iff {a b : αˣ} :
  a = b ↔ (a : α) = b := eq_iff.symm

@[to_additive] instance [decidable_eq α] : decidable_eq αˣ :=
λ a b, decidable_of_iff' _ ext_iff

@[simp, to_additive] theorem mk_coe (u : αˣ) (y h₁ h₂) :
  mk (u : α) y h₁ h₂ = u :=
ext rfl

/-- Copy a unit, adjusting definition equalities. -/
@[to_additive /-"Copy an `add_unit`, adjusting definitional equalities."-/, simps]
def copy (u : αˣ) (val : α) (hv : val = u) (inv : α) (hi : inv = ↑(u⁻¹)) : αˣ :=
{ val := val, inv := inv,
  inv_val := hv.symm ▸ hi.symm ▸ u.inv_val, val_inv := hv.symm ▸ hi.symm ▸ u.val_inv }

@[to_additive]
lemma copy_eq (u : αˣ) (val hv inv hi) :
  u.copy val hv inv hi = u :=
ext hv

@[to_additive] instance : mul_one_class αˣ :=
{ mul := λ u₁ u₂, ⟨u₁.val * u₂.val, u₂.inv * u₁.inv,
    by rw [mul_assoc, ←mul_assoc u₂.val, val_inv, one_mul, val_inv],
    by rw [mul_assoc, ←mul_assoc u₁.inv, inv_val, one_mul, inv_val]⟩,
  one := ⟨1, 1, one_mul 1, one_mul 1⟩,
  one_mul := λ u, ext $ one_mul u,
  mul_one := λ u, ext $ mul_one u }

/-- Units of a monoid form a group. -/
@[to_additive "Additive units of an additive monoid form an additive group."]
instance : group αˣ :=
{ mul := (*),
  one := 1,
  mul_assoc := λ u₁ u₂ u₃, ext $ mul_assoc u₁ u₂ u₃,
  inv := has_inv.inv,
  mul_left_inv := λ u, ext u.inv_val,
  ..units.mul_one_class }

@[to_additive] instance {α} [comm_monoid α] : comm_group αˣ :=
{ mul_comm := λ u₁ u₂, ext $ mul_comm _ _, ..units.group }

@[to_additive] instance : inhabited αˣ := ⟨1⟩

@[to_additive] instance [has_repr α] : has_repr αˣ := ⟨repr ∘ val⟩

variables (a b c : αˣ) {u : αˣ}

@[simp, norm_cast, to_additive] lemma coe_mul : (↑(a * b) : α) = a * b := rfl

@[simp, norm_cast, to_additive] lemma coe_one : ((1 : αˣ) : α) = 1 := rfl

@[simp, norm_cast, to_additive] lemma coe_eq_one {a : αˣ} : (a : α) = 1 ↔ a = 1 :=
by rw [←units.coe_one, eq_iff]

@[simp, to_additive] lemma inv_mk (x y : α) (h₁ h₂) : (mk x y h₁ h₂)⁻¹ = mk y x h₂ h₁ := rfl

@[simp, to_additive] lemma val_eq_coe : a.val = (↑a : α) := rfl

@[simp, to_additive] lemma inv_eq_coe_inv : a.inv = ((a⁻¹ : αˣ) : α) := rfl

@[simp, to_additive] lemma inv_mul : (↑a⁻¹ * a : α) = 1 := inv_val _
@[simp, to_additive] lemma mul_inv : (a * ↑a⁻¹ : α) = 1 := val_inv _

@[to_additive] lemma inv_mul_of_eq {a : α} (h : ↑u = a) : ↑u⁻¹ * a = 1 := by rw [←h, u.inv_mul]
@[to_additive] lemma mul_inv_of_eq {a : α} (h : ↑u = a) : a * ↑u⁻¹ = 1 := by rw [←h, u.mul_inv]

@[simp, to_additive] lemma mul_inv_cancel_left (a : αˣ) (b : α) : (a:α) * (↑a⁻¹ * b) = b :=
by rw [← mul_assoc, mul_inv, one_mul]

@[simp, to_additive] lemma inv_mul_cancel_left (a : αˣ) (b : α) : (↑a⁻¹:α) * (a * b) = b :=
by rw [← mul_assoc, inv_mul, one_mul]

@[simp, to_additive] lemma mul_inv_cancel_right (a : α) (b : αˣ) : a * b * ↑b⁻¹ = a :=
by rw [mul_assoc, mul_inv, mul_one]

@[simp, to_additive] lemma inv_mul_cancel_right (a : α) (b : αˣ) : a * ↑b⁻¹ * b = a :=
by rw [mul_assoc, inv_mul, mul_one]

@[simp, to_additive] theorem mul_right_inj (a : αˣ) {b c : α} : (a:α) * b = a * c ↔ b = c :=
⟨λ h, by simpa only [inv_mul_cancel_left] using congr_arg ((*) ↑(a⁻¹ : αˣ)) h, congr_arg _⟩

@[simp, to_additive] theorem mul_left_inj (a : αˣ) {b c : α} : b * a = c * a ↔ b = c :=
⟨λ h, by simpa only [mul_inv_cancel_right] using congr_arg (* ↑(a⁻¹ : αˣ)) h, congr_arg _⟩

@[to_additive] theorem eq_mul_inv_iff_mul_eq {a b : α} : a = b * ↑c⁻¹ ↔ a * c = b :=
⟨λ h, by rw [h, inv_mul_cancel_right], λ h, by rw [← h, mul_inv_cancel_right]⟩

@[to_additive] theorem eq_inv_mul_iff_mul_eq {a c : α} : a = ↑b⁻¹ * c ↔ ↑b * a = c :=
⟨λ h, by rw [h, mul_inv_cancel_left], λ h, by rw [← h, inv_mul_cancel_left]⟩

@[to_additive] theorem inv_mul_eq_iff_eq_mul {b c : α} : ↑a⁻¹ * b = c ↔ b = a * c :=
⟨λ h, by rw [← h, mul_inv_cancel_left], λ h, by rw [h, inv_mul_cancel_left]⟩

@[to_additive] theorem mul_inv_eq_iff_eq_mul {a c : α} : a * ↑b⁻¹ = c ↔ a = c * b :=
⟨λ h, by rw [← h, inv_mul_cancel_right], λ h, by rw [h, mul_inv_cancel_right]⟩

@[to_additive] protected lemma inv_eq_of_mul_eq_one_left {a : α} (h : a * u = 1) : ↑u⁻¹ = a :=
calc ↑u⁻¹ = 1 * ↑u⁻¹ : by rw one_mul
      ... = a : by rw [←h, mul_inv_cancel_right]

@[to_additive] protected lemma inv_eq_of_mul_eq_one_right {a : α} (h : ↑u * a = 1) : ↑u⁻¹ = a :=
calc ↑u⁻¹ = ↑u⁻¹ * 1 : by rw mul_one
      ... = a : by rw [←h, inv_mul_cancel_left]

@[to_additive] protected lemma eq_inv_of_mul_eq_one_left {a : α} (h : ↑u * a = 1) : a = ↑u⁻¹ :=
(units.inv_eq_of_mul_eq_one_right h).symm

@[to_additive] protected lemma eq_inv_of_mul_eq_one_right {a : α} (h : a * u = 1) : a = ↑u⁻¹ :=
(units.inv_eq_of_mul_eq_one_left h).symm

@[simp, to_additive] lemma mul_inv_eq_one {a : α} : a * ↑u⁻¹ = 1 ↔ a = u :=
⟨inv_inv u ▸ units.eq_inv_of_mul_eq_one_right, λ h, mul_inv_of_eq h.symm⟩

@[simp, to_additive] lemma inv_mul_eq_one {a : α} : ↑u⁻¹ * a = 1 ↔ ↑u = a :=
⟨inv_inv u ▸ units.inv_eq_of_mul_eq_one_right, inv_mul_of_eq⟩

@[to_additive] lemma mul_eq_one_iff_eq_inv {a : α} : a * u = 1 ↔ a = ↑u⁻¹ :=
by rw [←mul_inv_eq_one, inv_inv]

@[to_additive] lemma mul_eq_one_iff_inv_eq {a : α} : ↑u * a = 1 ↔ ↑u⁻¹ = a :=
by rw [←inv_mul_eq_one, inv_inv]

@[to_additive] lemma inv_unique {u₁ u₂ : αˣ} (h : (↑u₁ : α) = ↑u₂) : (↑u₁⁻¹ : α) = ↑u₂⁻¹ :=
units.inv_eq_of_mul_eq_one_right $ by rw [h, u₂.mul_inv]

@[simp, to_additive]
lemma coe_inv {M : Type*} [division_monoid M] (u : units M) : ↑u⁻¹ = (u⁻¹ : M) :=
eq.symm $ inv_eq_of_mul_eq_one_right u.mul_inv

end units

/-- For `a, b` in a `comm_monoid` such that `a * b = 1`, makes a unit out of `a`. -/
@[to_additive "For `a, b` in an `add_comm_monoid` such that `a + b = 0`, makes an add_unit
out of `a`."]
def units.mk_of_mul_eq_one [comm_monoid α] (a b : α) (hab : a * b = 1) :
  αˣ :=
⟨a, b, hab, (mul_comm b a).trans hab⟩

@[simp, to_additive] lemma units.coe_mk_of_mul_eq_one [comm_monoid α] {a b : α} (h : a * b = 1) :
  (units.mk_of_mul_eq_one a b h : α) = a := rfl

section monoid
variables [monoid α] {a b c : α}

/-- Partial division. It is defined when the
  second argument is invertible, and unlike the division operator
  in `division_ring` it is not totalized at zero. -/
def divp (a : α) (u) : α := a * (u⁻¹ : αˣ)

infix ` /ₚ `:70 := divp

@[simp] theorem divp_self (u : αˣ) : (u : α) /ₚ u = 1 := units.mul_inv _

@[simp] theorem divp_one (a : α) : a /ₚ 1 = a := mul_one _

theorem divp_assoc (a b : α) (u : αˣ) : a * b /ₚ u = a * (b /ₚ u) :=
mul_assoc _ _ _

/-- `field_simp` needs the reverse direction of `divp_assoc` to move all `/ₚ` to the right. -/
@[field_simps] lemma divp_assoc' (x y : α) (u : αˣ) : x * (y /ₚ u) = (x * y) /ₚ u :=
(divp_assoc _ _ _).symm

@[simp] theorem divp_inv (u : αˣ) : a /ₚ u⁻¹ = a * u := rfl

@[simp] theorem divp_mul_cancel (a : α) (u : αˣ) : a /ₚ u * u = a :=
(mul_assoc _ _ _).trans $ by rw [units.inv_mul, mul_one]

@[simp] theorem mul_divp_cancel (a : α) (u : αˣ) : (a * u) /ₚ u = a :=
(mul_assoc _ _ _).trans $ by rw [units.mul_inv, mul_one]

@[simp] theorem divp_left_inj (u : αˣ) {a b : α} : a /ₚ u = b /ₚ u ↔ a = b :=
units.mul_left_inj _

@[field_simps] theorem divp_divp_eq_divp_mul (x : α) (u₁ u₂ : αˣ) :
  (x /ₚ u₁) /ₚ u₂ = x /ₚ (u₂ * u₁) :=
by simp only [divp, mul_inv_rev, units.coe_mul, mul_assoc]

@[field_simps] theorem divp_eq_iff_mul_eq {x : α} {u : αˣ} {y : α} : x /ₚ u = y ↔ y * u = x :=
u.mul_left_inj.symm.trans $ by rw [divp_mul_cancel]; exact ⟨eq.symm, eq.symm⟩

@[field_simps] theorem eq_divp_iff_mul_eq {x : α} {u : αˣ} {y : α} : x = y /ₚ u ↔ x * u = y :=
by rw [eq_comm, divp_eq_iff_mul_eq]

theorem divp_eq_one_iff_eq {a : α} {u : αˣ} : a /ₚ u = 1 ↔ a = u :=
(units.mul_left_inj u).symm.trans $ by rw [divp_mul_cancel, one_mul]

@[simp] theorem one_divp (u : αˣ) : 1 /ₚ u = ↑u⁻¹ :=
one_mul _

/-- Used for `field_simp` to deal with inverses of units. -/
@[field_simps] lemma inv_eq_one_divp (u : αˣ) : ↑u⁻¹ = 1 /ₚ u :=
by rw one_divp

/--
Used for `field_simp` to deal with inverses of units. This form of the lemma
is essential since `field_simp` likes to use `inv_eq_one_div` to rewrite
`↑u⁻¹ = ↑(1 / u)`.
-/
@[field_simps] lemma inv_eq_one_divp' (u : αˣ) :
  ((1 / u : αˣ) : α) = 1 /ₚ u :=
by rw [one_div, one_divp]

/--
`field_simp` moves division inside `αˣ` to the right, and this lemma
lifts the calculation to `α`.
-/
@[field_simps] lemma coe_div_eq_divp (u₁ u₂ : αˣ) : ↑(u₁ / u₂) = ↑u₁ /ₚ u₂ :=
by rw [divp, division_def, units.coe_mul]

end monoid

section comm_monoid

variables [comm_monoid α]

@[field_simps] theorem divp_mul_eq_mul_divp (x y : α) (u : αˣ) : x /ₚ u * y = x * y /ₚ u :=
by simp_rw [divp, mul_assoc, mul_comm]

-- Theoretically redundant as `field_simp` lemma.
@[field_simps] lemma divp_eq_divp_iff {x y : α} {ux uy : αˣ} :
  x /ₚ ux = y /ₚ uy ↔ x * uy = y * ux :=
by rw [divp_eq_iff_mul_eq, divp_mul_eq_mul_divp, divp_eq_iff_mul_eq]

-- Theoretically redundant as `field_simp` lemma.
@[field_simps] lemma divp_mul_divp (x y : α) (ux uy : αˣ) :
  (x /ₚ ux) * (y /ₚ uy) = (x * y) /ₚ (ux * uy) :=
by rw [divp_mul_eq_mul_divp, divp_assoc', divp_divp_eq_divp_mul]

end comm_monoid

/-!
# `is_unit` predicate

In this file we define the `is_unit` predicate on a `monoid`, and
prove a few basic properties. For the bundled version see `units`. See
also `prime`, `associated`, and `irreducible` in `algebra/associated`.

-/

section is_unit

variables {M : Type*} {N : Type*}

/-- An element `a : M` of a monoid is a unit if it has a two-sided inverse.
The actual definition says that `a` is equal to some `u : Mˣ`, where
`Mˣ` is a bundled version of `is_unit`. -/
@[to_additive "An element `a : M` of an add_monoid is an `add_unit` if it has
a two-sided additive inverse. The actual definition says that `a` is equal to some
`u : add_units M`, where `add_units M` is a bundled version of `is_add_unit`."]
def is_unit [monoid M] (a : M) : Prop := ∃ u : Mˣ, (u : M) = a

@[nontriviality, to_additive]
lemma is_unit_of_subsingleton [monoid M] [subsingleton M] (a : M) : is_unit a :=
⟨⟨a, a, subsingleton.elim _ _, subsingleton.elim _ _⟩, rfl⟩

attribute [nontriviality] is_add_unit_of_subsingleton

@[to_additive] instance [monoid M] : can_lift M Mˣ coe is_unit :=
{ prf := λ _, id }

@[to_additive] instance [monoid M] [subsingleton M] : unique Mˣ :=
{ default := 1,
  uniq := λ a, units.coe_eq_one.mp $ subsingleton.elim (a : M) 1 }

@[simp, to_additive is_add_unit_add_unit]
protected lemma units.is_unit [monoid M] (u : Mˣ) : is_unit (u : M) := ⟨u, rfl⟩

@[simp, to_additive]
theorem is_unit_one [monoid M] : is_unit (1:M) := ⟨1, rfl⟩

@[to_additive] theorem is_unit_of_mul_eq_one [comm_monoid M]
  (a b : M) (h : a * b = 1) : is_unit a :=
⟨units.mk_of_mul_eq_one a b h, rfl⟩

@[to_additive is_add_unit.exists_neg] theorem is_unit.exists_right_inv [monoid M]
  {a : M} (h : is_unit a) : ∃ b, a * b = 1 :=
by { rcases h with ⟨⟨a, b, hab, _⟩, rfl⟩, exact ⟨b, hab⟩ }

@[to_additive is_add_unit.exists_neg'] theorem is_unit.exists_left_inv [monoid M]
  {a : M} (h : is_unit a) : ∃ b, b * a = 1 :=
by { rcases h with ⟨⟨a, b, _, hba⟩, rfl⟩, exact ⟨b, hba⟩ }

@[to_additive] theorem is_unit_iff_exists_inv [comm_monoid M]
  {a : M} : is_unit a ↔ ∃ b, a * b = 1 :=
⟨λ h, h.exists_right_inv,
 λ ⟨b, hab⟩, is_unit_of_mul_eq_one _ b hab⟩

@[to_additive] theorem is_unit_iff_exists_inv' [comm_monoid M]
  {a : M} : is_unit a ↔ ∃ b, b * a = 1 :=
by simp [is_unit_iff_exists_inv, mul_comm]

@[to_additive]
lemma is_unit.mul [monoid M] {x y : M} : is_unit x → is_unit y → is_unit (x * y) :=
by { rintros ⟨x, rfl⟩ ⟨y, rfl⟩, exact ⟨x * y, units.coe_mul _ _⟩ }

/-- Multiplication by a `u : Mˣ` on the right doesn't affect `is_unit`. -/
@[simp, to_additive "Addition of a `u : add_units M` on the right doesn't
affect `is_add_unit`."]
theorem units.is_unit_mul_units [monoid M] (a : M) (u : Mˣ) :
  is_unit (a * u) ↔ is_unit a :=
iff.intro
  (assume ⟨v, hv⟩,
    have is_unit (a * ↑u * ↑u⁻¹), by existsi v * u⁻¹; rw [←hv, units.coe_mul],
    by rwa [mul_assoc, units.mul_inv, mul_one] at this)
  (λ v, v.mul u.is_unit)

/-- Multiplication by a `u : Mˣ` on the left doesn't affect `is_unit`. -/
@[simp, to_additive "Addition of a `u : add_units M` on the left doesn't affect `is_add_unit`."]
theorem units.is_unit_units_mul {M : Type*} [monoid M] (u : Mˣ) (a : M) :
  is_unit (↑u * a) ↔ is_unit a :=
iff.intro
  (assume ⟨v, hv⟩,
    have is_unit (↑u⁻¹ * (↑u * a)), by existsi u⁻¹ * v; rw [←hv, units.coe_mul],
    by rwa [←mul_assoc, units.inv_mul, one_mul] at this)
  u.is_unit.mul

@[to_additive]
theorem is_unit_of_mul_is_unit_left [comm_monoid M] {x y : M}
  (hu : is_unit (x * y)) : is_unit x :=
let ⟨z, hz⟩ := is_unit_iff_exists_inv.1 hu in
is_unit_iff_exists_inv.2 ⟨y * z, by rwa ← mul_assoc⟩

@[to_additive] theorem is_unit_of_mul_is_unit_right [comm_monoid M] {x y : M}
  (hu : is_unit (x * y)) : is_unit y :=
@is_unit_of_mul_is_unit_left _ _ y x $ by rwa mul_comm

namespace is_unit

@[simp, to_additive]
lemma mul_iff [comm_monoid M] {x y : M} : is_unit (x * y) ↔ is_unit x ∧ is_unit y :=
⟨λ h, ⟨is_unit_of_mul_is_unit_left h, is_unit_of_mul_is_unit_right h⟩,
  λ h, is_unit.mul h.1 h.2⟩

section monoid

variables [monoid M] {a b c : M}

/-- The element of the group of units, corresponding to an element of a monoid which is a unit. When
`α` is a `division_monoid`, use `is_unit.unit'` instead. -/
@[to_additive "The element of the additive group of additive units, corresponding to an element of
an additive monoid which is an additive unit. When `α` is a `subtraction_monoid`, use
`is_add_unit.add_unit'` instead."]
protected noncomputable def unit (h : is_unit a) : Mˣ :=
(classical.some h).copy a (classical.some_spec h).symm _ rfl

@[simp, to_additive]
lemma unit_of_coe_units {a : Mˣ} (h : is_unit (a : M)) : h.unit = a :=
units.ext $ rfl

@[simp, to_additive] lemma unit_spec (h : is_unit a) : ↑h.unit = a := rfl

@[simp, to_additive]
lemma coe_inv_mul (h : is_unit a) : ↑(h.unit)⁻¹ * a = 1 := units.mul_inv _

@[simp, to_additive] lemma mul_coe_inv (h : is_unit a) : a * ↑(h.unit)⁻¹ = 1 :=
by convert h.unit.mul_inv

/-- `is_unit x` is decidable if we can decide if `x` comes from `Mˣ`. -/
@[to_additive "`is_add_unit x` is decidable if we can decide if `x` comes from `add_units M"]
instance (x : M) [h : decidable (∃ u : Mˣ, ↑u = x)] : decidable (is_unit x) := h

@[to_additive] lemma mul_left_inj (h : is_unit a) : b * a = c * a ↔ b = c :=
let ⟨u, hu⟩ := h in hu ▸ u.mul_left_inj

@[to_additive] lemma mul_right_inj (h : is_unit a) : a * b = a * c ↔ b = c :=
let ⟨u, hu⟩ := h in hu ▸ u.mul_right_inj

@[to_additive] protected lemma mul_left_cancel (h : is_unit a) : a * b = a * c → b = c :=
h.mul_right_inj.1

@[to_additive] protected lemma mul_right_cancel (h : is_unit b) : a * b = c * b → a = c :=
h.mul_left_inj.1

@[to_additive] protected lemma mul_right_injective (h : is_unit a) : injective ((*) a) :=
λ _ _, h.mul_left_cancel

@[to_additive] protected lemma mul_left_injective (h : is_unit b) : injective (* b) :=
λ _ _, h.mul_right_cancel

end monoid

variables [division_monoid M] {a : M}

@[simp, to_additive] protected lemma inv_mul_cancel : is_unit a → a⁻¹ * a = 1 :=
by { rintro ⟨u, rfl⟩, rw [← units.coe_inv, units.inv_mul] }

@[simp, to_additive] protected lemma mul_inv_cancel : is_unit a → a * a⁻¹ = 1 :=
by { rintro ⟨u, rfl⟩, rw [← units.coe_inv, units.mul_inv] }

end is_unit -- namespace

end is_unit -- section

section noncomputable_defs

variables {M : Type*}

/-- Constructs a `group` structure on a `monoid` consisting only of units. -/
noncomputable def group_of_is_unit [hM : monoid M] (h : ∀ (a : M), is_unit a) : group M :=
{ inv := λ a, ↑((h a).unit)⁻¹,
  mul_left_inv := λ a, by
  { change ↑((h a).unit)⁻¹ * a = 1,
    rw [units.inv_mul_eq_iff_eq_mul, (h a).unit_spec, mul_one] },
  .. hM }

/-- Constructs a `comm_group` structure on a `comm_monoid` consisting only of units. -/
noncomputable def comm_group_of_is_unit [hM : comm_monoid M] (h : ∀ (a : M), is_unit a) :
  comm_group M :=
{ inv := λ a, ↑((h a).unit)⁻¹,
  mul_left_inv := λ a, by
  { change ↑((h a).unit)⁻¹ * a = 1,
    rw [units.inv_mul_eq_iff_eq_mul, (h a).unit_spec, mul_one] },
  .. hM }

end noncomputable_defs
