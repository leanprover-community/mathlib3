/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import algebra.group_with_zero.basic
import algebra.group.units
import tactic.nontriviality
import tactic.assert_exists

/-!
# Lemmas about units in a `monoid_with_zero` or a `group_with_zero`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We also define `ring.inverse`, a globally defined function on any ring
(in fact any `monoid_with_zero`), which inverts units and sends non-units to zero.
-/

variables {α M₀ G₀ M₀' G₀' F F' : Type*}

variables [monoid_with_zero M₀]

namespace units

/-- An element of the unit group of a nonzero monoid with zero represented as an element
    of the monoid is nonzero. -/
@[simp] lemma ne_zero [nontrivial M₀] (u : M₀ˣ) :
  (u : M₀) ≠ 0 :=
left_ne_zero_of_mul_eq_one u.mul_inv

-- We can't use `mul_eq_zero` + `units.ne_zero` in the next two lemmas because we don't assume
-- `nonzero M₀`.

@[simp] lemma mul_left_eq_zero (u : M₀ˣ) {a : M₀} : a * u = 0 ↔ a = 0 :=
⟨λ h, by simpa using mul_eq_zero_of_left h ↑u⁻¹, λ h, mul_eq_zero_of_left h u⟩

@[simp] lemma mul_right_eq_zero (u : M₀ˣ) {a : M₀} : ↑u * a = 0 ↔ a = 0 :=
⟨λ h, by simpa using mul_eq_zero_of_right ↑u⁻¹ h, mul_eq_zero_of_right u⟩

end units

namespace is_unit

lemma ne_zero [nontrivial M₀] {a : M₀} (ha : is_unit a) : a ≠ 0 := let ⟨u, hu⟩ :=
ha in hu ▸ u.ne_zero

lemma mul_right_eq_zero {a b : M₀} (ha : is_unit a) : a * b = 0 ↔ b = 0 :=
let ⟨u, hu⟩ := ha in hu ▸ u.mul_right_eq_zero

lemma mul_left_eq_zero {a b : M₀} (hb : is_unit b) : a * b = 0 ↔ a = 0 :=
let ⟨u, hu⟩ := hb in hu ▸ u.mul_left_eq_zero

end is_unit

@[simp] theorem is_unit_zero_iff : is_unit (0 : M₀) ↔ (0:M₀) = 1 :=
⟨λ ⟨⟨_, a, (a0 : 0 * a = 1), _⟩, rfl⟩, by rwa zero_mul at a0,
 λ h, @is_unit_of_subsingleton _ _ (subsingleton_of_zero_eq_one h) 0⟩

@[simp] theorem not_is_unit_zero [nontrivial M₀] : ¬ is_unit (0 : M₀) :=
mt is_unit_zero_iff.1 zero_ne_one

namespace ring
open_locale classical

/-- Introduce a function `inverse` on a monoid with zero `M₀`, which sends `x` to `x⁻¹` if `x` is
invertible and to `0` otherwise.  This definition is somewhat ad hoc, but one needs a fully (rather
than partially) defined inverse function for some purposes, including for calculus.

Note that while this is in the `ring` namespace for brevity, it requires the weaker assumption
`monoid_with_zero M₀` instead of `ring M₀`. -/
noncomputable def inverse : M₀ → M₀ :=
λ x, if h : is_unit x then ((h.unit⁻¹ : M₀ˣ) : M₀) else 0

/-- By definition, if `x` is invertible then `inverse x = x⁻¹`. -/
@[simp] lemma inverse_unit (u : M₀ˣ) : inverse (u : M₀) = (u⁻¹ : M₀ˣ) :=
begin
  simp only [units.is_unit, inverse, dif_pos],
  exact units.inv_unique rfl
end

/-- By definition, if `x` is not invertible then `inverse x = 0`. -/
@[simp] lemma inverse_non_unit (x : M₀) (h : ¬(is_unit x)) : inverse x = 0 := dif_neg h

lemma mul_inverse_cancel (x : M₀) (h : is_unit x) : x * inverse x = 1 :=
by { rcases h with ⟨u, rfl⟩, rw [inverse_unit, units.mul_inv], }

lemma inverse_mul_cancel (x : M₀) (h : is_unit x) : inverse x * x = 1 :=
by { rcases h with ⟨u, rfl⟩, rw [inverse_unit, units.inv_mul], }

lemma mul_inverse_cancel_right (x y : M₀) (h : is_unit x) : y * x * inverse x = y :=
by rw [mul_assoc, mul_inverse_cancel x h, mul_one]

lemma inverse_mul_cancel_right (x y : M₀) (h : is_unit x) : y * inverse x * x = y :=
by rw [mul_assoc, inverse_mul_cancel x h, mul_one]

lemma mul_inverse_cancel_left (x y : M₀) (h : is_unit x) : x * (inverse x * y) = y :=
by rw [← mul_assoc, mul_inverse_cancel x h, one_mul]

lemma inverse_mul_cancel_left (x y : M₀) (h : is_unit x) : inverse x * (x * y) = y :=
by rw [← mul_assoc, inverse_mul_cancel x h, one_mul]

lemma inverse_mul_eq_iff_eq_mul (x y z : M₀) (h : is_unit x) :
  inverse x * y = z ↔ y = x * z :=
⟨λ h1, by rw [← h1, mul_inverse_cancel_left _ _ h], λ h1, by rw [h1, inverse_mul_cancel_left _ _ h]⟩

lemma eq_mul_inverse_iff_mul_eq (x y z : M₀) (h : is_unit z) :
  x = y * inverse z ↔ x * z = y :=
⟨λ h1, by rw [h1, inverse_mul_cancel_right _ _ h],
  λ h1, by rw [← h1, mul_inverse_cancel_right _ _ h]⟩

variables (M₀)

@[simp] lemma inverse_one : inverse (1 : M₀) = 1 :=
inverse_unit 1

@[simp] lemma inverse_zero : inverse (0 : M₀) = 0 :=
by { nontriviality, exact inverse_non_unit _ not_is_unit_zero }

variables {M₀}

end ring

lemma is_unit.ring_inverse {a : M₀} : is_unit a → is_unit (ring.inverse a)
| ⟨u, hu⟩ := hu ▸ ⟨u⁻¹, (ring.inverse_unit u).symm⟩

@[simp] lemma is_unit_ring_inverse {a : M₀} : is_unit (ring.inverse a) ↔ is_unit a :=
⟨λ h, begin
  casesI subsingleton_or_nontrivial M₀,
  { convert h },
  { contrapose h,
    rw ring.inverse_non_unit _ h,
    exact not_is_unit_zero, },
end, is_unit.ring_inverse⟩

namespace units
variables [group_with_zero G₀]
variables {a b : G₀}

/-- Embed a non-zero element of a `group_with_zero` into the unit group.
  By combining this function with the operations on units,
  or the `/ₚ` operation, it is possible to write a division
  as a partial function with three arguments. -/
def mk0 (a : G₀) (ha : a ≠ 0) : G₀ˣ :=
⟨a, a⁻¹, mul_inv_cancel ha, inv_mul_cancel ha⟩

@[simp] lemma mk0_one (h := one_ne_zero) :
  mk0 (1 : G₀) h = 1 :=
by { ext, refl }

@[simp] lemma coe_mk0 {a : G₀} (h : a ≠ 0) : (mk0 a h : G₀) = a := rfl

@[simp] lemma mk0_coe (u : G₀ˣ) (h : (u : G₀) ≠ 0) : mk0 (u : G₀) h = u :=
units.ext rfl

@[simp] lemma mul_inv' (u : G₀ˣ) : (u : G₀) * u⁻¹ = 1 := mul_inv_cancel u.ne_zero

@[simp] lemma inv_mul' (u : G₀ˣ) : (u⁻¹ : G₀) * u = 1 := inv_mul_cancel u.ne_zero

@[simp] lemma mk0_inj {a b : G₀} (ha : a ≠ 0) (hb : b ≠ 0) :
  units.mk0 a ha = units.mk0 b hb ↔ a = b :=
⟨λ h, by injection h, λ h, units.ext h⟩

/-- In a group with zero, an existential over a unit can be rewritten in terms of `units.mk0`. -/
lemma exists0 {p : G₀ˣ → Prop} : (∃ g : G₀ˣ, p g) ↔ ∃ (g : G₀) (hg : g ≠ 0), p (units.mk0 g hg) :=
⟨λ ⟨g, pg⟩, ⟨g, g.ne_zero, (g.mk0_coe g.ne_zero).symm ▸ pg⟩, λ ⟨g, hg, pg⟩, ⟨units.mk0 g hg, pg⟩⟩

/-- An alternative version of `units.exists0`. This one is useful if Lean cannot
figure out `p` when using `units.exists0` from right to left. -/
lemma exists0' {p : Π g : G₀, g ≠ 0 → Prop} :
  (∃ (g : G₀) (hg : g ≠ 0), p g hg) ↔ ∃ g : G₀ˣ, p g g.ne_zero :=
iff.trans (by simp_rw [coe_mk0]) exists0.symm

@[simp] lemma exists_iff_ne_zero {x : G₀} : (∃ u : G₀ˣ, ↑u = x) ↔ x ≠ 0 :=
by simp [exists0]

lemma _root_.group_with_zero.eq_zero_or_unit (a : G₀) :
  a = 0 ∨ ∃ u : G₀ˣ, a = u :=
begin
  by_cases h : a = 0,
  { left,
    exact h },
  { right,
    simpa only [eq_comm] using units.exists_iff_ne_zero.mpr h }
end

end units

section group_with_zero
variables [group_with_zero G₀] {a b c : G₀}

lemma is_unit.mk0 (x : G₀) (hx : x ≠ 0) : is_unit x := (units.mk0 x hx).is_unit

lemma is_unit_iff_ne_zero : is_unit a ↔ a ≠ 0 := units.exists_iff_ne_zero

alias is_unit_iff_ne_zero ↔ _ ne.is_unit

attribute [protected] ne.is_unit

@[priority 10] -- see Note [lower instance priority]
instance group_with_zero.no_zero_divisors : no_zero_divisors G₀ :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ a b h,
    begin
      contrapose! h,
      exact ((units.mk0 a h.1) * (units.mk0 b h.2)).ne_zero
    end,
  .. (‹_› : group_with_zero G₀) }

@[priority 10] -- see Note [lower instance priority]
instance group_with_zero.cancel_monoid_with_zero : cancel_monoid_with_zero G₀ :=
{ mul_left_cancel_of_ne_zero := λ x y z hx h,
    by rw [← inv_mul_cancel_left₀ hx y, h, inv_mul_cancel_left₀ hx z],
  mul_right_cancel_of_ne_zero := λ x y z hy h,
    by rw [← mul_inv_cancel_right₀ hy x, h, mul_inv_cancel_right₀ hy z],
  .. (‹_› : group_with_zero G₀) }

-- Can't be put next to the other `mk0` lemmas because it depends on the
-- `no_zero_divisors` instance, which depends on `mk0`.
@[simp] lemma units.mk0_mul (x y : G₀) (hxy) :
  units.mk0 (x * y) hxy =
    units.mk0 x (mul_ne_zero_iff.mp hxy).1 * units.mk0 y (mul_ne_zero_iff.mp hxy).2 :=
by { ext, refl }

lemma div_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a / b ≠ 0 :=
by { rw div_eq_mul_inv, exact mul_ne_zero ha (inv_ne_zero hb) }

@[simp] lemma div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = 0:=
by simp [div_eq_mul_inv]

lemma div_ne_zero_iff : a / b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 :=
div_eq_zero_iff.not.trans not_or_distrib

lemma ring.inverse_eq_inv (a : G₀) : ring.inverse a = a⁻¹ :=
begin
  obtain rfl | ha := eq_or_ne a 0,
  { simp },
  { exact ring.inverse_unit (units.mk0 a ha) }
end

@[simp] lemma ring.inverse_eq_inv' : (ring.inverse : G₀ → G₀) = has_inv.inv :=
funext ring.inverse_eq_inv

end group_with_zero

section comm_group_with_zero -- comm
variables [comm_group_with_zero G₀] {a b c d : G₀}

@[priority 10] -- see Note [lower instance priority]
instance comm_group_with_zero.cancel_comm_monoid_with_zero : cancel_comm_monoid_with_zero G₀ :=
{ ..group_with_zero.cancel_monoid_with_zero, ..comm_group_with_zero.to_comm_monoid_with_zero G₀ }

@[priority 100] -- See note [lower instance priority]
instance comm_group_with_zero.to_division_comm_monoid : division_comm_monoid G₀ :=
{ ..‹comm_group_with_zero G₀›, ..group_with_zero.to_division_monoid }

end comm_group_with_zero

section noncomputable_defs

open_locale classical
variables {M : Type*} [nontrivial M]

/-- Constructs a `group_with_zero` structure on a `monoid_with_zero`
  consisting only of units and 0. -/
noncomputable def group_with_zero_of_is_unit_or_eq_zero [hM : monoid_with_zero M]
  (h : ∀ (a : M), is_unit a ∨ a = 0) : group_with_zero M :=
{ inv := λ a, if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).unit⁻¹,
  inv_zero := dif_pos rfl,
  mul_inv_cancel := λ a h0, by
  { change a * (if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).unit⁻¹) = 1,
    rw [dif_neg h0, units.mul_inv_eq_iff_eq_mul, one_mul, is_unit.unit_spec] },
  exists_pair_ne := nontrivial.exists_pair_ne,
.. hM }

/-- Constructs a `comm_group_with_zero` structure on a `comm_monoid_with_zero`
  consisting only of units and 0. -/
noncomputable def comm_group_with_zero_of_is_unit_or_eq_zero [hM : comm_monoid_with_zero M]
  (h : ∀ (a : M), is_unit a ∨ a = 0) : comm_group_with_zero M :=
{ .. (group_with_zero_of_is_unit_or_eq_zero h), .. hM }

end noncomputable_defs

-- Guard against import creep
assert_not_exists multiplicative
