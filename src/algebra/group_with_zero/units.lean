/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import algebra.group_with_zero.basic
import algebra.hom.units
import group_theory.group_action.units

/-!
# Lemmas about units in a `monoid_with_zero` or a `group_with_zero`.

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

lemma mul_inverse_rev' {a b : M₀} (h : commute a b) : inverse (a * b) = inverse b * inverse a :=
begin
  by_cases hab : is_unit (a * b),
  { obtain ⟨⟨a, rfl⟩, b, rfl⟩ := h.is_unit_mul_iff.mp hab,
    rw [←units.coe_mul, inverse_unit, inverse_unit, inverse_unit, ←units.coe_mul,
      mul_inv_rev], },
  obtain ha | hb := not_and_distrib.mp (mt h.is_unit_mul_iff.mpr hab),
  { rw [inverse_non_unit _ hab, inverse_non_unit _ ha, mul_zero]},
  { rw [inverse_non_unit _ hab, inverse_non_unit _ hb, zero_mul]},
end

lemma mul_inverse_rev {M₀} [comm_monoid_with_zero M₀] (a b : M₀) :
  ring.inverse (a * b) = inverse b * inverse a :=
mul_inverse_rev' (commute.all _ _)

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

lemma commute.ring_inverse_ring_inverse {a b : M₀} (h : commute a b) :
  commute (ring.inverse a) (ring.inverse b) :=
(ring.mul_inverse_rev' h.symm).symm.trans $ (congr_arg _ h.symm.eq).trans $ ring.mul_inverse_rev' h


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

@[simp] lemma smul_mk0 {α : Type*} [has_smul G₀ α] {g : G₀} (hg : g ≠ 0) (a : α) :
  (mk0 g hg) • a = g • a :=
rfl

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

@[simp] lemma div_self (h : a ≠ 0) : a / a = 1 := h.is_unit.div_self

lemma eq_mul_inv_iff_mul_eq₀ (hc : c ≠ 0) : a = b * c⁻¹ ↔ a * c = b :=
hc.is_unit.eq_mul_inv_iff_mul_eq

lemma eq_inv_mul_iff_mul_eq₀ (hb : b ≠ 0) : a = b⁻¹ * c ↔ b * a = c :=
hb.is_unit.eq_inv_mul_iff_mul_eq

lemma inv_mul_eq_iff_eq_mul₀ (ha : a ≠ 0) : a⁻¹ * b = c ↔ b = a * c :=
ha.is_unit.inv_mul_eq_iff_eq_mul

lemma mul_inv_eq_iff_eq_mul₀ (hb : b ≠ 0) : a * b⁻¹ = c ↔ a = c * b :=
hb.is_unit.mul_inv_eq_iff_eq_mul

lemma mul_inv_eq_one₀ (hb : b ≠ 0) : a * b⁻¹ = 1 ↔ a = b := hb.is_unit.mul_inv_eq_one
lemma inv_mul_eq_one₀ (ha : a ≠ 0) : a⁻¹ * b = 1 ↔ a = b := ha.is_unit.inv_mul_eq_one

lemma mul_eq_one_iff_eq_inv₀ (hb : b ≠ 0) : a * b = 1 ↔ a = b⁻¹ := hb.is_unit.mul_eq_one_iff_eq_inv
lemma mul_eq_one_iff_inv_eq₀ (ha : a ≠ 0) : a * b = 1 ↔ a⁻¹ = b := ha.is_unit.mul_eq_one_iff_inv_eq

@[simp] lemma div_mul_cancel (a : G₀) (h : b ≠ 0) : a / b * b = a := h.is_unit.div_mul_cancel _
@[simp] lemma mul_div_cancel (a : G₀) (h : b ≠ 0) : a * b / b = a := h.is_unit.mul_div_cancel _

lemma mul_one_div_cancel (h : a ≠ 0) : a * (1 / a) = 1 := h.is_unit.mul_one_div_cancel
lemma one_div_mul_cancel (h : a ≠ 0) : (1 / a) * a = 1 := h.is_unit.one_div_mul_cancel

lemma div_left_inj' (hc : c ≠ 0) : a / c = b / c ↔ a = b := hc.is_unit.div_left_inj

@[field_simps] lemma div_eq_iff (hb : b ≠ 0) : a / b = c ↔ a = c * b := hb.is_unit.div_eq_iff
@[field_simps] lemma eq_div_iff (hb : b ≠ 0) : c = a / b ↔ c * b = a := hb.is_unit.eq_div_iff

lemma div_eq_iff_mul_eq (hb : b ≠ 0) : a / b = c ↔ c * b = a := hb.is_unit.div_eq_iff.trans eq_comm
lemma eq_div_iff_mul_eq (hc : c ≠ 0) : a = b / c ↔ a * c = b := hc.is_unit.eq_div_iff

lemma div_eq_of_eq_mul (hb : b ≠ 0) : a = c * b → a / b = c := hb.is_unit.div_eq_of_eq_mul
lemma eq_div_of_mul_eq (hc : c ≠ 0) : a * c = b → a = b / c := hc.is_unit.eq_div_of_mul_eq

lemma div_eq_one_iff_eq (hb : b ≠ 0) : a / b = 1 ↔ a = b := hb.is_unit.div_eq_one_iff_eq

lemma div_mul_left (hb : b ≠ 0) : b / (a * b) = 1 / a := hb.is_unit.div_mul_left

lemma mul_div_mul_right (a b : G₀) (hc : c ≠ 0) : (a * c) / (b * c) = a / b :=
hc.is_unit.mul_div_mul_right _ _

lemma mul_mul_div (a : G₀) (hb : b ≠ 0) : a = a * b * (1 / b) := (hb.is_unit.mul_mul_div _).symm

lemma div_div_div_cancel_right (a : G₀) (hc : c ≠ 0) : (a / c) / (b / c) = a / b :=
by rw [div_div_eq_mul_div, div_mul_cancel _ hc]

lemma div_mul_div_cancel (a : G₀) (hc : c ≠ 0) : (a / c) * (c / b) = a / b :=
by rw [← mul_div_assoc, div_mul_cancel _ hc]

lemma div_mul_cancel_of_imp {a b : G₀} (h : b = 0 → a = 0) : a / b * b = a :=
classical.by_cases (λ hb : b = 0, by simp [*]) (div_mul_cancel a)

lemma mul_div_cancel_of_imp {a b : G₀} (h : b = 0 → a = 0) : a * b / b = a :=
classical.by_cases (λ hb : b = 0, by simp [*]) (mul_div_cancel a)

@[simp] theorem divp_mk0 (a : G₀) {b : G₀} (hb : b ≠ 0) :
  a /ₚ units.mk0 b hb = a / b :=
divp_eq_div _ _

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

lemma div_mul_right (b : G₀) (ha : a ≠ 0) : a / (a * b) = 1 / b := ha.is_unit.div_mul_right _

lemma mul_div_cancel_left_of_imp {a b : G₀} (h : a = 0 → b = 0) : a * b / a = b :=
by rw [mul_comm, mul_div_cancel_of_imp h]

lemma mul_div_cancel_left (b : G₀) (ha : a ≠ 0) : a * b / a = b := ha.is_unit.mul_div_cancel_left _

lemma mul_div_cancel_of_imp' {a b : G₀} (h : b = 0 → a = 0) : b * (a / b) = a :=
by rw [mul_comm, div_mul_cancel_of_imp h]

lemma mul_div_cancel' (a : G₀) (hb : b ≠ 0) : b * (a / b) = a := hb.is_unit.mul_div_cancel' _

lemma mul_div_mul_left (a b : G₀) (hc : c ≠ 0) : (c * a) / (c * b) = a / b :=
hc.is_unit.mul_div_mul_left _ _

lemma mul_eq_mul_of_div_eq_div (a : G₀) {b : G₀} (c : G₀) {d : G₀} (hb : b ≠ 0) (hd : d ≠ 0)
  (h : a / b = c / d) : a * d = c * b :=
by rw [←mul_one a, ←div_self hb, ←mul_comm_div, h, div_mul_eq_mul_div, div_mul_cancel _ hd]

@[field_simps] lemma div_eq_div_iff (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = c * b :=
hb.is_unit.div_eq_div_iff hd.is_unit

lemma div_div_cancel' (ha : a ≠ 0) : a / (a / b) = b := ha.is_unit.div_div_cancel

lemma div_helper (b : G₀) (h : a ≠ 0) : 1 / (a * b) * a = 1 / b :=
by rw [div_mul_eq_mul_div, one_mul, div_mul_right _ h]

end comm_group_with_zero


namespace semiconj_by

@[simp] lemma zero_right [mul_zero_class G₀] (a : G₀) : semiconj_by a 0 0 :=
by simp only [semiconj_by, mul_zero, zero_mul]

@[simp] lemma zero_left [mul_zero_class G₀] (x y : G₀) : semiconj_by 0 x y :=
by simp only [semiconj_by, mul_zero, zero_mul]

variables [group_with_zero G₀] {a x y x' y' : G₀}

@[simp] lemma inv_symm_left_iff₀ : semiconj_by a⁻¹ x y ↔ semiconj_by a y x :=
classical.by_cases
  (λ ha : a = 0, by simp only [ha, inv_zero, semiconj_by.zero_left])
  (λ ha, @units_inv_symm_left_iff _ _ (units.mk0 a ha) _ _)

lemma inv_symm_left₀ (h : semiconj_by a x y) : semiconj_by a⁻¹ y x :=
semiconj_by.inv_symm_left_iff₀.2 h

lemma inv_right₀ (h : semiconj_by a x y) : semiconj_by a x⁻¹ y⁻¹ :=
begin
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

@[simp] lemma inv_right_iff₀ : semiconj_by a x⁻¹ y⁻¹ ↔ semiconj_by a x y :=
⟨λ h, inv_inv x ▸ inv_inv y ▸ h.inv_right₀, inv_right₀⟩

lemma div_right (h : semiconj_by a x y) (h' : semiconj_by a x' y') :
  semiconj_by a (x / x') (y / y') :=
by { rw [div_eq_mul_inv, div_eq_mul_inv], exact h.mul_right h'.inv_right₀ }

end semiconj_by

namespace commute

@[simp] theorem zero_right [mul_zero_class G₀] (a : G₀) :commute a 0 := semiconj_by.zero_right a
@[simp] theorem zero_left [mul_zero_class G₀] (a : G₀) : commute 0 a := semiconj_by.zero_left a a

variables [group_with_zero G₀] {a b c : G₀}

@[simp] theorem inv_left_iff₀ : commute a⁻¹ b ↔ commute a b :=
semiconj_by.inv_symm_left_iff₀

theorem inv_left₀ (h : commute a b) : commute a⁻¹ b := inv_left_iff₀.2 h

@[simp] theorem inv_right_iff₀ : commute a b⁻¹ ↔ commute a b :=
semiconj_by.inv_right_iff₀

theorem inv_right₀ (h : commute a b) : commute a b⁻¹ := inv_right_iff₀.2 h

@[simp] theorem div_right (hab : commute a b) (hac : commute a c) :
  commute a (b / c) :=
hab.div_right hac

@[simp] theorem div_left (hac : commute a c) (hbc : commute b c) :
  commute (a / b) c :=
by { rw div_eq_mul_inv, exact hac.mul_left hbc.inv_left₀ }

end commute

section monoid_with_zero
variables [group_with_zero G₀] [nontrivial M₀]
  [monoid_with_zero M₀'] [monoid_with_zero_hom_class F G₀ M₀]
  [monoid_with_zero_hom_class F' G₀ M₀'] (f : F) {a : G₀}
include M₀

lemma map_ne_zero : f a ≠ 0 ↔ a ≠ 0 :=
⟨λ hfa ha, hfa $ ha.symm ▸ map_zero f, λ ha, ((is_unit.mk0 a ha).map f).ne_zero⟩

@[simp] lemma map_eq_zero : f a = 0 ↔ a = 0 := not_iff_not.1 (map_ne_zero f)

omit M₀
include M₀'

lemma eq_on_inv₀ (f g : F') (h : f a = g a) : f a⁻¹ = g a⁻¹ :=
begin
  rcases eq_or_ne a 0 with rfl|ha,
  { rw [inv_zero, map_zero, map_zero] },
  { exact (is_unit.mk0 a ha).eq_on_inv f g h }
end

end monoid_with_zero

section group_with_zero

variables [group_with_zero G₀] [group_with_zero G₀'] [monoid_with_zero_hom_class F G₀ G₀']
  (f : F) (a b : G₀)
include G₀'

/-- A monoid homomorphism between groups with zeros sending `0` to `0` sends `a⁻¹` to `(f a)⁻¹`. -/
@[simp] lemma map_inv₀ : f a⁻¹ = (f a)⁻¹ :=
begin
  by_cases h : a = 0, by simp [h],
  apply eq_inv_of_mul_eq_one_left,
  rw [← map_mul, inv_mul_cancel h, map_one]
end

@[simp] lemma map_div₀ : f (a / b) = f a / f b := map_div' f (map_inv₀ f) a b

end group_with_zero

/-- We define the inverse as a `monoid_with_zero_hom` by extending the inverse map by zero
on non-units. -/
noncomputable
def monoid_with_zero.inverse {M : Type*} [comm_monoid_with_zero M] :
  M →*₀ M :=
{ to_fun := ring.inverse,
  map_zero' := ring.inverse_zero _,
  map_one' := ring.inverse_one _,
  map_mul' := λ x y, (ring.mul_inverse_rev x y).trans (mul_comm _ _) }

@[simp]
lemma monoid_with_zero.coe_inverse {M : Type*} [comm_monoid_with_zero M] :
  (monoid_with_zero.inverse : M → M) = ring.inverse := rfl

@[simp]
lemma monoid_with_zero.inverse_apply {M : Type*} [comm_monoid_with_zero M] (a : M) :
  monoid_with_zero.inverse a = ring.inverse a := rfl

/-- Inversion on a commutative group with zero, considered as a monoid with zero homomorphism. -/
def inv_monoid_with_zero_hom {G₀ : Type*} [comm_group_with_zero G₀] : G₀ →*₀ G₀ :=
{ map_zero' := inv_zero,
  ..inv_monoid_hom }

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
