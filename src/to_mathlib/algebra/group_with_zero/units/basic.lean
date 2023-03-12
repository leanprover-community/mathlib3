import algebra.group_with_zero.units.basic
import to_mathlib.algebra.hom.units

variables {α M₀ G₀ M₀' G₀' F F' : Type*}

variables [monoid_with_zero M₀] [group_with_zero G₀]

@[simp] lemma surj_units_apply_zero [decidable (is_unit (0 : M₀))] :
  surj_units (0 : M₀) = 1 :=
begin
  nontriviality M₀,
  exact surj_units_apply_not_is_unit not_is_unit_zero
end

lemma surj_units_apply_eq_mk0_apply {x : G₀} [decidable (is_unit x)] (hx : x ≠ 0) :
  surj_units x = units.mk0 _ hx :=
begin
  ext,
  simp [is_unit_iff_ne_zero, hx]
end
