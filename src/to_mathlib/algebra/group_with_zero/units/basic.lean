import algebra.group_with_zero.units.basic
import to_mathlib.algebra.hom.units

variables {α M₀ G₀ M₀' G₀' F F' : Type*}

variables [monoid_with_zero M₀] [decidable_pred (is_unit : M₀ → Prop)]
  [group_with_zero G₀] [decidable_pred (is_unit : G₀ → Prop)]

@[simp] lemma surj_units_apply_zero  :
  surj_units (0 : M₀) = 1 :=
begin
  nontriviality M₀,
  exact surj_units_apply_not_is_unit not_is_unit_zero
end

lemma surj_units_apply_eq_mk0_apply {x : G₀} (hx : x ≠ 0) :
  surj_units x = units.mk0 _ hx :=
begin
  ext,
  simp [is_unit_iff_ne_zero, hx]
end

lemma coe_surj_units_apply_ne_zero {x : G₀} (hx : x ≠ 0) :
  (surj_units x : G₀) = x :=
coe_surj_units_apply_is_unit (is_unit_iff_ne_zero.mpr hx)
