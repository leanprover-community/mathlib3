import algebra.hom.units

variables {M : Type*} [monoid M]

noncomputable
def surj_units (x : M) [decidable (is_unit x)] : Mˣ := if h : is_unit x then h.unit else 1

instance group.decidable_is_unit {G : Type*} [group G] {x : G} : decidable (is_unit x) :=
is_true (group.is_unit x)

instance units.decidable_is_unit_coe {x : Mˣ} : decidable (is_unit (x : M)) :=
is_true (x.is_unit)

lemma surj_units_apply_is_unit {x : M} [decidable (is_unit x)] (hx : is_unit x) :
  surj_units x = hx.unit :=
dif_pos hx

lemma surj_units_apply_not_is_unit {x : M} [decidable (is_unit x)] (hx : ¬ is_unit x) :
  surj_units x = 1 :=
dif_neg hx

@[simp] lemma surj_units_apply_coe_units (x : Mˣ) [decidable (is_unit (x : M))] :
  surj_units (x : M) = x :=
by simp only [surj_units_apply_is_unit x.is_unit, is_unit.unit_of_coe_units]

@[simp] lemma surj_units_apply_one [decidable (is_unit (1 : M))] :
  surj_units (1 : M) = 1 :=
begin
  ext,
  simp only [is_unit.unit_spec, units.coe_one, surj_units_apply_is_unit is_unit_one]
end

@[simp] lemma coe_surj_units_apply_eq_iff {x : M} [decidable (is_unit (x : M))] :
  (surj_units x : M) = x ↔ is_unit x :=
begin
  by_cases h : is_unit x,
  { simp [surj_units_apply_is_unit h, h] },
  { simp only [surj_units_apply_not_is_unit h, h, units.coe_one, iff_false],
    contrapose! h,
    simp [←h] }
end

lemma surj_units_apply_inv_mul_surj_units_apply (x : M) [decidable (is_unit x)] :
  (surj_units x)⁻¹ * surj_units x = 1 :=
begin
  by_cases h : is_unit x,
  { simp [surj_units_apply_is_unit h] },
  { simp [surj_units_apply_not_is_unit h] }
end

lemma surj_units_apply_mul_surj_units_apply_inv (x : M) [decidable (is_unit x)] :
  surj_units x * (surj_units x)⁻¹ = 1 :=
begin
  by_cases h : is_unit x,
  { simp [surj_units_apply_is_unit h] },
  { simp [surj_units_apply_not_is_unit h] }
end

lemma left_inverse_surj_units [decidable_pred (is_unit : M → Prop)] :
  function.left_inverse (λ x, surj_units x) (coe : Mˣ → M) :=
λ _, by simp

lemma surj_units_surjective [decidable_pred (is_unit : M → Prop)] :
  function.surjective (λ x : M, surj_units x) :=
(left_inverse_surj_units).surjective

@[simp] lemma is_unit_inv_iff {γ : Type*} [division_monoid γ] {x : γ} :
  is_unit x⁻¹ ↔ is_unit x :=
begin
  split;
  intro h;
  simpa using h.inv
end

@[simp] lemma surj_units_inv {γ : Type*} [division_monoid γ] (x : γ)
  [decidable (is_unit x⁻¹)] [decidable (is_unit x)] :
  surj_units x⁻¹ = (surj_units x)⁻¹ :=
begin
  by_cases h : is_unit x,
  { rw [surj_units_apply_is_unit h.inv, surj_units_apply_is_unit h],
    ext,
    simp },
  { have h' : ¬ is_unit x⁻¹ := is_unit_inv_iff.not.mpr h,
    rw [surj_units_apply_not_is_unit h, surj_units_apply_not_is_unit h', inv_one] }
end
