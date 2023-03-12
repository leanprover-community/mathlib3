import algebra.hom.units

variables {M X : Type*} [monoid M] [decidable_pred (is_unit : M → Prop)]

@[simp] lemma is_unit_one_unit : (is_unit_one : is_unit (1 : M)).unit = 1 :=
units.ext $ by simp

@[simp] lemma units.unit_spec {x : Mˣ} : x.is_unit.unit = x :=
by ext; simp

-- Since this is noncomputable anyway, we put the `decidable (is_unit x)`
-- constraint as a `decidable_pred (is_unit : M → Prop)` to cover all the cases
-- which also turns this function into less-dependently typed,
-- allowsing for better unification elsewhere
noncomputable
def surj_units (x : M) : Mˣ := if h : is_unit x then h.unit else 1

instance group.decidable_is_unit {G : Type*} [group G] {x : G} : decidable (is_unit x) :=
is_true (group.is_unit x)

instance units.decidable_is_unit_coe {x : Mˣ} : decidable (is_unit (x : M)) :=
is_true (x.is_unit)

lemma surj_units_apply_is_unit {x : M} (hx : is_unit x) :
  surj_units x = hx.unit :=
dif_pos hx

lemma surj_units_apply_not_is_unit {x : M} (hx : ¬ is_unit x) :
  surj_units x = 1 :=
dif_neg hx

@[simp] lemma surj_units_apply_coe_units (x : Mˣ) :
  surj_units (x : M) = x :=
by simp only [surj_units_apply_is_unit x.is_unit, is_unit.unit_of_coe_units]

@[simp] lemma surj_units_apply_one :
  surj_units (1 : M) = 1 :=
by simp [surj_units_apply_is_unit is_unit_one]

@[simp] lemma coe_surj_units_apply_eq_iff {x : M} :
  (surj_units x : M) = x ↔ is_unit x :=
begin
  by_cases h : is_unit x,
  { simp [surj_units_apply_is_unit h, h] },
  { simp only [surj_units_apply_not_is_unit h, h, units.coe_one, iff_false],
    contrapose! h,
    simp [←h] }
end

lemma coe_surj_units_apply_is_unit {x : M} (hx : is_unit x) :
  (surj_units x : M) = x :=
coe_surj_units_apply_eq_iff.mpr hx

lemma surj_units_apply_inv_mul_surj_units_apply (x : M) :
  (surj_units x)⁻¹ * surj_units x = 1 :=
begin
  by_cases h : is_unit x,
  { simp [surj_units_apply_is_unit h] },
  { simp [surj_units_apply_not_is_unit h] }
end

lemma surj_units_apply_mul_surj_units_apply_inv (x : M) :
  surj_units x * (surj_units x)⁻¹ = 1 :=
begin
  by_cases h : is_unit x,
  { simp [surj_units_apply_is_unit h] },
  { simp [surj_units_apply_not_is_unit h] }
end

lemma left_inverse_surj_units : function.left_inverse surj_units (coe : Mˣ → M) :=
λ _, by simp

lemma surj_units_surjective : function.surjective (surj_units : M → Mˣ) :=
(left_inverse_surj_units).surjective

@[simp] lemma is_unit_inv_iff {γ : Type*} [division_monoid γ] {x : γ} :
  is_unit x⁻¹ ↔ is_unit x :=
begin
  split;
  intro h;
  simpa using h.inv
end

@[simp] lemma surj_units_inv {γ : Type*} [division_monoid γ] [decidable_pred (is_unit : γ → Prop)]
  (x : γ) : surj_units x⁻¹ = (surj_units x)⁻¹ :=
begin
  by_cases h : is_unit x,
  { rw [surj_units_apply_is_unit h.inv, surj_units_apply_is_unit h],
    ext,
    simp },
  { have h' : ¬ is_unit x⁻¹ := is_unit_inv_iff.not.mpr h,
    rw [surj_units_apply_not_is_unit h, surj_units_apply_not_is_unit h', inv_one] }
end
