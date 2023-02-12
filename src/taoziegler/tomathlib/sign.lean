import data.real.basic
import data.sign

open_locale big_operators

variables {α β : Type*}

protected lemma sign_type.mul_self_eq_one_iff {a : sign_type} : a * a = 1 ↔ a ≠ 0 := by dec_trivial!

protected lemma sign_type.is_unit {a : sign_type} (ha : a ≠ 0) : is_unit a :=
begin
  suffices : a * a = 1,
  { exact ⟨⟨a, a, this, this⟩, rfl⟩ },
  rwa sign_type.mul_self_eq_one_iff
end

section

lemma sign_type.is_unit_sign [mul_zero_one_class α] [linear_order α]
  {a : α} (ha : a ≠ 0) : is_unit (sign a) :=
begin
  rw ←sign_ne_zero at ha,
  exact sign_type.is_unit ha
end

protected lemma coe_sign_mul_self_eq_one_iff [mul_zero_one_class α] [has_distrib_neg α]
  [linear_order α] [nontrivial α] {a : α} : (sign a : α) * (sign a : α) = 1 ↔ a ≠ 0 :=
begin
  rcases lt_trichotomy a 0 with ha|ha|ha,
  { simp [ha, ha.ne], },
  { simp [ha] },
  { simp [ha, ha.ne'] }
end

end
section

variables [linear_ordered_field α] [@decidable_rel α (<)]
local attribute [instance] linear_ordered_add_comm_group.decidable_lt

@[simp] lemma inv_coe_sign (a : α) : ((sign a) : α)⁻¹ = sign a :=
begin
  rcases lt_trichotomy a 0 with ha|ha|ha;
  simp [ha, inv_neg]
end

end

section

variables [linear_ordered_ring α] [@decidable_rel α (<)]
local attribute [instance] linear_ordered_add_comm_group.decidable_lt

lemma coe_sign_is_unit {a : α} (ha : a ≠ 0) : is_unit (sign a : α) :=
by convert (sign_type.is_unit_sign ha).map (@sign_type.cast_hom α _ _)


@[simp] lemma sign_mul_abs (a : α) : (sign a : α) * | a | = a :=
begin
  rcases lt_trichotomy a 0 with ha|rfl|ha,
  { simp only [ha, sign_neg, sign_type.coe_neg_one, neg_mul, one_mul],
    rw [neg_eq_iff_neg_eq, eq_comm, abs_eq, neg_neg];
    simp [ha.le] },
  { simp only [abs_zero, mul_zero]},
  { simp only [ha, ha.le, sign_pos, sign_type.coe_one, one_mul, abs_eq_self] }
end

lemma sign_mul_eq_abs (a : α) : (sign a : α) * a = | a | :=
begin
  rcases eq_or_ne a 0 with rfl|ha,
  { simp },
  { rw [←(coe_sign_is_unit ha).mul_right_inj, ←mul_assoc, sign_mul_abs],
    convert one_mul a,
    convert coe_sign_mul_self_eq_one_iff.mpr ha }
end

end

namespace finset

@[simp] lemma pow_zero_eq_one_iff [monoid_with_zero α] [nontrivial α] {n : ℕ} :
  (0 : α) ^ n = 1 ↔ n = 0 :=
by { cases n; simp }

lemma prod_abs {α β : Type*} [linear_ordered_comm_ring α] [@decidable_rel α (<)]
  (s : finset β) (f : β → α) :
  ∏ i in s, | f i | = (- 1) ^ (s.filter (λ i, f i < 0)).card * ∏ i in s, f i :=
begin
  by_cases h : ∃ i ∈ s, f i = 0,
  { obtain ⟨i, hs, hi⟩ := h,
    rw [prod_eq_zero hs, prod_eq_zero hs];
    simp [hi] },
  push_neg at h,
  suffices : (- 1 : α) ^ (filter (λ (i : β), f i < 0) s).card = ∏ i in s, sign (f i),
  { simp [this, ←prod_mul_distrib, sign_mul_eq_abs] },
  simp_rw [sign_apply, apply_ite (coe : sign_type → α), prod_ite, filter_filter, prod_const],
  simp only [sign_type.coe_one, sign_type.coe_zero, sign_type.coe_neg_one, not_lt, one_pow,
             one_mul],
  rw [eq_comm],
  convert @mul_one α _ _,
  { simp only [filter_eq_empty_iff, pow_zero_eq_one_iff, card_eq_zero, not_and, not_le],
    intros i hs hn,
    exact lt_of_le_of_ne hn (h _ hs) },
  { ext,
    simpa using le_of_lt }
end

lemma sign_prod_abs {α β : Type*} [linear_ordered_comm_ring α] [@decidable_rel α (<)]
  (s : finset β) (f : β → α) :
  (- 1 : α) ^ (s.filter (λ i, f i < 0)).card * ∏ i in s, | f i | = ∏ i in s, f i :=
by simp [prod_abs, ←mul_assoc, ←mul_pow]

end finset
