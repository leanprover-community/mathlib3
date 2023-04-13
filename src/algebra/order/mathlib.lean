/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.order.module

/-!
# To move

Feel free to open PRs!
-/

section
variables {α : Type*} [comm_group α] [linear_order α] [covariant_class α α (*) (≤)] {a b c d : α}

@[to_additive] lemma lt_or_lt_of_div_lt_div : a / d < b / c → a < b ∨ c < d :=
by { contrapose!, exact λ h, div_le_div'' h.1 h.2 }

end

section
variables {α β γ : Type*}

@[to_additive]
instance order_dual.smul_comm_class [has_smul β γ] [has_smul α γ] [smul_comm_class α β γ] :
  smul_comm_class αᵒᵈ β γ :=
‹smul_comm_class α β γ›

@[to_additive]
instance order_dual.smul_comm_class' [has_smul β γ] [has_smul α γ] [smul_comm_class α β γ] :
  smul_comm_class α βᵒᵈ γ :=
‹smul_comm_class α β γ›

@[to_additive]
instance order_dual.smul_comm_class'' [has_smul β γ] [has_smul α γ] [smul_comm_class α β γ] :
  smul_comm_class α β γᵒᵈ :=
‹smul_comm_class α β γ›

@[to_additive]
instance order_dual.is_scalar_tower [has_smul α β] [has_smul β γ] [has_smul α γ]
  [is_scalar_tower α β γ] : is_scalar_tower αᵒᵈ β γ :=
‹is_scalar_tower α β γ›

@[to_additive]
instance order_dual.is_scalar_tower' [has_smul α β] [has_smul β γ] [has_smul α γ]
  [is_scalar_tower α β γ] : is_scalar_tower α βᵒᵈ γ :=
‹is_scalar_tower α β γ›

@[to_additive]
instance order_dual.is_scalar_tower'' [has_smul α β] [has_smul β γ] [has_smul α γ]
  [is_scalar_tower α β γ] : is_scalar_tower α β γᵒᵈ :=
‹is_scalar_tower α β γ›

end

section
variables {α β : Type*} [ordered_ring α] [ordered_add_comm_group β] [module α β] [ordered_smul α β]
  {a a₁ a₂ : α} {b b₁ b₂ : β}

lemma smul_le_smul_of_nonneg_left (h : b₁ ≤ b₂) (ha : 0 ≤ a) : a • b₁ ≤ a • b₂ :=
smul_le_smul_of_nonneg h ha

lemma smul_le_smul_of_nonneg_right (h : a₁ ≤ a₂) (hb : 0 ≤ b) : a₁ • b ≤ a₂ • b :=
by { rw [←sub_nonneg, ←sub_smul], exact smul_nonneg (sub_nonneg.2 h) hb }

lemma smul_le_smul (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (h₁ : 0 ≤ b₁) (h₂ : 0 ≤ a₂) : a₁ • b₁ ≤ a₂ • b₂ :=
(smul_le_smul_of_nonneg_right ha h₁).trans $ smul_le_smul_of_nonneg_left hb h₂

end

section
variables {ι α β : Type*} [linear_ordered_ring α] [linear_ordered_add_comm_group β] [module α β]
  [ordered_smul α β] {f : ι → α} {g : ι → β} {s : set ι} {a a₁ a₂ : α} {b b₁ b₂ : β}

-- TODO: Rename `nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nnonneg` to
-- `nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg`
lemma nonneg_and_nonneg_or_nonpos_and_nonpos_of_smul_nonneg (hab : 0 ≤ a • b) :
  0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 :=
begin
  simp only [decidable.or_iff_not_and_not, not_and, not_le],
  refine λ ab nab, hab.not_lt _,
  obtain ha | rfl | ha := lt_trichotomy 0 a,
  exacts [smul_neg_of_pos_of_neg ha (ab ha.le), ((ab le_rfl).asymm (nab le_rfl)).elim,
    smul_neg_of_neg_of_pos ha (nab ha.le)],
end

lemma smul_nonneg_iff : 0 ≤ a • b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 :=
⟨nonneg_and_nonneg_or_nonpos_and_nonpos_of_smul_nonneg,
  λ h, h.elim (and_imp.2 smul_nonneg) (and_imp.2 smul_nonneg_of_nonpos_of_nonpos)⟩

lemma smul_nonpos_iff : a • b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b :=
by rw [←neg_nonneg, ←smul_neg, smul_nonneg_iff, neg_nonneg, neg_nonpos]

lemma smul_nonneg_iff_pos_imp_nonneg : 0 ≤ a • b ↔ (0 < a → 0 ≤ b) ∧ (0 < b → 0 ≤ a) :=
begin
  refine smul_nonneg_iff.trans _,
  simp_rw [←not_le, ←or_iff_not_imp_left],
  have := le_total a 0,
  have := le_total b 0,
  tauto,
end

lemma smul_nonneg_iff_neg_imp_nonpos : 0 ≤ a • b ↔ (a < 0 → b ≤ 0) ∧ (b < 0 → a ≤ 0) :=
by rw [←neg_smul_neg, smul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

lemma smul_nonpos_iff_pos_imp_nonpos : a • b ≤ 0 ↔ (0 < a → b ≤ 0) ∧ (b < 0 → 0 ≤ a) :=
by rw [←neg_nonneg, ←smul_neg, smul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

lemma smul_nonpos_iff_neg_imp_nonneg : a • b ≤ 0 ↔ (a < 0 → 0 ≤ b) ∧ (0 < b → a ≤ 0) :=
by rw [←neg_nonneg, ←neg_smul, smul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

end

section
variables {ι α : Type*} [linear_ordered_ring α] {f g : ι → α} {s : set ι} {a b c d : α}

lemma mul_nonneg_iff_pos_imp_nonneg : 0 ≤ a * b ↔ (0 < a → 0 ≤ b) ∧ (0 < b → 0 ≤ a) :=
begin
  refine mul_nonneg_iff.trans _,
  simp_rw [←not_le, ←or_iff_not_imp_left],
  have := le_total a 0,
  have := le_total b 0,
  tauto,
end

lemma mul_nonneg_iff_neg_imp_nonpos : 0 ≤ a * b ↔ (a < 0 → b ≤ 0) ∧ (b < 0 → a ≤ 0) :=
by rw [←neg_mul_neg, mul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

lemma mul_nonpos_iff_pos_imp_nonpos : a * b ≤ 0 ↔ (0 < a → b ≤ 0) ∧ (b < 0 → 0 ≤ a) :=
by rw [←neg_nonneg, ←mul_neg, mul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

lemma mul_nonpos_iff_neg_imp_nonneg : a * b ≤ 0 ↔ (a < 0 → 0 ≤ b) ∧ (0 < b → a ≤ 0) :=
by rw [←neg_nonneg, ←neg_mul, mul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

end
