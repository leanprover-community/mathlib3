/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import algebra.ordered_ring algebra.field

section linear_ordered_field
variables {α : Type*} [linear_ordered_field α] {a b c d : α}

def div_pos := @div_pos_of_pos_of_pos

lemma inv_pos {a : α} : 0 < a → 0 < a⁻¹ :=
by rw [inv_eq_one_div]; exact div_pos zero_lt_one

lemma inv_lt_zero {a : α} : a < 0 → a⁻¹ < 0 :=
by rw [inv_eq_one_div]; exact div_neg_of_pos_of_neg zero_lt_one

lemma one_le_div_iff_le (hb : 0 < b) : 1 ≤ a / b ↔ b ≤ a :=
⟨le_of_one_le_div a hb, one_le_div_of_le a hb⟩

lemma one_lt_div_iff_lt (hb : 0 < b) : 1 < a / b ↔ b < a :=
⟨lt_of_one_lt_div a hb, one_lt_div_of_lt a hb⟩

lemma div_le_one_iff_le (hb : 0 < b) : a / b ≤ 1 ↔ a ≤ b :=
le_iff_le_iff_lt_iff_lt.2 (one_lt_div_iff_lt hb)

lemma div_lt_one_iff_lt (hb : 0 < b) : a / b < 1 ↔ a < b :=
lt_iff_lt_of_le_iff_le (one_le_div_iff_le hb)

lemma le_div_iff (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b :=
⟨mul_le_of_le_div hc, le_div_of_mul_le hc⟩

lemma le_div_iff' (hc : 0 < c) : a ≤ b / c ↔ c * a ≤ b :=
by rw [mul_comm, le_div_iff hc]

lemma div_le_iff (hb : 0 < b) : a / b ≤ c ↔ a ≤ c * b :=
⟨le_mul_of_div_le hb, by rw [mul_comm]; exact div_le_of_le_mul hb⟩

lemma div_le_iff' (hb : 0 < b) : a / b ≤ c ↔ a ≤ b * c :=
by rw [mul_comm, div_le_iff hb]

lemma lt_div_iff (hc : 0 < c) : a < b / c ↔ a * c < b :=
⟨mul_lt_of_lt_div hc, lt_div_of_mul_lt hc⟩

lemma lt_div_iff' (hc : 0 < c) : a < b / c ↔ c * a < b :=
by rw [mul_comm, lt_div_iff hc]

lemma div_le_iff_of_neg (hc : c < 0) : b / c ≤ a ↔ a * c ≤ b :=
⟨mul_le_of_div_le_of_neg hc, div_le_of_mul_le_of_neg hc⟩

lemma div_lt_iff (hc : 0 < c) : b / c < a ↔ b < a * c :=
lt_iff_lt_of_le_iff_le (le_div_iff hc)

lemma div_lt_iff' (hc : 0 < c) : b / c < a ↔ b < c * a :=
by rw [mul_comm, div_lt_iff hc]

lemma div_lt_iff_of_neg (hc : c < 0) : b / c < a ↔ a * c < b :=
⟨mul_lt_of_gt_div_of_neg hc, div_lt_of_mul_gt_of_neg hc⟩

lemma inv_le_inv (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
by rw [inv_eq_one_div, div_le_iff ha,
       ← div_eq_inv_mul, one_le_div_iff_le hb]

lemma inv_le (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b ↔ b⁻¹ ≤ a :=
by rw [← inv_le_inv hb (inv_pos ha), division_ring.inv_inv (ne_of_gt ha)]

lemma le_inv (ha : 0 < a) (hb : 0 < b) : a ≤ b⁻¹ ↔ b ≤ a⁻¹ :=
by rw [← inv_le_inv (inv_pos hb) ha, division_ring.inv_inv (ne_of_gt hb)]

lemma one_div_le_one_div (ha : 0 < a) (hb : 0 < b) : 1 / a ≤ 1 / b ↔ b ≤ a :=
by simpa [one_div_eq_inv] using inv_le_inv ha hb

lemma inv_lt_inv (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a :=
lt_iff_lt_of_le_iff_le (inv_le_inv hb ha)

lemma inv_lt (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b ↔ b⁻¹ < a :=
lt_iff_lt_of_le_iff_le (le_inv hb ha)

lemma lt_inv (ha : 0 < a) (hb : 0 < b) : a < b⁻¹ ↔ b < a⁻¹ :=
lt_iff_lt_of_le_iff_le (inv_le hb ha)

lemma one_div_lt_one_div (ha : 0 < a) (hb : 0 < b) : 1 / a < 1 / b ↔ b < a :=
lt_iff_lt_of_le_iff_le (one_div_le_one_div hb ha)

def div_nonneg := @div_nonneg_of_nonneg_of_pos

lemma div_lt_div_right (hc : 0 < c) : a / c < b / c ↔ a < b :=
⟨lt_imp_lt_of_le_imp_le (λ h, div_le_div_of_le_of_pos h hc),
 λ h, div_lt_div_of_lt_of_pos h hc⟩

lemma div_le_div_right (hc : 0 < c) : a / c ≤ b / c ↔ a ≤ b :=
le_iff_le_iff_lt_iff_lt.2 (div_lt_div_right hc)

lemma div_lt_div_right_of_neg (hc : c < 0) : a / c < b / c ↔ b < a :=
⟨lt_imp_lt_of_le_imp_le (λ h, div_le_div_of_le_of_neg h hc),
 λ h, div_lt_div_of_lt_of_neg h hc⟩

lemma div_le_div_right_of_neg (hc : c < 0) : a / c ≤ b / c ↔ b ≤ a :=
le_iff_le_iff_lt_iff_lt.2 (div_lt_div_right_of_neg hc)

lemma div_lt_div_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b < a / c ↔ c < b :=
(mul_lt_mul_left ha).trans (inv_lt_inv hb hc)

lemma div_le_div_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b ≤ a / c ↔ c ≤ b :=
le_iff_le_iff_lt_iff_lt.2 (div_lt_div_left ha hc hb)

lemma div_lt_div_iff (b0 : 0 < b) (d0 : 0 < d) :
  a / b < c / d ↔ a * d < c * b :=
by rw [lt_div_iff d0, div_mul_eq_mul_div, div_lt_iff b0]

lemma div_lt_div (hac : a < c) (hbd : d ≤ b) (c0 : 0 ≤ c) (d0 : 0 < d) :
  a / b < c / d :=
(div_lt_div_iff (lt_of_lt_of_le d0 hbd) d0).2 (mul_lt_mul hac hbd d0 c0)

lemma div_lt_div' (hac : a ≤ c) (hbd : d < b) (c0 : 0 < c) (d0 : 0 < d) :
  a / b < c / d :=
(div_lt_div_iff (lt_trans d0 hbd) d0).2 (mul_lt_mul' hac hbd (le_of_lt d0) c0)

lemma half_pos {a : α} (h : 0 < a) : 0 < a / 2 := div_pos h two_pos

lemma one_half_pos : (0:α) < 1 / 2 := half_pos zero_lt_one

def half_lt_self := @div_two_lt_of_pos

lemma one_half_lt_one : (1 / 2 : α) < 1 := half_lt_self zero_lt_one

lemma ivl_translate : (λx, x + c) '' {r:α | a ≤ r ∧ r ≤ b } = {r:α | a + c ≤ r ∧ r ≤ b + c} :=
calc (λx, x + c) '' {r | a ≤ r ∧ r ≤ b } = (λx, x - c) ⁻¹' {r | a ≤ r ∧ r ≤ b } :
    congr_fun (set.image_eq_preimage_of_inverse
      (assume a, add_sub_cancel a c) (assume b, sub_add_cancel b c)) _
  ... = {r | a + c ≤ r ∧ r ≤ b + c} :
    set.ext $ by simp [-sub_eq_add_neg, le_sub_iff_add_le, sub_le_iff_le_add]

lemma ivl_stretch (hc : 0 < c) : (λx, x * c) '' {r | a ≤ r ∧ r ≤ b } = {r | a * c ≤ r ∧ r ≤ b * c} :=
calc (λx, x * c) '' {r | a ≤ r ∧ r ≤ b } = (λx, x / c) ⁻¹' {r | a ≤ r ∧ r ≤ b } :
    congr_fun (set.image_eq_preimage_of_inverse
      (assume a, mul_div_cancel _ $ ne_of_gt hc) (assume b, div_mul_cancel _ $ ne_of_gt hc)) _
  ... = {r | a * c ≤ r ∧ r ≤ b * c} :
    set.ext $ by simp [le_div_iff, div_le_iff, hc]

instance linear_ordered_field.to_densely_ordered [linear_ordered_field α] : densely_ordered α :=
{ dense := assume a₁ a₂ h, ⟨(a₁ + a₂) / 2,
  calc a₁ = (a₁ + a₁) / 2 : (add_self_div_two a₁).symm
    ... < (a₁ + a₂) / 2 : div_lt_div_of_lt_of_pos (add_lt_add_left h _) two_pos,
  calc (a₁ + a₂) / 2 < (a₂ + a₂) / 2 : div_lt_div_of_lt_of_pos (add_lt_add_right h _) two_pos
    ... = a₂ : add_self_div_two a₂⟩ }

instance linear_ordered_field.to_no_top_order [linear_ordered_field α] : no_top_order α :=
{ no_top := assume a, ⟨a + 1, lt_add_of_le_of_pos (le_refl a) zero_lt_one ⟩ }

instance linear_ordered_field.to_no_bot_order [linear_ordered_field α] : no_bot_order α :=
{ no_bot := assume a, ⟨a + -1,
    add_lt_of_le_of_neg (le_refl _) (neg_lt_of_neg_lt $ by simp [zero_lt_one]) ⟩ }

lemma inv_lt_one {a : α} (ha : 1 < a) : a⁻¹ < 1 :=
by rw [inv_eq_one_div]; exact div_lt_of_mul_lt_of_pos (lt_trans zero_lt_one ha) (by simp *)

lemma one_lt_inv (h₁ : 0 < a) (h₂ : a < 1) : 1 < a⁻¹ :=
by rw [inv_eq_one_div, lt_div_iff h₁]; simp [h₂]

lemma inv_le_one {a : α} (ha : 1 ≤ a) : a⁻¹ ≤ 1 :=
by rw [inv_eq_one_div]; exact div_le_of_le_mul (lt_of_lt_of_le zero_lt_one ha) (by simp *)

lemma mul_self_inj_of_nonneg {a b : α} (a0 : 0 ≤ a) (b0 : 0 ≤ b) : a * a = b * b ↔ a = b :=
(mul_self_eq_mul_self_iff a b).trans $ or_iff_left_of_imp $
λ h, by subst a; rw [le_antisymm (neg_nonneg.1 a0) b0, neg_zero]

end linear_ordered_field

section
variables {α : Type*} [discrete_linear_ordered_field α] (a b c : α)

lemma inv_pos' {a : α} : 0 < a⁻¹ ↔ 0 < a :=
⟨by rw [inv_eq_one_div]; exact pos_of_one_div_pos, inv_pos⟩

lemma inv_neg' {a : α} : a⁻¹ < 0 ↔ a < 0 :=
⟨by rw [inv_eq_one_div]; exact neg_of_one_div_neg, inv_lt_zero⟩

lemma inv_nonneg {a : α} : 0 ≤ a⁻¹ ↔ 0 ≤ a :=
le_iff_le_iff_lt_iff_lt.2 inv_neg'

lemma inv_nonpos {a : α} : a⁻¹ ≤ 0 ↔ a ≤ 0 :=
le_iff_le_iff_lt_iff_lt.2 inv_pos'

lemma abs_inv : abs a⁻¹ = (abs a)⁻¹ :=
have h : abs (1 / a) = 1 / abs a,
  begin rw [abs_div, abs_of_nonneg], exact zero_le_one end,
by simp [*] at *

lemma inv_neg : (-a)⁻¹ = -(a⁻¹) :=
if h : a = 0
then by simp [h, inv_zero]
else by rwa [inv_eq_one_div, inv_eq_one_div, div_neg_eq_neg_div]

lemma inv_le_inv_of_le {a b : α} (hb : 0 < b) (h : b ≤ a) : a⁻¹ ≤ b⁻¹ :=
begin
  rw [inv_eq_one_div, inv_eq_one_div],
  exact one_div_le_one_div_of_le hb h
end

lemma div_nonneg' {a b : α} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b :=
(lt_or_eq_of_le hb).elim (div_nonneg ha) (λ h, by simp [h.symm])

end
