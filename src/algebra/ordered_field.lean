/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import algebra.ordered_ring
import algebra.field

section linear_ordered_field
variables {α : Type*} [linear_ordered_field α] {a b c d : α}

lemma div_pos : 0 < a → 0 < b → 0 < a / b := div_pos_of_pos_of_pos

@[simp] lemma inv_pos : ∀ {a : α}, 0 < a⁻¹ ↔ 0 < a :=
suffices ∀ a : α, 0 < a → 0 < a⁻¹,
from λ a, ⟨λ h, inv_inv'' a ▸ this _ h, this a⟩,
λ a, one_div_eq_inv a ▸ one_div_pos_of_pos

@[simp] lemma inv_lt_zero : ∀ {a : α}, a⁻¹ < 0 ↔ a < 0 :=
suffices ∀ a : α, a < 0 → a⁻¹ < 0,
from λ a, ⟨λ h, inv_inv'' a ▸ this _ h, this a⟩,
λ a, one_div_eq_inv a ▸ one_div_neg_of_neg

@[simp] lemma inv_nonneg {a : α} : 0 ≤ a⁻¹ ↔ 0 ≤ a :=
le_iff_le_iff_lt_iff_lt.2 inv_lt_zero

@[simp] lemma inv_nonpos {a : α} : a⁻¹ ≤ 0 ↔ a ≤ 0 :=
le_iff_le_iff_lt_iff_lt.2 inv_pos

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

lemma le_div_iff_of_neg (hc : c < 0) : a ≤ b / c ↔ b ≤ a * c :=
by rw [← neg_neg c, mul_neg_eq_neg_mul_symm, div_neg, le_neg,
    div_le_iff (neg_pos.2 hc), neg_mul_eq_neg_mul_symm]

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
by rw [← inv_le_inv hb (inv_pos.2 ha), inv_inv']

lemma le_inv (ha : 0 < a) (hb : 0 < b) : a ≤ b⁻¹ ↔ b ≤ a⁻¹ :=
by rw [← inv_le_inv (inv_pos.2 hb) ha, inv_inv']

lemma one_div_le_one_div (ha : 0 < a) (hb : 0 < b) : 1 / a ≤ 1 / b ↔ b ≤ a :=
by simpa [one_div_eq_inv] using inv_le_inv ha hb

lemma inv_lt_inv (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a :=
lt_iff_lt_of_le_iff_le (inv_le_inv hb ha)

lemma inv_lt (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b ↔ b⁻¹ < a :=
lt_iff_lt_of_le_iff_le (le_inv hb ha)

lemma one_div_lt (ha : 0 < a) (hb : 0 < b) : 1 / a < b ↔ 1 / b < a :=
(one_div_eq_inv a).symm ▸ (one_div_eq_inv b).symm ▸ inv_lt ha hb

lemma lt_inv (ha : 0 < a) (hb : 0 < b) : a < b⁻¹ ↔ b < a⁻¹ :=
lt_iff_lt_of_le_iff_le (inv_le hb ha)

lemma one_div_lt_one_div (ha : 0 < a) (hb : 0 < b) : 1 / a < 1 / b ↔ b < a :=
lt_iff_lt_of_le_iff_le (one_div_le_one_div hb ha)

lemma div_nonneg : 0 ≤ a → 0 < b → 0 ≤ a / b := div_nonneg_of_nonneg_of_pos

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

lemma div_le_div_iff (b0 : 0 < b) (d0 : 0 < d) : a / b ≤ c / d ↔ a * d ≤ c * b :=
by rw [le_div_iff d0, div_mul_eq_mul_div, div_le_iff b0]

lemma div_lt_div (hac : a < c) (hbd : d ≤ b) (c0 : 0 ≤ c) (d0 : 0 < d) :
  a / b < c / d :=
(div_lt_div_iff (lt_of_lt_of_le d0 hbd) d0).2 (mul_lt_mul hac hbd d0 c0)

lemma div_lt_div' (hac : a ≤ c) (hbd : d < b) (c0 : 0 < c) (d0 : 0 < d) :
  a / b < c / d :=
(div_lt_div_iff (lt_trans d0 hbd) d0).2 (mul_lt_mul' hac hbd (le_of_lt d0) c0)

lemma monotone.div_const {β : Type*} [preorder β] {f : β → α} (hf : monotone f)
  {c : α} (hc : 0 ≤ c) :
  monotone (λ x, (f x) / c) :=
hf.mul_const (inv_nonneg.2 hc)

lemma strict_mono.div_const {β : Type*} [preorder β] {f : β → α} (hf : strict_mono f)
  {c : α} (hc : 0 < c) :
  strict_mono (λ x, (f x) / c) :=
hf.mul_const (inv_pos.2 hc)

lemma half_pos {a : α} (h : 0 < a) : 0 < a / 2 := div_pos h two_pos

lemma one_half_pos : (0:α) < 1 / 2 := half_pos zero_lt_one

lemma half_lt_self : 0 < a → a / 2 < a := div_two_lt_of_pos

lemma one_half_lt_one : (1 / 2 : α) < 1 := half_lt_self zero_lt_one

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_field.to_densely_ordered : densely_ordered α :=
{ dense := assume a₁ a₂ h, ⟨(a₁ + a₂) / 2,
  calc a₁ = (a₁ + a₁) / 2 : (add_self_div_two a₁).symm
    ... < (a₁ + a₂) / 2 : div_lt_div_of_lt_of_pos (add_lt_add_left h _) two_pos,
  calc (a₁ + a₂) / 2 < (a₂ + a₂) / 2 : div_lt_div_of_lt_of_pos (add_lt_add_right h _) two_pos
    ... = a₂ : add_self_div_two a₂⟩ }

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_field.to_no_top_order : no_top_order α :=
{ no_top := assume a, ⟨a + 1, lt_add_of_le_of_pos (le_refl a) zero_lt_one ⟩ }

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_field.to_no_bot_order : no_bot_order α :=
{ no_bot := assume a, ⟨a + -1,
    add_lt_of_le_of_neg (le_refl _) (neg_lt_of_neg_lt $ by simp [zero_lt_one]) ⟩ }

lemma inv_lt_one {a : α} (ha : 1 < a) : a⁻¹ < 1 :=
by rw [inv_eq_one_div]; exact div_lt_of_mul_lt_of_pos (lt_trans zero_lt_one ha) (by simp *)

lemma one_lt_inv (h₁ : 0 < a) (h₂ : a < 1) : 1 < a⁻¹ :=
by rw [inv_eq_one_div, lt_div_iff h₁]; simp [h₂]

lemma inv_le_one {a : α} (ha : 1 ≤ a) : a⁻¹ ≤ 1 :=
by rw [inv_eq_one_div]; exact div_le_of_le_mul (lt_of_lt_of_le zero_lt_one ha) (by simp *)

lemma one_le_inv {x : α} (hx0 : 0 < x) (hx : x ≤ 1) : 1 ≤ x⁻¹ :=
le_of_mul_le_mul_left (by simpa [mul_inv_cancel (ne.symm (ne_of_lt hx0))]) hx0

lemma mul_self_inj_of_nonneg {a b : α} (a0 : 0 ≤ a) (b0 : 0 ≤ b) : a * a = b * b ↔ a = b :=
(mul_self_eq_mul_self_iff a b).trans $ or_iff_left_of_imp $
λ h, by subst a; rw [le_antisymm (neg_nonneg.1 a0) b0, neg_zero]

lemma div_le_div_of_le_left {a b c : α} (ha : 0 ≤ a) (hc : 0 < c) (h : c ≤ b) :
  a / b ≤ a / c :=
by haveI := classical.dec_eq α; exact
if ha0 : a = 0 then by simp [ha0]
else (div_le_div_left (lt_of_le_of_ne ha (ne.symm ha0)) (lt_of_lt_of_le hc h) hc).2 h

lemma inv_le_inv_of_le {a b : α} (hb : 0 < b) (h : b ≤ a) : a⁻¹ ≤ b⁻¹ :=
begin
  rw [inv_eq_one_div, inv_eq_one_div],
  exact one_div_le_one_div_of_le hb h
end

lemma div_nonneg' {a b : α} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b :=
(lt_or_eq_of_le hb).elim (div_nonneg ha) (λ h, by simp [h.symm])

lemma div_le_div_of_le_of_nonneg {a b c : α} (hab : a ≤ b) (hc : 0 ≤ c) :
  a / c ≤ b / c :=
mul_le_mul_of_nonneg_right hab (inv_nonneg.2 hc)


end linear_ordered_field

namespace nat

variables {α : Type*} [linear_ordered_field α]

lemma inv_pos_of_nat {n : ℕ} : 0 < ((n : α) + 1)⁻¹ :=
inv_pos.2 $ add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one

lemma one_div_pos_of_nat {n : ℕ} : 0 < 1 / ((n : α) + 1) :=
by { rw one_div_eq_inv, exact inv_pos_of_nat }

lemma one_div_le_one_div {n m : ℕ} (h : n ≤ m) : 1 / ((m : α) + 1) ≤ 1 / ((n : α) + 1) :=
by { refine one_div_le_one_div_of_le _ _, exact nat.cast_add_one_pos _, simpa }

lemma one_div_lt_one_div {n m : ℕ} (h : n < m) : 1 / ((m : α) + 1) < 1 / ((n : α) + 1) :=
by { refine one_div_lt_one_div_of_lt _ _, exact nat.cast_add_one_pos _, simpa }

end nat

section
variables {α : Type*} [discrete_linear_ordered_field α] (a b c : α)

lemma abs_inv : abs a⁻¹ = (abs a)⁻¹ :=
have h : abs (1 / a) = 1 / abs a,
  begin rw [abs_div, abs_of_nonneg], exact zero_le_one end,
by simp [*] at *

end
