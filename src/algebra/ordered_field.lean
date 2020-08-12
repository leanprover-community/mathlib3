/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro
-/
import algebra.ordered_ring
import algebra.field

set_option default_priority 100 -- see Note [default priority]
set_option old_structure_cmd true

variable {α : Type*}

@[protect_proj] class linear_ordered_field (α : Type*) extends linear_ordered_comm_ring α, field α

section linear_ordered_field
variables [linear_ordered_field α] {a b c d e : α}

@[simp] lemma inv_pos : 0 < a⁻¹ ↔ 0 < a :=
suffices ∀ a : α, 0 < a → 0 < a⁻¹,
from ⟨λ h, inv_inv' a ▸ this _ h, this a⟩,
assume a ha, flip lt_of_mul_lt_mul_left (le_of_lt ha) $ by simp [ne_of_gt ha, zero_lt_one]

@[simp] lemma inv_nonneg : 0 ≤ a⁻¹ ↔ 0 ≤ a :=
by simp only [le_iff_eq_or_lt, inv_pos, zero_eq_inv]

@[simp] lemma inv_lt_zero : a⁻¹ < 0 ↔ a < 0 :=
by simp only [← not_le, inv_nonneg]

@[simp] lemma inv_nonpos : a⁻¹ ≤ 0 ↔ a ≤ 0 :=
by simp only [← not_lt, inv_pos]

lemma one_div_pos : 0 < 1 / a ↔ 0 < a :=
inv_eq_one_div a ▸ inv_pos

lemma one_div_neg : 1 / a < 0 ↔ a < 0 :=
inv_eq_one_div a ▸ inv_lt_zero

lemma one_div_nonneg : 0 ≤ 1 / a ↔ 0 ≤ a :=
inv_eq_one_div a ▸ inv_nonneg

lemma one_div_nonpos : 1 / a ≤ 0 ↔ a ≤ 0 :=
inv_eq_one_div a ▸ inv_nonpos

lemma div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b :=
mul_pos ha (inv_pos.2 hb)

lemma div_pos_of_neg_of_neg (ha : a < 0) (hb : b < 0) : 0 < a / b :=
mul_pos_of_neg_of_neg ha (inv_lt_zero.2 hb)

lemma div_neg_of_neg_of_pos (ha : a < 0) (hb : 0 < b) : a / b < 0 :=
mul_neg_of_neg_of_pos ha (inv_pos.2 hb)

lemma div_neg_of_pos_of_neg (ha : 0 < a) (hb : b < 0) : a / b < 0 :=
mul_neg_of_pos_of_neg ha (inv_lt_zero.2 hb)

lemma div_nonneg (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b :=
mul_nonneg ha (inv_nonneg.2 hb)

lemma div_nonneg_of_nonpos (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a / b :=
mul_nonneg_of_nonpos_of_nonpos ha (inv_nonpos.2 hb)

lemma div_nonpos_of_nonpos_of_nonneg (ha : a ≤ 0) (hb : 0 ≤ b) : a / b ≤ 0 :=
mul_nonpos_of_nonpos_of_nonneg ha (inv_nonneg.2 hb)

lemma div_nonpos_of_nonneg_of_nonpos (ha : 0 ≤ a) (hb : b ≤ 0) : a / b ≤ 0 :=
mul_nonpos_of_nonneg_of_nonpos ha (inv_nonpos.2 hb)

lemma one_le_div_of_le (a : α) {b : α} (hb : 0 < b) (h : b ≤ a) : 1 ≤ a / b :=
have hb'   : b ≠ 0,     from ne_of_gt hb,
have hbinv : 0 < 1 / b, from one_div_pos.2 hb,
calc
   1  = b * (1 / b)  : eq.symm (mul_one_div_cancel hb')
   ... ≤ a * (1 / b) : mul_le_mul_of_nonneg_right h (le_of_lt hbinv)
   ... = a / b       : eq.symm $ div_eq_mul_one_div a b

lemma le_of_one_le_div (a : α) {b : α} (hb : 0 < b) (h : 1 ≤ a / b) : b ≤ a :=
have hb'   : b ≠ 0,     from (ne_of_lt hb).symm,
calc
   b   ≤ b * (a / b) : le_mul_of_one_le_right (le_of_lt hb) h
   ... = a           : by rw [mul_div_cancel' _ hb']

lemma one_lt_div_of_lt (a : α) {b : α} (hb : 0 < b) (h : b < a) : 1 < a / b :=
have hb' : b ≠ 0, from (ne_of_lt hb).symm,
have hbinv : 0 < 1 / b, from  one_div_pos.2 hb, calc
     1 = b * (1 / b) : eq.symm (mul_one_div_cancel hb')
   ... < a * (1 / b) : mul_lt_mul_of_pos_right h hbinv
   ... = a / b       : eq.symm $ div_eq_mul_one_div a b

lemma lt_of_one_lt_div (a : α) {b : α} (hb : 0 < b) (h : 1 < a / b) : b < a :=
have hb' : b ≠ 0, from (ne_of_lt hb).symm,
calc
   b   < b * (a / b) : lt_mul_of_one_lt_right hb h
   ... = a           : by rw [mul_div_cancel' _ hb']

-- the following lemmas amount to four iffs, for <, ≤, ≥, >.

lemma mul_le_of_le_div (hc : 0 < c) (h : a ≤ b / c) : a * c ≤ b :=
div_mul_cancel b (ne.symm (ne_of_lt hc)) ▸ mul_le_mul_of_nonneg_right h (le_of_lt hc)

lemma le_div_of_mul_le (hc : 0 < c) (h : a * c ≤ b) : a ≤ b / c :=
calc
    a   = a * c * (1 / c) : mul_mul_div a (ne.symm (ne_of_lt hc))
    ... ≤ b * (1 / c)     : mul_le_mul_of_nonneg_right h (le_of_lt (one_div_pos.2 hc))
    ... = b / c           : eq.symm $ div_eq_mul_one_div b c

lemma mul_lt_of_lt_div (hc : 0 < c) (h : a < b / c) : a * c < b :=
div_mul_cancel b (ne.symm (ne_of_lt hc)) ▸ mul_lt_mul_of_pos_right h hc

lemma lt_div_of_mul_lt (hc : 0 < c) (h : a * c < b) : a < b / c :=
calc
   a   = a * c * (1 / c) : mul_mul_div a (ne.symm (ne_of_lt hc))
   ... < b * (1 / c)     : mul_lt_mul_of_pos_right h (one_div_pos.2 hc)
   ... = b / c           : eq.symm $ div_eq_mul_one_div b c

lemma mul_le_of_neg_of_div_le (hc : c < 0) (h : b / c ≤ a) : a * c ≤ b :=
div_mul_cancel b (ne_of_lt hc) ▸ mul_le_mul_of_nonpos_right h (le_of_lt hc)

lemma div_le_of_neg_of_mul_le (hc : c < 0) (h : a * c ≤ b) : b / c ≤ a :=
calc
   a   = a * c * (1 / c) : mul_mul_div a (ne_of_lt hc)
    ... ≥ b * (1 / c)     : mul_le_mul_of_nonpos_right h (le_of_lt (one_div_neg.2 hc))
    ... = b / c           : eq.symm $ div_eq_mul_one_div b c

lemma mul_lt_of_neg_of_div_lt (hc : c < 0) (h : b / c < a) : a * c < b :=
div_mul_cancel b (ne_of_lt hc) ▸ mul_lt_mul_of_neg_right h hc

lemma div_lt_of_pos_of_lt_mul (hc : 0 < c) (h : b < a * c) : b / c < a :=
calc
   a   = a * c * (1 / c) : mul_mul_div a (ne_of_gt hc)
   ... > b * (1 / c)     : mul_lt_mul_of_pos_right h (one_div_pos.2 hc)
   ... = b / c           : eq.symm $ div_eq_mul_one_div b c

lemma div_lt_of_neg_of_mul_lt (hc : c < 0) (h : a * c < b) : b / c < a :=
calc
   a   = a * c * (1 / c) : mul_mul_div a (ne_of_lt hc)
   ... > b * (1 / c)     : mul_lt_mul_of_neg_right h (one_div_neg.2 hc)
   ... = b / c           : eq.symm $ div_eq_mul_one_div b c

lemma div_le_of_le_mul (hb : 0 < b) (h : a ≤ b * c) : a / b ≤ c :=
calc
   a / b = a * (1 / b)       : div_eq_mul_one_div a b
     ... ≤ (b * c) * (1 / b) : mul_le_mul_of_nonneg_right h (le_of_lt (one_div_pos.2 hb))
     ... = (b * c) / b       : eq.symm $ div_eq_mul_one_div (b * c) b
     ... = c                 : by rw [mul_div_cancel_left _ (ne.symm (ne_of_lt hb))]

lemma le_mul_of_div_le (hc : 0 < c) (h : a / c ≤ b) : a ≤ b * c :=
calc
   a = a / c * c : by rw (div_mul_cancel _ (ne.symm (ne_of_lt hc)))
 ... ≤ b * c     : mul_le_mul_of_nonneg_right h (le_of_lt hc)

  -- following these in the isabelle file, there are 8 biconditionals for the above with - signs
  -- skipping for now

lemma mul_sub_mul_div_mul_neg_iff (hc : c ≠ 0) (hd : d ≠ 0) :
  (a * d - b * c) / (c * d) < 0 ↔ a / c < b / d :=
by rw [mul_comm b c, ← div_sub_div _ _ hc hd, sub_lt_zero]

alias mul_sub_mul_div_mul_neg_iff ↔ div_lt_div_of_mul_sub_mul_div_neg  mul_sub_mul_div_mul_neg

lemma mul_sub_mul_div_mul_nonpos_iff (hc : c ≠ 0) (hd : d ≠ 0) :
      (a * d - b * c) / (c * d) ≤ 0 ↔ a / c ≤ b / d :=
by rw [mul_comm b c, ← div_sub_div _ _ hc hd, sub_nonpos]

alias mul_sub_mul_div_mul_nonpos_iff ↔
  div_le_div_of_mul_sub_mul_div_nonpos mul_sub_mul_div_mul_nonpos

lemma div_lt_div_of_pos_of_lt (hc : 0 < c) (h : a < b) : a / c < b / c :=
begin
  intros,
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c],
  exact mul_lt_mul_of_pos_right h (one_div_pos.2 hc)
end

lemma div_le_div_of_pos_of_le (hc : 0 < c) (h : a ≤ b) : a / c ≤ b / c :=
begin
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c],
  exact mul_le_mul_of_nonneg_right h (le_of_lt (one_div_pos.2 hc))
end

lemma div_lt_div_of_neg_of_lt (hc : c < 0) (h : b < a) : a / c < b / c :=
begin
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c],
  exact mul_lt_mul_of_neg_right h (one_div_neg.2 hc)
end

lemma div_le_div_of_neg_of_le (hc : c < 0) (h : b ≤ a) : a / c ≤ b / c :=
begin
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c],
  exact mul_le_mul_of_nonpos_right h (le_of_lt (one_div_neg.2 hc))
end

lemma add_halves (a : α) : a / 2 + a / 2 = a :=
by { rw [div_add_div_same, ← two_mul, mul_div_cancel_left], exact two_ne_zero }

lemma sub_self_div_two (a : α) : a - a / 2 = a / 2 :=
suffices a / 2 + a / 2 - a / 2 = a / 2, by rwa add_halves at this,
by rw [add_sub_cancel]

lemma add_midpoint {a b : α} (h : a < b) : a + (b - a) / 2 < b :=
begin
  rw [← div_sub_div_same, sub_eq_add_neg, add_comm (b/2), ← add_assoc, ← sub_eq_add_neg],
  apply add_lt_of_lt_sub_right,
  rw [sub_self_div_two, sub_self_div_two],
  apply div_lt_div_of_pos_of_lt (@two_pos α _) h
end

lemma div_two_sub_self (a : α) : a / 2 - a = - (a / 2) :=
suffices a / 2 - (a / 2 + a / 2) = - (a / 2), by rwa add_halves at this,
by rw [sub_add_eq_sub_sub, sub_self, zero_sub]

lemma add_self_div_two (a : α) : (a + a) / 2 = a :=
eq.symm
  (iff.mpr (eq_div_iff_mul_eq (ne_of_gt (add_pos (@zero_lt_one α _) zero_lt_one)))
           (begin unfold bit0, rw [left_distrib, mul_one] end))

lemma mul_le_mul_of_mul_div_le {a b c d : α} (h : a * (b / c) ≤ d) (hc : 0 < c) : b * a ≤ d * c :=
begin
  rw [← mul_div_assoc] at h, rw [mul_comm b],
  apply le_mul_of_div_le hc h
end

lemma div_two_lt_of_pos {a : α} (h : 0 < a) : a / 2 < a :=
have ha : a / 2 > 0, from div_pos h two_pos,
calc
      a / 2 < a / 2 + a / 2 : lt_add_of_pos_left _ ha
        ... = a             : add_halves a

lemma div_mul_le_div_mul_of_div_le_div_nonneg {a b c d e : α} (h : a / b ≤ c / d) (he : 0 ≤ e) :
  a / (b * e) ≤ c / (d * e) :=
begin
  rw [div_mul_eq_div_mul_one_div, div_mul_eq_div_mul_one_div],
  exact mul_le_mul_of_nonneg_right h (one_div_nonneg.2 he)
end

lemma exists_add_lt_and_pos_of_lt {a b : α} (h : b < a) : ∃ c : α, b + c < a ∧ 0 < c :=
begin
  apply exists.intro ((a - b) / (1 + 1)),
  split,
  {have h2 : a + a > (b + b) + (a - b),
    calc
      a + a > b + a             : add_lt_add_right h _
        ... = b + a + b - b     : by rw add_sub_cancel
        ... = b + b + a - b     : by simp [add_comm, add_left_comm]
        ... = (b + b) + (a - b) : by rw add_sub,
   have h3 : (a + a) / 2 > ((b + b) + (a - b)) / 2,
     exact div_lt_div_of_pos_of_lt two_pos h2,
   rw [one_add_one_eq_two, sub_eq_add_neg],
   rw [add_self_div_two, ← div_add_div_same, add_self_div_two, sub_eq_add_neg] at h3,
   exact h3},
  exact div_pos (sub_pos_of_lt h) two_pos
end

lemma le_of_forall_sub_le {a b : α} (h : ∀ ε > 0, b - ε ≤ a) : b ≤ a :=
begin
  contrapose! h,
  simpa only [and_comm ((0:α) < _), lt_sub_iff_add_lt, gt_iff_lt]
    using exists_add_lt_and_pos_of_lt h,
end

lemma one_div_lt_one_div_of_lt {a b : α} (ha : 0 < a) (h : a < b) : 1 / b < 1 / a :=
begin
  apply lt_div_of_mul_lt ha,
  rw [mul_comm, ← div_eq_mul_one_div],
  apply div_lt_of_pos_of_lt_mul (lt_trans ha h),
  rwa [one_mul]
end

lemma one_div_le_one_div_of_le {a b : α} (ha : 0 < a) (h : a ≤ b) : 1 / b ≤ 1 / a :=
(lt_or_eq_of_le h).elim
  (λ h, le_of_lt $ one_div_lt_one_div_of_lt ha h)
  (λ h, by rw [h])

lemma one_div_lt_one_div_of_neg_of_lt {a b : α} (hb : b < 0) (h : a < b) : 1 / b < 1 / a :=
begin
  apply div_lt_of_neg_of_mul_lt hb,
  rw [mul_comm, ← div_eq_mul_one_div],
  apply div_lt_of_neg_of_mul_lt (lt_trans h hb),
  rwa [one_mul]
end

lemma one_div_le_one_div_of_neg_of_le {a b : α} (hb : b < 0) (h : a ≤ b) : 1 / b ≤ 1 / a :=
(lt_or_eq_of_le h).elim
  (λ h, le_of_lt $ one_div_lt_one_div_of_neg_of_lt hb h)
  (λ h, by rw [h])

lemma le_of_one_div_le_one_div {a b : α} (h : 0 < a) (hl : 1 / a ≤ 1 / b) : b ≤ a :=
le_of_not_gt $ λ hn, not_lt_of_ge hl $ one_div_lt_one_div_of_lt h hn

lemma le_of_neg_of_one_div_le_one_div {a b : α} (h : b < 0) (hl : 1 / a ≤ 1 / b) : b ≤ a :=
le_of_not_gt $ λ hn, not_lt_of_ge hl $ one_div_lt_one_div_of_neg_of_lt h hn

lemma lt_of_one_div_lt_one_div {a b : α} (h : 0 < a) (hl : 1 / a < 1 / b) : b < a :=
lt_of_not_ge $ λ hn, not_le_of_gt hl $ one_div_le_one_div_of_le h hn

lemma lt_of_neg_of_one_div_lt_one_div {a b : α} (h : b < 0) (hl : 1 / a < 1 / b) : b < a :=
lt_of_not_ge $ λ hn, not_le_of_gt hl $ one_div_le_one_div_of_neg_of_le h hn

lemma one_div_le_of_pos_of_one_div_le {a b : α} (ha : 0 < a) (h : 1 / a ≤ b) : 1 / b ≤ a :=
begin
  rw [← one_div_one_div a],
  apply one_div_le_one_div_of_le _ h,
  apply one_div_pos.2 ha
end

lemma one_div_le_of_neg_of_one_div_le {a b : α} (hb : b < 0) (h : 1 / a ≤ b) : 1 / b ≤ a :=
le_of_not_gt $ λ hl, begin
  have : a < 0, from lt_trans hl (one_div_neg.2 hb),
  rw ← one_div_one_div a at hl,
  exact not_lt_of_ge h (lt_of_neg_of_one_div_lt_one_div hb hl)
end

lemma one_lt_one_div {a : α} (h1 : 0 < a) (h2 : a < 1) : 1 < 1 / a :=
suffices 1 / 1 < 1 / a, by rwa one_div_one at this,
one_div_lt_one_div_of_lt h1 h2

lemma one_le_one_div {a : α} (h1 : 0 < a) (h2 : a ≤ 1) : 1 ≤ 1 / a :=
suffices 1 / 1 ≤ 1 / a, by rwa one_div_one at this,
one_div_le_one_div_of_le h1 h2

lemma one_div_lt_neg_one {a : α} (h1 : a < 0) (h2 : -1 < a) : 1 / a < -1 :=
suffices 1 / a < 1 / -1, by rwa one_div_neg_one_eq_neg_one at this,
one_div_lt_one_div_of_neg_of_lt h1 h2

lemma one_div_le_neg_one {a : α} (h1 : a < 0) (h2 : -1 ≤ a) : 1 / a ≤ -1 :=
suffices 1 / a ≤ 1 / -1, by rwa one_div_neg_one_eq_neg_one at this,
one_div_le_one_div_of_neg_of_le h1 h2

lemma div_lt_div_of_pos_of_lt_of_pos (hb : 0 < b) (h : b < a) (hc : 0 < c) : c / a < c / b :=
begin
  apply lt_of_sub_neg,
  rw [div_eq_mul_one_div, div_eq_mul_one_div c b, ← mul_sub_left_distrib],
  apply mul_neg_of_pos_of_neg,
  exact hc,
  apply sub_neg_of_lt,
  apply one_div_lt_one_div_of_lt; assumption,
end

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
⟨mul_le_of_neg_of_div_le hc, div_le_of_neg_of_mul_le hc⟩

lemma le_div_iff_of_neg (hc : c < 0) : a ≤ b / c ↔ b ≤ a * c :=
by rw [← neg_neg c, mul_neg_eq_neg_mul_symm, div_neg, le_neg,
    div_le_iff (neg_pos.2 hc), neg_mul_eq_neg_mul_symm]

lemma div_lt_iff (hc : 0 < c) : b / c < a ↔ b < a * c :=
lt_iff_lt_of_le_iff_le (le_div_iff hc)

lemma div_lt_iff' (hc : 0 < c) : b / c < a ↔ b < c * a :=
by rw [mul_comm, div_lt_iff hc]

lemma div_lt_iff_of_neg (hc : c < 0) : b / c < a ↔ a * c < b :=
⟨mul_lt_of_neg_of_div_lt hc, div_lt_of_neg_of_mul_lt hc⟩

lemma inv_le_inv (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
by rw [inv_eq_one_div, div_le_iff ha,
       ← div_eq_inv_mul, one_le_div_iff_le hb]

lemma inv_le (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b ↔ b⁻¹ ≤ a :=
by rw [← inv_le_inv hb (inv_pos.2 ha), inv_inv']

lemma le_inv (ha : 0 < a) (hb : 0 < b) : a ≤ b⁻¹ ↔ b ≤ a⁻¹ :=
by rw [← inv_le_inv (inv_pos.2 hb) ha, inv_inv']

lemma one_div_le_one_div (ha : 0 < a) (hb : 0 < b) : 1 / a ≤ 1 / b ↔ b ≤ a :=
by simpa [one_div] using inv_le_inv ha hb

lemma inv_lt_inv (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a :=
lt_iff_lt_of_le_iff_le (inv_le_inv hb ha)

lemma inv_lt (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b ↔ b⁻¹ < a :=
lt_iff_lt_of_le_iff_le (le_inv hb ha)

lemma one_div_lt (ha : 0 < a) (hb : 0 < b) : 1 / a < b ↔ 1 / b < a :=
(one_div a).symm ▸ (one_div b).symm ▸ inv_lt ha hb

lemma one_div_le (ha : 0 < a) (hb : 0 < b) : 1 / a ≤ b ↔ 1 / b ≤ a :=
by simpa using inv_le ha hb

lemma lt_inv (ha : 0 < a) (hb : 0 < b) : a < b⁻¹ ↔ b < a⁻¹ :=
lt_iff_lt_of_le_iff_le (inv_le hb ha)

lemma one_div_lt_one_div (ha : 0 < a) (hb : 0 < b) : 1 / a < 1 / b ↔ b < a :=
lt_iff_lt_of_le_iff_le (one_div_le_one_div hb ha)

lemma div_lt_div_right (hc : 0 < c) : a / c < b / c ↔ a < b :=
⟨lt_imp_lt_of_le_imp_le (λ h, div_le_div_of_pos_of_le hc h),
 λ h, div_lt_div_of_pos_of_lt hc h⟩

lemma div_le_div_right (hc : 0 < c) : a / c ≤ b / c ↔ a ≤ b :=
le_iff_le_iff_lt_iff_lt.2 (div_lt_div_right hc)

lemma div_lt_div_right_of_neg (hc : c < 0) : a / c < b / c ↔ b < a :=
⟨lt_imp_lt_of_le_imp_le (λ h, div_le_div_of_neg_of_le hc h),
 λ h, div_lt_div_of_neg_of_lt hc h⟩

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

lemma div_le_div (hc : 0 ≤ c) (hac : a ≤ c) (hd : 0 < d) (hbd : d ≤ b) : a / b ≤ c / d :=
begin
  rw div_le_div_iff (lt_of_lt_of_le hd hbd) hd,
  exact mul_le_mul hac hbd (le_of_lt hd) hc
end

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

instance linear_ordered_field.to_densely_ordered : densely_ordered α :=
{ dense := assume a₁ a₂ h, ⟨(a₁ + a₂) / 2,
  calc a₁ = (a₁ + a₁) / 2 : (add_self_div_two a₁).symm
    ... < (a₁ + a₂) / 2 : div_lt_div_of_pos_of_lt two_pos (add_lt_add_left h _),
  calc (a₁ + a₂) / 2 < (a₂ + a₂) / 2 : div_lt_div_of_pos_of_lt two_pos (add_lt_add_right h _)
    ... = a₂ : add_self_div_two a₂⟩ }

instance linear_ordered_field.to_no_top_order : no_top_order α :=
{ no_top := assume a, ⟨a + 1, lt_add_of_le_of_pos (le_refl a) zero_lt_one ⟩ }

instance linear_ordered_field.to_no_bot_order : no_bot_order α :=
{ no_bot := assume a, ⟨a + -1,
    add_lt_of_le_of_neg (le_refl _) (neg_lt_of_neg_lt $ by simp [zero_lt_one]) ⟩ }

lemma inv_lt_one (ha : 1 < a) : a⁻¹ < 1 :=
by rw [inv_eq_one_div]; exact div_lt_of_pos_of_lt_mul (lt_trans zero_lt_one ha) (by simp *)

lemma one_lt_inv (h₁ : 0 < a) (h₂ : a < 1) : 1 < a⁻¹ :=
by rw [inv_eq_one_div, lt_div_iff h₁]; simp [h₂]

lemma inv_le_one (ha : 1 ≤ a) : a⁻¹ ≤ 1 :=
by rw [inv_eq_one_div]; exact div_le_of_le_mul (lt_of_lt_of_le zero_lt_one ha) (by simp *)

lemma one_le_inv (ha0 : 0 < a) (ha : a ≤ 1) : 1 ≤ a⁻¹ :=
le_of_mul_le_mul_left (by simpa [mul_inv_cancel (ne.symm (ne_of_lt ha0))]) ha0

lemma mul_self_inj_of_nonneg (a0 : 0 ≤ a) (b0 : 0 ≤ b) : a * a = b * b ↔ a = b :=
mul_self_eq_mul_self_iff.trans $ or_iff_left_of_imp $
λ h, by subst a; rw [le_antisymm (neg_nonneg.1 a0) b0, neg_zero]

lemma div_le_div_of_le_left (ha : 0 ≤ a) (hc : 0 < c) (h : c ≤ b) :
  a / b ≤ a / c :=
by haveI := classical.dec_eq α; exact
if ha0 : a = 0 then by simp [ha0]
else (div_le_div_left (lt_of_le_of_ne ha (ne.symm ha0)) (lt_of_lt_of_le hc h) hc).2 h

lemma inv_le_inv_of_le (hb : 0 < b) (h : b ≤ a) : a⁻¹ ≤ b⁻¹ :=
begin
  rw [inv_eq_one_div, inv_eq_one_div],
  exact one_div_le_one_div_of_le hb h
end

lemma div_le_div_of_le_of_nonneg (hab : a ≤ b) (hc : 0 ≤ c) :
  a / c ≤ b / c :=
mul_le_mul_of_nonneg_right hab (inv_nonneg.2 hc)

end linear_ordered_field

@[protect_proj] class discrete_linear_ordered_field (α : Type*)
  extends linear_ordered_field α, decidable_linear_ordered_comm_ring α

section discrete_linear_ordered_field
variables [discrete_linear_ordered_field α]

lemma abs_div (a b : α) : abs (a / b) = abs a / abs b :=
decidable.by_cases
  (assume h : b = 0, by rw [h, abs_zero, div_zero, div_zero, abs_zero])
  (assume h : b ≠ 0,
   have h₁ : abs b ≠ 0, from
     assume h₂, h (eq_zero_of_abs_eq_zero h₂),
   eq_div_of_mul_eq h₁
   (show abs (a / b) * abs b = abs a, by rw [← abs_mul, div_mul_cancel _ h]))

lemma abs_one_div (a : α) : abs (1 / a) = 1 / abs a :=
by rw [abs_div, abs_of_nonneg (zero_le_one : 1 ≥ (0 : α))]

lemma abs_inv (a : α) : abs a⁻¹ = (abs a)⁻¹ :=
have h : abs (1 / a) = 1 / abs a,
  begin rw [abs_div, abs_of_nonneg], exact zero_le_one end,
by simp [*] at *

end discrete_linear_ordered_field
