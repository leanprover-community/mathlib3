/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn
-/
open eq

universe variable uu
variable {A : Type uu}

/- ring -/

section
  variables [ring A] (a b c d e : A)

  theorem mul_add_eq_mul_add_iff_sub_mul_add_eq : a * e + c = b * e + d ↔ (a - b) * e + c = d :=
  calc
    a * e + c = b * e + d ↔ a * e + c = d + b * e : by simp
      ... ↔ a * e + c - b * e = d : iff.intro (λ h, begin simp [h] end) (λ h,
                                                    begin simp [h.symm] end)
      ... ↔ (a - b) * e + c = d   : begin simp [@sub_eq_add_neg A, @right_distrib A] end

  theorem sub_mul_add_eq_of_mul_add_eq_mul_add : a * e + c = b * e + d → (a - b) * e + c = d :=
  assume h,
  calc
    (a - b) * e + c = (a * e + c) - b * e : begin simp [@sub_eq_add_neg A, @right_distrib A] end
                ... = d                   : begin rewrite h, simp [@add_sub_cancel A] end

  theorem mul_neg_one_eq_neg : a * (-1) = -a :=
    have a + a * -1 = 0, from calc
      a + a * -1 = a * 1 + a * -1 : by simp
             ... = a * (1 + -1)   : eq.symm (left_distrib a 1 (-1))
             ... = 0              : by simp,
    symm (neg_eq_of_add_eq_zero this)

  theorem ne_zero_and_ne_zero_of_mul_ne_zero {a b : A} (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 :=
  begin
    split,
      intro ha, apply h, simp [ha],
    intro hb, apply h, simp [hb]
  end
end

/- integral domains -/

section
  variables [s : integral_domain A] (a b c d e : A)
  include s

  theorem eq_of_mul_eq_mul_right_of_ne_zero {a b c : A} (ha : a ≠ 0) (h : b * a = c * a) : b = c :=
  have b * a - c * a = 0, by simp [h],
  have (b - c) * a = 0, by rewrite [mul_sub_right_distrib, this],
  have b - c = 0, from (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right ha,
  eq_of_sub_eq_zero this

  theorem eq_of_mul_eq_mul_left_of_ne_zero {a b c : A} (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  have a * b - a * c = 0, by simp [h],
  have a * (b - c) = 0, by rewrite [mul_sub_left_distrib, this],
  have b - c = 0, from (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_left ha,
  eq_of_sub_eq_zero this


  -- TODO: do we want the iff versions?

--  theorem dvd_of_mul_dvd_mul_left {a b c : A} (Ha : a ≠ 0) (Hdvd : (a * b ∣ a * c)) : (b ∣ c) :=
--  sorry
  /-
  dvd.elim Hdvd
    (assume d,
      assume : a * c = a * b * d,
      have b * d = c, from eq_of_mul_eq_mul_left Ha begin rewrite ←mul.assoc, symmetry, exact this end,
      dvd.intro this)
  -/

--  theorem dvd_of_mul_dvd_mul_right {a b c : A} (Ha : a ≠ 0) (Hdvd : (b * a ∣ c * a)) : (b ∣ c) :=
--  sorry
  /-
  dvd.elim Hdvd
    (assume d,
      assume : c * a = b * a * d,
      have b * d * a = c * a, from by rewrite [mul.right_comm, ←this],
      have b * d = c, from eq_of_mul_eq_mul_right Ha this,
      dvd.intro this)
  -/
end

/-
namespace norm_num

local attribute bit0 bit1 add1 [reducible]
local attribute right_distrib left_distrib [simp]

theorem mul_zero [mul_zero_class A] (a : A) : a * zero = zero :=
sorry -- by simp

theorem zero_mul [mul_zero_class A] (a : A) : zero * a = zero :=
sorry -- by simp

theorem mul_one [monoid A] (a : A) : a * one = a :=
sorry -- by simp

theorem mul_bit0 [distrib A] (a b : A) : a * (bit0 b) = bit0 (a * b) :=
sorry -- by simp

theorem mul_bit0_helper [distrib A] (a b t : A) (h : a * b = t) : a * (bit0 b) = bit0 t :=
sorry -- by rewrite -H; simp

theorem mul_bit1 [semiring A] (a b : A) : a * (bit1 b) = bit0 (a * b) + a :=
sorry -- by simp

theorem mul_bit1_helper [semiring A] (a b s t : A) (Hs : a * b = s) (Ht : bit0 s + a  = t) :
        a * (bit1 b) = t :=
sorry -- by simp

theorem subst_into_prod [has_mul A] (l r tl tr t : A) (prl : l = tl) (prr : r = tr)
        (prt : tl * tr = t) :
        l * r = t :=
sorry -- by simp

theorem mk_cong (op : A → A) (a b : A) (h : a = b) : op a = op b :=
sorry -- by simp

theorem neg_add_neg_eq_of_add_add_eq_zero [add_comm_group A] (a b c : A) (h : c + a + b = 0) :
        -a + -b = c :=
sorry
/-
begin
  apply add_neg_eq_of_eq_add,
  apply neg_eq_of_add_eq_zero,
  simp
end
-/

theorem neg_add_neg_helper [add_comm_group A] (a b c : A) (h : a + b = c) : -a + -b = -c :=
sorry -- begin apply iff.mp !neg_eq_neg_iff_eq, simp end

theorem neg_add_pos_eq_of_eq_add [add_comm_group A] (a b c : A) (h : b = c + a) : -a + b = c :=
sorry -- begin apply neg_add_eq_of_eq_add, simp end

theorem neg_add_pos_helper1 [add_comm_group A] (a b c : A) (h : b + c = a) : -a + b = -c :=
sorry -- begin apply neg_add_eq_of_eq_add, apply eq_add_neg_of_add_eq H end

theorem neg_add_pos_helper2 [add_comm_group A] (a b c : A) (h : a + c = b) : -a + b = c :=
sorry -- begin apply neg_add_eq_of_eq_add, rewrite H end

theorem pos_add_neg_helper [add_comm_group A] (a b c : A) (h : b + a = c) : a + b = c :=
sorry -- by simp

theorem sub_eq_add_neg_helper [add_comm_group A] (t₁ t₂ e w₁ w₂: A) (H₁ : t₁ = w₁)
        (H₂ : t₂ = w₂) (h : w₁ + -w₂ = e) : t₁ - t₂ = e :=
sorry -- by simp

theorem pos_add_pos_helper [add_comm_group A] (a b c h₁ h₂ : A) (H₁ : a = h₁) (H₂ : b = h₂)
        (h : h₁ + h₂ = c) : a + b = c :=
sorry -- by simp

theorem subst_into_subtr [add_group A] (l r t : A) (prt : l + -r = t) : l - r = t :=
sorry -- by simp

theorem neg_neg_helper [add_group A] (a b : A) (h : a = -b) : -a = b :=
sorry -- by simp

theorem neg_mul_neg_helper [ring A] (a b c : A) (h : a * b = c) : (-a) * (-b) = c :=
sorry -- by simp

theorem neg_mul_pos_helper [ring A] (a b c : A) (h : a * b = c) : (-a) * b = -c :=
sorry -- by simp

theorem pos_mul_neg_helper [ring A] (a b c : A) (h : a * b = c) : a * (-b) = -c :=
sorry -- by simp

end norm_num

attribute [simp]
  zero_mul mul_zero

attribute [simp]
  neg_mul_eq_neg_mul_symm mul_neg_eq_neg_mul_symm

attribute [simp]
  left_distrib right_distrib
-/
