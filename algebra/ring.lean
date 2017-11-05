/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn
-/
import algebra.group

universe u
variable {α : Type u}

section
  variable [semiring α]

  theorem mul_two (n : α) : n * 2 = n + n :=
  (left_distrib n 1 1).trans (by simp)
end

section units
  variables [semiring α]
  variable (α)

  structure invertible :=
  (val : α)
  (inv : α)
  (val_inv : val * inv = 1)
  (inv_val : inv * val = 1)

  variables {a b c : invertible α}
  variable {α}

  def units.ext (HAB : a.val = b.val) : a = b :=
  begin
    cases a,
    cases b,
    dsimp at HAB,
    congr,
    exact HAB,
    exact calc
        inv = inv * (val_1 * inv_1) : by rw [val_inv_1, mul_one]
        ... = (inv * val_1) * inv_1 : by rw [mul_assoc]
        ... = (inv * val) * inv_1   : by rw [HAB]
        ... = inv_1                 : by rw [inv_val, one_mul]
  end

  lemma mul_four {a b c d : α} :
  (a * b) * (c * d) = a * (b * c) * d := by simp

  instance : has_mul (invertible α) := ⟨(λ a b,
  { val     := a.val * b.val,
    inv     := b.inv * a.inv,
    val_inv := by rw [mul_four,b.val_inv,mul_one,a.val_inv],
    inv_val := by rw [mul_four,a.inv_val,mul_one,b.inv_val] })⟩

  instance : has_one (invertible α) := ⟨
  { val     := 1,
    inv     := 1,
    val_inv := mul_one 1,
    inv_val := one_mul 1 }⟩

  instance : has_inv (invertible α) := ⟨(λ a,
  { val     := a.inv,
    inv     := a.val,
    val_inv := a.inv_val,
    inv_val := a.val_inv })⟩

  variables (a b c)

  @[simp] lemma mul_val : (a*b).val = a.val * b.val := rfl
  @[simp] lemma one_val : (1 : invertible α).val = 1 := rfl
  @[simp] lemma inv_val : (a⁻¹).val = a.inv := rfl
  @[simp] lemma inv_mul : (a⁻¹*a).val = 1 := by simp [a.inv_val]

  instance : group (invertible α) :=
  {
    mul := has_mul.mul,
    mul_assoc := (λ a b c, units.ext (by simp)),
    one := has_one.one _,
    mul_one := (λ a, units.ext (by simp)),
    one_mul := (λ a, units.ext (by simp)),
    inv := has_inv.inv,
    mul_left_inv := (λ a, units.ext (by simp [a.inv_val]))
  }

end units

section
  variables [ring α] (a b c d e : α)

  lemma mul_neg_one (a : α) : a * -1 = -a := by simp

  lemma neg_one_mul (a : α) : -1 * a = -a := by simp

  theorem mul_add_eq_mul_add_iff_sub_mul_add_eq : a * e + c = b * e + d ↔ (a - b) * e + c = d :=
  calc
    a * e + c = b * e + d ↔ a * e + c = d + b * e : by simp
      ... ↔ a * e + c - b * e = d : iff.intro (λ h, begin simp [h] end) (λ h,
                                                    begin simp [h.symm] end)
      ... ↔ (a - b) * e + c = d   : begin simp [@sub_eq_add_neg α, @right_distrib α] end

  theorem sub_mul_add_eq_of_mul_add_eq_mul_add : a * e + c = b * e + d → (a - b) * e + c = d :=
  assume h,
  calc
    (a - b) * e + c = (a * e + c) - b * e : begin simp [@sub_eq_add_neg α, @right_distrib α] end
                ... = d                   : begin rewrite h, simp [@add_sub_cancel α] end

  theorem ne_zero_and_ne_zero_of_mul_ne_zero {a b : α} (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 :=
  begin
    split,
    { intro ha, apply h, simp [ha] },
    { intro hb, apply h, simp [hb] }
  end
end

section comm_ring
  variable [comm_ring α]

  @[simp] lemma dvd_neg (a b : α) : (a ∣ -b) ↔ (a ∣ b) :=
  ⟨dvd_of_dvd_neg, dvd_neg_of_dvd⟩

  @[simp] lemma neg_dvd (a b : α) : (-a ∣ b) ↔ (a ∣ b) :=
  ⟨dvd_of_neg_dvd, neg_dvd_of_dvd⟩
end comm_ring

set_option old_structure_cmd true
class domain (α : Type u) extends ring α, no_zero_divisors α, zero_ne_one_class α

section domain
  variable [domain α]

  theorem mul_eq_zero {a b : α} : a * b = 0 ↔ a = 0 ∨ b = 0 :=
  ⟨eq_zero_or_eq_zero_of_mul_eq_zero, λo,
    or.elim o (λh, by rw h; apply zero_mul) (λh, by rw h; apply mul_zero)⟩

  theorem mul_ne_zero' {a b : α} (h₁ : a ≠ 0) (h₂ : b ≠ 0) : a * b ≠ 0 :=
  λ h, or.elim (eq_zero_or_eq_zero_of_mul_eq_zero h) h₁ h₂

  theorem domain.mul_right_inj {a b c : α} (ha : a ≠ 0) : b * a = c * a ↔ b = c :=
  by rw [← sub_eq_zero, ← mul_sub_right_distrib, mul_eq_zero];
     simp [ha]; exact sub_eq_zero

  theorem domain.mul_left_inj {a b c : α} (ha : a ≠ 0) : a * b = a * c ↔ b = c :=
  by rw [← sub_eq_zero, ← mul_sub_left_distrib, mul_eq_zero];
     simp [ha]; exact sub_eq_zero

  theorem eq_zero_of_mul_eq_self_right' {a b : α} (h₁ : b ≠ 1) (h₂ : a * b = a) : a = 0 :=
  by apply (mul_eq_zero.1 _).resolve_right (sub_ne_zero.2 h₁);
     rw [mul_sub_left_distrib, mul_one, sub_eq_zero, h₂]

  theorem eq_zero_of_mul_eq_self_left' {a b : α} (h₁ : b ≠ 1) (h₂ : b * a = a) : a = 0 :=
  by apply (mul_eq_zero.1 _).resolve_left (sub_ne_zero.2 h₁);
     rw [mul_sub_right_distrib, one_mul, sub_eq_zero, h₂]

  theorem mul_ne_zero_comm' {a b : α} (h : a * b ≠ 0) : b * a ≠ 0 :=
  mul_ne_zero' (ne_zero_of_mul_ne_zero_left h) (ne_zero_of_mul_ne_zero_right h)

end domain

/- integral domains -/

section
  variables [s : integral_domain α] (a b c d e : α)
  include s

  instance integral_domain.to_domain : domain α := {s with}

  theorem eq_of_mul_eq_mul_right_of_ne_zero {a b c : α} (ha : a ≠ 0) (h : b * a = c * a) : b = c :=
  have b * a - c * a = 0, by simp [h],
  have (b - c) * a = 0, by rewrite [mul_sub_right_distrib, this],
  have b - c = 0, from (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right ha,
  eq_of_sub_eq_zero this

  theorem eq_of_mul_eq_mul_left_of_ne_zero {a b c : α} (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  have a * b - a * c = 0, by simp [h],
  have a * (b - c) = 0, by rewrite [mul_sub_left_distrib, this],
  have b - c = 0, from (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_left ha,
  eq_of_sub_eq_zero this

  theorem mul_dvd_mul_iff_left {a b c : α} (ha : a ≠ 0) : a * b ∣ a * c ↔ b ∣ c :=
  exists_congr $ λ d, by rw [mul_assoc, domain.mul_left_inj ha]

  theorem mul_dvd_mul_iff_right {a b c : α} (hc : c ≠ 0) : a * c ∣ b * c ↔ a ∣ b :=
  exists_congr $ λ d, by rw [mul_right_comm, domain.mul_right_inj hc]

end

section division_ring
variables [division_ring α] {a b c : α}

lemma add_div : (a + b) / c = a / c + b / c :=
by rw [div_eq_mul_one_div, add_mul, ←div_eq_mul_one_div, ←div_eq_mul_one_div]

lemma div_eq_mul_inv : a / b = a * b⁻¹ :=
by rw [div_eq_mul_one_div, inv_eq_one_div]

lemma neg_inv (h : a ≠ 0) : - a⁻¹ = (- a)⁻¹ :=
by rwa [inv_eq_one_div, inv_eq_one_div, div_neg_eq_neg_div]

end division_ring
