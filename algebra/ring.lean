/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn
-/
import algebra.group tactic

universe u
variable {α : Type u}

section
  variable [semiring α]

  theorem mul_two (n : α) : n * 2 = n + n :=
  (left_distrib n 1 1).trans (by simp)
end

structure units (α : Type u) [semiring α] :=
(val : α)
(inv : α)
(val_inv : val * inv = 1)
(inv_val : inv * val = 1)

namespace units
  variables [semiring α] {a b c : units α}

  instance : has_coe (units α) α := ⟨val⟩

  theorem ext : ∀ {a b : units α}, (a : α) = b → a = b
  | ⟨v, i₁, vi₁, iv₁⟩ ⟨v', i₂, vi₂, iv₂⟩ e :=
    by change v = v' at e; subst v'; congr;
       simpa [iv₂, vi₁] using mul_assoc i₂ v i₁

  protected def mul : units α → units α → units α
  | ⟨v₁, i₁, vi₁, iv₁⟩ ⟨v₂, i₂, vi₂, iv₂⟩ := ⟨v₁ * v₂, i₂ * i₁,
    have v₁ * (v₂ * i₂) * i₁ = 1, by rw [vi₂]; simp [vi₁], by simpa,
    have i₂ * (i₁ * v₁) * v₂ = 1, by rw [iv₁]; simp [iv₂], by simpa⟩

  protected def inv' : units α → units α
  | ⟨v, i, vi, iv⟩ := ⟨i, v, iv, vi⟩

  instance : has_mul (units α) := ⟨units.mul⟩
  instance : has_one (units α) := ⟨⟨1, 1, mul_one 1, one_mul 1⟩⟩
  instance : has_inv (units α) := ⟨units.inv'⟩

  variables (a b)
  @[simp] lemma mul_coe : (↑(a * b) : α) = a * b := by cases a; cases b; refl
  @[simp] lemma one_coe : ((1 : units α) : α) = 1 := rfl
  lemma val_coe : (↑a : α) = a.val := rfl
  lemma inv_coe : ((a⁻¹ : units α) : α) = a.inv := by cases a; refl
  @[simp] lemma inv_mul : (↑a⁻¹ * a : α) = 1 := by simp [val_coe, inv_coe, inv_val]
  @[simp] lemma mul_inv : (a * ↑a⁻¹ : α) = 1 := by simp [val_coe, inv_coe, val_inv]

  instance : group (units α) :=
  by refine {
      mul          := (*),
      one          := 1,
      inv          := has_inv.inv,
      mul_assoc    := _,
      mul_one      := _,
      one_mul      := _,
      mul_left_inv := _ };
    { intros, apply ext, simp }

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
