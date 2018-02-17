/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn
-/
import algebra.group algebra.module tactic data.set.basic

universes u v
variable {α : Type u}

section
  variable [semiring α]

  theorem mul_two (n : α) : n * 2 = n + n :=
  (left_distrib n 1 1).trans (by simp)
  
  theorem bit0_eq_two_mul (n : α) : bit0 n = 2 * n :=
  (two_mul _).symm
end

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

def nonunits (α : Type u) [comm_ring α] : set α := { x | ¬∃ y, y * x = 1 }

class is_ring_hom {α : Type u} {β : Type v} [comm_ring α] [comm_ring β] (f : α → β) : Prop :=
(map_add : ∀ {x y}, f (x + y) = f x + f y)
(map_mul : ∀ {x y}, f (x * y) = f x * f y)
(map_one : f 1 = 1)

namespace is_ring_hom

variables {β : Type v} [comm_ring α] [comm_ring β]
variables (f : α → β) [is_ring_hom f] {x y : α}

lemma map_zero : f 0 = 0 :=
calc f 0 = f (0 + 0) - f 0 : by rw [map_add f]; simp
     ... = 0 : by simp

lemma map_neg : f (-x) = -f x :=
calc f (-x) = f (-x + x) - f x : by rw [map_add f]; simp
        ... = -f x : by simp [map_zero f]

lemma map_sub : f (x - y) = f x - f y :=
by simp [map_add f, map_neg f]

end is_ring_hom

theorem is_submodule.eq_univ_of_contains_unit {α : Type u} [comm_ring α] (S : set α) [is_submodule S] :
(∃ x ∈ S, ∃ y, y * x = (1:α)) → S = set.univ :=
λ ⟨x, hx, y, hy⟩, set.ext $ λ z, ⟨λ hz, trivial, λ hz, calc
    z = z * (y * x) : by simp [hy]
  ... = (z * y) * x : eq.symm $ mul_assoc z y x
  ... ∈ S : is_submodule.smul (z * y) hx⟩

theorem is_submodule.univ_of_one_mem {α : Type u} [comm_ring α] (S : set α) [is_submodule S] :
(1:α) ∈ S → S = set.univ :=
λ h, set.ext $ λ z, ⟨λ hz, trivial, λ hz, by simpa using (is_submodule.smul z h : z * 1 ∈ S)⟩

set_option old_structure_cmd true
/-- A domain is a ring with no zero divisors, i.e. satisfying
  the condition `a * b = 0 ↔ a = 0 ∨ b = 0`. Alternatively, a domain
  is an integral domain without assuming commutativity of multiplication. -/
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

  instance integral_domain.to_domain : domain α := {..s}

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
