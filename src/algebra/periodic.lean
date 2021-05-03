/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
import algebra.group_power.lemmas

variables {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

namespace function

/-! ### Periodicity -/

/-- A function `f` is said to be `periodic` with period `c` if for all `x`, `f (x + c) = f x`. -/
@[simp] def periodic [has_add α] (f : α → β) (c : α) : Prop := ∀ x : α, f (x + c) = f x

lemma periodic.comp [has_add α] (h : periodic f c) (g : β → γ) : periodic (g ∘ f) c :=
by simp * at *

@[to_additive]
lemma periodic.mul [has_add α] [has_mul β] (hf : periodic f c) (hg : periodic g c) :
  periodic (f * g) c :=
by simp * at *

@[to_additive]
lemma periodic.div [has_add α] [has_div β] (hf : periodic f c) (hg : periodic g c) :
  periodic (f / g) c :=
by simp * at *

lemma periodic.mul_const [division_ring α] (a : α) (h : periodic f c) :
  periodic (λ x, f (x * a)) (c * a⁻¹) :=
begin
  intro x,
  by_cases ha : a = 0, { simp only [ha, mul_zero] },
  simpa only [add_mul, inv_mul_cancel_right' ha] using h (x * a),
end

lemma periodic.mul_const' [division_ring α] (a : α) (h : periodic f c) :
  periodic (λ x, f (x * a)) (c / a) :=
by simpa only [div_eq_mul_inv] using h.mul_const a

lemma periodic.mul_const_inv [division_ring α] (a : α) (h : periodic f c) :
  periodic (λ x, f (x * a⁻¹)) (c * a) :=
by simpa only [inv_inv'] using h.mul_const a⁻¹

lemma periodic.div_const [division_ring α] (a : α) (h : periodic f c) :
  periodic (λ x, f (x / a)) (c * a) :=
by simpa only [div_eq_mul_inv] using h.mul_const_inv a

lemma periodic.add_period [add_semigroup α] (h1 : periodic f c₁) (h2 : periodic f c₂) :
  periodic f (c₁ + c₂) :=
by simp [*, ← add_assoc] at *

lemma periodic.sub_eq [add_group α] (h : periodic f c) (x : α) : f (x - c) = f x :=
by simpa only [sub_add_cancel] using (h (x - c)).symm

lemma periodic.neg [add_group α] (h : periodic f c) : periodic f (-c) :=
by simpa only [sub_eq_add_neg, periodic] using h.sub_eq

lemma periodic.sub_period [add_comm_group α] (h1 : periodic f c₁) (h2 : periodic f c₂) :
  periodic f (c₁ - c₂) :=
let h := h2.neg in by simp [*, sub_eq_add_neg, add_comm c₁, ← add_assoc] at *

lemma periodic.nsmul [add_monoid α] (h : periodic f c) (n : ℕ) : periodic f (n • c) :=
by induction n; simp [nat.succ_eq_add_one, add_nsmul, ← add_assoc, zero_nsmul, *] at *

lemma periodic.nat_mul [semiring α] (h : periodic f c) (n : ℕ) : periodic f (n * c) :=
by simpa only [nsmul_eq_mul] using h.nsmul n

lemma periodic.neg_nsmul [add_group α] (h : periodic f c) (n : ℕ) : periodic f (-(n • c)) :=
(h.nsmul n).neg

lemma periodic.neg_nat_mul [ring α] (h : periodic f c) (n : ℕ) : periodic f (-(n * c)) :=
(h.nat_mul n).neg

lemma periodic.sub_nsmul_eq [add_group α] (h : periodic f c) (n : ℕ) : f (x - n • c) = f x :=
by simpa only [sub_eq_add_neg] using h.neg_nsmul n x

lemma periodic.sub_nat_mul_eq [ring α] (h : periodic f c) (n : ℕ) : f (x - n * c) = f x :=
by simpa only [nsmul_eq_mul] using h.sub_nsmul_eq n

lemma periodic.gsmul [add_group α] (h : periodic f c) (n : ℤ) : periodic f (n •ℤ c) :=
begin
  cases n, { exact h.nsmul n },
  simpa only [gsmul_neg_succ_of_nat] using (h.nsmul n.succ).neg,
end

lemma periodic.int_mul [ring α] (h : periodic f c) (n : ℤ) : periodic f (n * c) :=
by simpa only [gsmul_eq_mul] using h.gsmul n

lemma periodic.sub_gsmul_eq [add_group α] (h : periodic f c) (n : ℤ) : f (x - n •ℤ c) = f x :=
(h.gsmul n).sub_eq x

lemma periodic.sub_int_mul_eq [ring α] (h : periodic f c) (n : ℤ) : f (x - n * c) = f x :=
(h.int_mul n).sub_eq x

lemma periodic.eq [add_zero_class α] (h : periodic f c) : f c = f 0 :=
by simpa only [zero_add] using h 0

lemma periodic.neg_eq [add_group α] (h : periodic f c) : f (-c) = f 0 :=
h.neg.eq

lemma periodic.nsmul_eq [add_monoid α] (h : periodic f c) (n : ℕ) : f (n • c) = f 0 :=
(h.nsmul n).eq

lemma periodic.nat_mul_eq [semiring α] (h : periodic f c) (n : ℕ) : f (n * c) = f 0 :=
(h.nat_mul n).eq

lemma periodic.gsmul_eq [add_group α] (h : periodic f c) (n : ℤ) : f (n •ℤ c) = f 0 :=
(h.gsmul n).eq

lemma periodic.int_mul_eq [ring α] (h : periodic f c) (n : ℤ) : f (n * c) = f 0 :=
(h.int_mul n).eq

lemma periodic_with_period_zero [add_zero_class α] (f : α → β) : periodic f 0 :=
λ x, by rw add_zero

/-! ### Antiperiodicity -/

/-- A function `f` is said to be `antiperiodic` with antiperiod `c` if for all `x`,
  `f (x + c) = -f x`. -/
@[simp] def antiperiodic [has_add α] [has_neg β] (f : α → β) (c : α) : Prop :=
∀ x : α, f (x + c) = -f x

/-- If a function is `antiperiodic` with antiperiod `c`, then it is also `periodic` with period
  `2 * c`. -/
lemma antiperiodic.periodic [semiring α] [add_group β] (h : antiperiodic f c) :
  periodic f (2 * c) :=
by simp [two_mul, ← add_assoc, h _]

lemma antiperiodic.eq [add_zero_class α] [has_neg β] (h : antiperiodic f c) : f c = -f 0 :=
by simpa only [zero_add] using h 0

lemma antiperiodic.sub_eq [add_group α] [add_group β] (h : antiperiodic f c) (x : α) :
  f (x - c) = -f x :=
by simp only [eq_neg_iff_eq_neg.mp (h (x - c)), sub_add_cancel]

lemma antiperiodic.neg [add_group α] [add_group β] (h : antiperiodic f c) : antiperiodic f (-c) :=
by simpa only [sub_eq_add_neg, antiperiodic] using h.sub_eq

lemma antiperiodic.neg_eq [add_group α] [add_group β] (h : antiperiodic f c) : f (-c) = -f 0 :=
by simpa only [zero_add] using h.neg 0

lemma antiperiodic.mul_const [division_ring α] [has_neg β] {a : α}
  (h : antiperiodic f c) (ha : a ≠ 0) :
  antiperiodic (λ x, f (x * a)) (c * a⁻¹) :=
λ x, by simpa only [add_mul, inv_mul_cancel_right' ha] using h (x * a)

lemma antiperiodic.mul_const' [division_ring α] [has_neg β] {a : α}
  (h : antiperiodic f c) (ha : a ≠ 0) :
  antiperiodic (λ x, f (x * a)) (c / a) :=
by simpa only [div_eq_mul_inv] using h.mul_const ha

lemma antiperiodic.mul_const_inv [division_ring α] [has_neg β] {a : α}
  (h : antiperiodic f c) (ha : a ≠ 0) :
  antiperiodic (λ x, f (x * a⁻¹)) (c * a) :=
by simpa only [inv_inv'] using h.mul_const (inv_ne_zero ha)

lemma antiperiodic.div_inv [division_ring α] [has_neg β] {a : α}
  (h : antiperiodic f c) (ha : a ≠ 0) :
  antiperiodic (λ x, f (x / a)) (c * a) :=
by simpa only [div_eq_mul_inv] using h.mul_const_inv ha

lemma antiperiodic.add [add_group α] [add_group β]
  (h1 : antiperiodic f c₁) (h2 : antiperiodic f c₂) :
  periodic f (c₁ + c₂) :=
by simp [*, ← add_assoc] at *

lemma antiperiodic.sub [add_comm_group α] [add_group β]
  (h1 : antiperiodic f c₁) (h2 : antiperiodic f c₂) :
  periodic f (c₁ - c₂) :=
let h := h2.neg in by simp [*, sub_eq_add_neg, add_comm c₁, ← add_assoc] at *

lemma periodic.add_antiperiod [add_group α] [add_group β]
  (h1 : periodic f c₁) (h2 : antiperiodic f c₂) :
  antiperiodic f (c₁ + c₂) :=
by simp [*, ← add_assoc] at *

lemma periodic.sub_antiperiod [add_comm_group α] [add_group β]
  (h1 : periodic f c₁) (h2 : antiperiodic f c₂) :
  antiperiodic f (c₁ - c₂) :=
let h := h2.neg in by simp [*, sub_eq_add_neg, add_comm c₁, ← add_assoc] at *

lemma periodic.add_antiperiod_eq [add_group α] [add_group β]
  (h1 : periodic f c₁) (h2 : antiperiodic f c₂) :
  f (c₁ + c₂) = -f 0 :=
(h1.add_antiperiod h2).eq

lemma periodic.sub_antiperiod_eq [add_comm_group α] [add_group β]
  (h1 : periodic f c₁) (h2 : antiperiodic f c₂) :
  f (c₁ - c₂) = -f 0 :=
(h1.sub_antiperiod h2).eq

lemma antiperiodic.mul [has_add α] [ring β]
  (hf : antiperiodic f c) (hg : antiperiodic g c) :
  periodic (f * g) c :=
by simp * at *

lemma antiperiodic.div [has_add α] [division_ring β]
  (hf : antiperiodic f c) (hg : antiperiodic g c) :
  periodic (f / g) c :=
by simp [*, neg_div_neg_eq] at *

end function
