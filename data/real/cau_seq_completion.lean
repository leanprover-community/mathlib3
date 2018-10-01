/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Robert Y. Lewis

Generalizes the Cauchy completion of (ℚ, abs) to the completion of a
commutative ring with absolute value.
-/

import data.real.cau_seq

namespace cau_seq.completion
open cau_seq

section
parameters {α : Type*} [discrete_linear_ordered_field α]
parameters {β : Type*} [comm_ring β] {abv : β → α} [is_absolute_value abv]

def Cauchy := @quotient (cau_seq _ abv) cau_seq.equiv

def mk : cau_seq _ abv → Cauchy := quotient.mk

@[simp] theorem mk_eq_mk (f) : @eq Cauchy ⟦f⟧ (mk f) := rfl

theorem mk_eq {f g} : mk f = mk g ↔ f ≈ g := quotient.eq

def of_rat (x : β) : Cauchy := mk (const abv x)

instance : has_zero Cauchy := ⟨of_rat 0⟩
instance : has_one Cauchy := ⟨of_rat 1⟩
instance : inhabited Cauchy := ⟨0⟩

theorem of_rat_zero : of_rat 0 = 0 := rfl
theorem of_rat_one : of_rat 1 = 1 := rfl

@[simp] theorem mk_eq_zero {f} : mk f = 0 ↔ lim_zero f :=
by have : mk f = 0 ↔ lim_zero (f - 0) := quotient.eq;
   rwa sub_zero at this

instance : has_add Cauchy :=
⟨λ x y, quotient.lift_on₂ x y (λ f g, mk (f + g)) $
  λ f₁ g₁ f₂ g₂ hf hg, quotient.sound $
  by simpa [(≈), setoid.r] using add_lim_zero hf hg⟩

@[simp] theorem mk_add (f g : cau_seq β abv) : mk f + mk g = mk (f + g) := rfl

instance : has_neg Cauchy :=
⟨λ x, quotient.lift_on x (λ f, mk (-f)) $
  λ f₁ f₂ hf, quotient.sound $
  by simpa [(≈), setoid.r] using neg_lim_zero hf⟩

@[simp] theorem mk_neg (f : cau_seq β abv) : -mk f = mk (-f) := rfl

instance : has_mul Cauchy :=
⟨λ x y, quotient.lift_on₂ x y (λ f g, mk (f * g)) $
  λ f₁ g₁ f₂ g₂ hf hg, quotient.sound $
  by simpa [(≈), setoid.r, mul_add, mul_comm] using
    add_lim_zero (mul_lim_zero g₁ hf) (mul_lim_zero f₂ hg)⟩

@[simp] theorem mk_mul (f g : cau_seq β abv) : mk f * mk g = mk (f * g) := rfl

theorem of_rat_add (x y : β) : of_rat (x + y) = of_rat x + of_rat y :=
congr_arg mk (const_add _ _)

theorem of_rat_neg (x : β) : of_rat (-x) = -of_rat x :=
congr_arg mk (const_neg _)

theorem of_rat_mul (x y : β) : of_rat (x * y) = of_rat x * of_rat y :=
congr_arg mk (const_mul _ _)

private lemma zero_def : 0 = mk 0 := rfl

private lemma one_def : 1 = mk 1 := rfl

instance : comm_ring Cauchy :=
by refine { neg := has_neg.neg,
    add := (+), zero := 0, mul := (*), one := 1, .. };
  { repeat {refine λ a, quotient.induction_on a (λ _, _)},
    simp [zero_def, one_def, mul_left_comm, mul_comm, mul_add] }

theorem of_rat_sub (x y : β) : of_rat (x - y) = of_rat x - of_rat y :=
congr_arg mk (const_sub _ _)

end

local attribute [instance] classical.prop_decidable
section

parameters {α : Type*} [discrete_linear_ordered_field α]
parameters {β : Type*} [discrete_field β] {abv : β → α} [is_absolute_value abv]
local notation `Cauchy` := @Cauchy _ _ _ _ abv _

noncomputable instance : has_inv Cauchy :=
⟨λ x, quotient.lift_on x
  (λ f, mk $ if h : lim_zero f then 0 else inv f h) $
λ f g fg, begin
  have := lim_zero_congr fg,
  by_cases hf : lim_zero f,
  { simp [hf, this.1 hf, setoid.refl] },
  { have hg := mt this.2 hf, simp [hf, hg],
    have If : mk (inv f hf) * mk f = 1 := mk_eq.2 (inv_mul_cancel hf),
    have Ig : mk (inv g hg) * mk g = 1 := mk_eq.2 (inv_mul_cancel hg),
    rw [mk_eq.2 fg, ← Ig] at If,
    rw mul_comm at Ig,
    rw [← mul_one (mk (inv f hf)), ← Ig, ← mul_assoc, If,
        mul_assoc, Ig, mul_one] }
end⟩

@[simp] theorem inv_zero : (0 : Cauchy)⁻¹ = 0 :=
congr_arg mk $ by rw dif_pos; [refl, exact zero_lim_zero]

@[simp] theorem inv_mk {f} (hf) : (@mk α _ β _ abv _ f)⁻¹ = mk (inv f hf) :=
congr_arg mk $ by rw dif_neg

lemma cau_seq_zero_ne_one : ¬ (0 : cau_seq _ abv) ≈ 1 := λ h,
have lim_zero (1 - 0), from setoid.symm h,
have lim_zero 1, by simpa,
one_ne_zero $ const_lim_zero.1 this

lemma zero_ne_one : (0 : Cauchy) ≠ 1 :=
λ h, cau_seq_zero_ne_one $ mk_eq.1 h


protected theorem inv_mul_cancel {x : Cauchy} : x ≠ 0 → x⁻¹ * x = 1 :=
quotient.induction_on x $ λ f hf, begin
  simp at hf, simp [hf],
  exact quotient.sound (cau_seq.inv_mul_cancel hf)
end

noncomputable def discrete_field : discrete_field Cauchy :=
{ inv              := has_inv.inv,
  inv_mul_cancel   := @cau_seq.completion.inv_mul_cancel,
  mul_inv_cancel   := λ x x0, by rw [mul_comm, cau_seq.completion.inv_mul_cancel x0],
  zero_ne_one      := zero_ne_one,
  inv_zero         := inv_zero,
  has_decidable_eq := by apply_instance,
  ..cau_seq.completion.comm_ring }

local attribute [instance] discrete_field

theorem of_rat_inv (x : β) : of_rat (x⁻¹) = ((of_rat x)⁻¹ : Cauchy) :=
congr_arg mk $ by split_ifs with h; try {simp [const_lim_zero.1 h]}; refl

theorem of_rat_div (x y : β) : of_rat (x / y) = (of_rat x / of_rat y : Cauchy) :=
by simp only [div_eq_inv_mul, of_rat_inv, of_rat_mul]

end
end cau_seq.completion

namespace cau_seq
section

variables {α : Type*} [discrete_linear_ordered_field α]
variables (β : Type*) [ring β] (abv : β → α) [is_absolute_value abv]

class is_complete :=
(is_complete : ∀ s : cau_seq β abv, ∃ b : β, ∀ ε > 0, ∃ N : ℕ, ∀ i ≥ N, abv (b - s.val i) < ε)
end

section

variables {α : Type*} [discrete_linear_ordered_field α]
variables {β : Type*} [ring β] {abv : β → α} [is_absolute_value abv]
variable [is_complete β abv]

lemma complete : ∀ s : cau_seq β abv, ∃ b : β, ∀ ε > 0, ∃ N : ℕ, ∀ i ≥ N, abv (b - s.val i) < ε :=
is_complete.is_complete

noncomputable def lim (s : cau_seq β abv) := classical.some (complete s)

lemma lim_spec (s : cau_seq β abv) : ∀ ε > 0, ∃ N : ℕ, ∀ i ≥ N, abv (lim s - s.val i) < ε :=
classical.some_spec (complete s)

end
end cau_seq