/-
Tests for norm_cast
-/

import tactic.norm_cast
import data.complex.basic -- ℕ, ℤ, ℚ, ℝ, ℂ

constants (an bn cn dn : ℕ) (az bz cz dz : ℤ) (aq bq cq dq : ℚ)
constants (ar br cr dr : ℝ) (ac bc cc dc : ℂ)

example : (an : ℤ) = bn → an = bn := λ h, by exact_mod_cast h -- by simp
example : an = bn → (an : ℤ) = bn := λ h, by exact_mod_cast h -- by simp
example : az = bz ↔ (az : ℚ) = bz := by norm_cast -- by simp

example : (aq : ℝ) = br ↔ (aq : ℂ) = br := by norm_cast
example : (an : ℚ) = bz ↔ (an : ℂ) = bz := by norm_cast
example : (((an : ℤ) : ℚ) : ℝ) = bq ↔ ((an : ℚ) : ℂ) = (bq : ℝ) :=
by norm_cast

example : (an : ℤ) < bn ↔ an < bn             := by norm_cast -- by simp
example : (an : ℚ) < bz ↔ (an : ℝ) < bz       := by norm_cast
example : ((an : ℤ) : ℝ) < bq ↔ (an : ℚ) < bq := by norm_cast
example : (an : ℤ) ≠ (bn : ℤ) ↔ an ≠ bn := by norm_cast -- by simp

-- zero and one cause special problems
example : 0 < (bq : ℝ) ↔ 0 < bq := by norm_cast -- by simp
example : az > (1 : ℕ) ↔ az > 1 := by norm_cast -- by simp
example : az > (0 : ℕ) ↔ az > 0 := by norm_cast -- by simp
example : (an : ℤ) ≠ 0 ↔ an ≠ 0 := by norm_cast -- by simp
example : aq < (1 : ℕ) ↔ (aq : ℝ) < (1 : ℤ) := by norm_cast

example : (an : ℤ) + bn = (an + bn : ℕ)   := by norm_cast -- by simp
example : (an : ℂ) + bq = ((an + bq) : ℚ) := by norm_cast -- by simp
example : (((an : ℤ) : ℚ) : ℝ) + bn = (an + (bn : ℤ)) := by norm_cast -- by simp

example : (((((an : ℚ) : ℝ) * bq) + (cq : ℝ) ^ dn) : ℂ) = (an : ℂ) * (bq : ℝ) + cq ^ dn :=
by norm_cast -- by simp
example : ((an : ℤ) : ℝ) < bq ∧ (cr : ℂ) ^ 2 = dz ↔ (an : ℚ) < bq ∧ ((cr ^ 2) : ℂ) = dz :=
by norm_cast

example : (an : ℤ) = 1 → an = 1 := λ h, by exact_mod_cast h
example : (an : ℤ) < 5 → an < 5 := λ h, by exact_mod_cast h
example : an < 5 → (an : ℤ) < 5 := λ h, by exact_mod_cast h
example : (an + 5) < 10 → (an : ℤ) + 5 < 10 := λ h, by exact_mod_cast h
example : (an : ℤ) + 5 < 10 → (an + 5) < 10 := λ h, by exact_mod_cast h
example : ((an + 5 : ℕ) : ℤ) < 10 → an + 5 < 10 := λ h, by exact_mod_cast h
example : an + 5 < 10 → ((an + 5 : ℕ) : ℤ) < 10 := λ h, by exact_mod_cast h

example (h : bn ≤ an) : an - bn = 1 ↔ (an - bn : ℤ) = 1 :=
by norm_cast
example (h : (cz : ℚ) = az / bz) : (cz : ℝ) = az / bz :=
by assumption_mod_cast

namespace hidden

def with_zero (α) := option α

variables {α : Type*}

instance : has_coe_t α (with_zero α) := ⟨some⟩

instance : has_zero (with_zero α) := ⟨none⟩

instance [has_one α]: has_one (with_zero α) := ⟨some 1⟩

instance [has_mul α] : mul_zero_class (with_zero α) :=
{ mul       := λ o₁ o₂, o₁.bind (λ a, o₂.map (λ b, a * b)),
  zero_mul  := λ a, rfl,
  mul_zero  := λ a, by cases a; refl,
  ..with_zero.has_zero }

@[squash_cast] lemma coe_one [has_one α] : ((1 : α) : with_zero α) = 1 := rfl

@[elim_cast] lemma coe_inj {a b : α} : (a : with_zero α) = b ↔ a = b :=
option.some_inj

@[move_cast] lemma mul_coe {α : Type*} [has_mul α] (a b : α) :
  ((a * b : α) : with_zero α) = (a : with_zero α) * b := rfl

example [has_mul α] [has_one α] (x y : α) (h : (x : with_zero α) * y = 1) :
  x*y = 1 :=
by exact_mod_cast h

end hidden
