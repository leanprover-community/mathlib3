/-
Tests for norm_cast
-/

import tactic.norm_cast
import data.complex.basic -- ℕ, ℤ, ℚ, ℝ, ℂ
import data.real.ennreal

open_locale ennreal

constants (an bn cn dn : ℕ) (az bz cz dz : ℤ) (aq bq cq dq : ℚ)
constants (ar br cr dr : ℝ) (ac bc cc dc : ℂ)

example : (an : ℤ) = bn → an = bn := by {intro h, exact_mod_cast h}
example : an = bn → (an : ℤ) = bn := by {intro h, exact_mod_cast h}
example : az = bz ↔ (az : ℚ) = bz := by norm_cast

example : (aq : ℝ) = br ↔ (aq : ℂ) = br := by norm_cast
example : (an : ℚ) = bz ↔ (an : ℂ) = bz := by norm_cast
example : (((an : ℤ) : ℚ) : ℝ) = bq ↔ ((an : ℚ) : ℂ) = (bq : ℝ) :=
by norm_cast

example : (an : ℤ) < bn ↔ an < bn := by norm_cast
example : (an : ℚ) < bz ↔ (an : ℝ) < bz := by norm_cast
example : ((an : ℤ) : ℝ) < bq ↔ (an : ℚ) < bq := by norm_cast
example : (an : ℤ) ≠ (bn : ℤ) ↔ an ≠ bn := by norm_cast

-- zero and one cause special problems
example : 0 < (bq : ℝ) ↔ 0 < bq := by norm_cast
example : az > (1 : ℕ) ↔ az > 1 := by norm_cast
example : az > (0 : ℕ) ↔ az > 0 := by norm_cast
example : (an : ℤ) ≠ 0 ↔ an ≠ 0 := by norm_cast
example : aq < (1 : ℕ) ↔ (aq : ℝ) < (1 : ℤ) := by norm_cast

example : (an : ℤ) + bn = (an + bn : ℕ) := by norm_cast
example : (an : ℂ) + bq = ((an + bq) : ℚ) := by norm_cast
example : (((an : ℤ) : ℚ) : ℝ) + bn = (an + (bn : ℤ)) := by norm_cast

example : (((((an : ℚ) : ℝ) * bq) + (cq : ℝ) ^ dn) : ℂ) = (an : ℂ) * (bq : ℝ) + cq ^ dn :=
by norm_cast
example : ((an : ℤ) : ℝ) < bq ∧ (cr : ℂ) ^ 2 = dz ↔ (an : ℚ) < bq ∧ ((cr ^ 2) : ℂ) = dz :=
by norm_cast

--testing numerals
example : ((42 : ℕ) : ℤ) = 42 := by norm_cast
example : ((42 : ℕ) : ℂ) = 42 := by norm_cast
example : ((42 : ℤ) : ℚ) = 42 := by norm_cast
example : ((42 : ℚ) : ℝ) = 42 := by norm_cast

example (h : (an : ℝ) = 0) : an = 0 := by exact_mod_cast h
example (h : (an : ℝ) = 42) : an = 42 := by exact_mod_cast h
example (h : (an + 42) ≠ 42) : (an : ℝ) + 42 ≠ 42 := by exact_mod_cast h

-- testing the heuristic
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
  ..hidden.with_zero.has_zero }

@[norm_cast] lemma coe_one [has_one α] : ((1 : α) : with_zero α) = 1 := rfl

@[norm_cast] lemma coe_inj {a b : α} : (a : with_zero α) = b ↔ a = b :=
option.some_inj

@[norm_cast] lemma mul_coe {α : Type*} [has_mul α] (a b : α) :
  ((a * b : α) : with_zero α) = (a : with_zero α) * b := rfl

example [has_mul α] [has_one α] (x y : α) (h : (x : with_zero α) * y = 1) : x*y = 1 :=
by exact_mod_cast h

end hidden

example (k : ℕ) {x y : ℕ} :
  (x * x + y * y : ℤ) - ↑((x * y + 1) * k) = ↑y * ↑y - ↑k * ↑x * ↑y + (↑x * ↑x - ↑k) :=
begin
  push_cast,
  ring
end

example (k : ℕ) {x y : ℕ} (h : ((x + y + k : ℕ) : ℤ) = 0) : x + y + k = 0 :=
begin
  push_cast at h,
  guard_hyp h : (x : ℤ) + y + k = 0,
  assumption_mod_cast
end

example (a b : ℕ) (h2 : ((a + b + 0 : ℕ) : ℤ) = 10) :
  ((a + b : ℕ) : ℤ) = 10 :=
begin
  push_cast,
  push_cast [int.add_zero] at h2,
  exact h2
end

example {x : ℚ} : ((x + 42 : ℚ) : ℝ) = x + 42 := by push_cast

namespace ennreal

--TODO: debug
lemma half_lt_self_bis {a : ℝ≥0∞} (hz : a ≠ 0) (ht : a ≠ ⊤) : a / 2 < a :=
begin
  lift a to nnreal using ht,
  have h : (2 : ℝ≥0∞) = ((2 : nnreal) : ℝ≥0∞), from rfl,
  have h' : (2 : nnreal) ≠ 0, from _root_.two_ne_zero',
  rw [h, ← coe_div h', coe_lt_coe], -- `norm_cast` fails to apply `coe_div`
  norm_cast at hz,
  exact nnreal.half_lt_self hz
end

end ennreal

lemma b (h g : true) : true ∧ true :=
begin
 split,
 assumption_mod_cast,
 assumption_mod_cast,
end
