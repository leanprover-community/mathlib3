import data.real.irrational
import data.nat.fib
import tactic.ring_exp
import tactic.
/-! #AUTHORS : https://www.codewars.com/about/terms-of-service -/

noncomputable theory

@[reducible] def golden_ratio := (1 + real.sqrt 5)/2
@[reducible] def golden_conj := (1 - real.sqrt 5)/2

localized "notation `φ` := golden_ratio" in real
localized "notation `ψ` := golden_conj" in real

lemma gold_conj_eq_neg_inv_gold : ψ = -φ⁻¹ :=
begin
  have : 1 + real.sqrt 5 ≠ 0,
    from ne_of_gt (add_pos (by norm_num) $ real.sqrt_pos.mpr (by norm_num)),
  field_simp,
  apply mul_left_cancel' this,
  rw mul_div_cancel' _ this,
  rw ← sq_sub_sq,
  norm_num
end

lemma gold_mul_gold_conj : φ * ψ = -1 :=
by {field_simp, rw ← sq_sub_sq, norm_num}

lemma gold_add_gold_conj : φ + ψ = 1 := by {rw [golden_ratio, golden_conj], ring}

lemma one_sub_gold_conj : 1 - φ = ψ := by linarith [gold_add_gold_conj]

lemma one_sub_gold : 1 - ψ = φ := by linarith [gold_add_gold_conj]

lemma gold_sub_gold_conj : φ - ψ = real.sqrt 5 := by {rw [golden_ratio, golden_conj], ring}

lemma gold_sq : φ^2 = φ + 1 :=
begin
  rw [golden_ratio, ←sub_eq_zero],
  ring_exp,
  rw real.sqr_sqrt; norm_num,
end

lemma gold_conj_sq : ψ^2 = ψ + 1 :=
begin
  rw [golden_conj, ←sub_eq_zero],
  ring_exp,
  rw real.sqr_sqrt; norm_num,
end

/-!
## Irrationality
-/

theorem gold_irrational : irrational φ :=
begin
  have := nat.prime.irrational_sqrt (show nat.prime 5, by norm_num),
  have := this.rat_add 1,
  have := this.rat_mul (show (0.5 : ℚ) ≠ 0, by norm_num),
  convert this,
  field_simp
end

theorem gold_conj_irrational : irrational ψ :=
begin
  have := nat.prime.irrational_sqrt (show nat.prime 5, by norm_num),
  have := this.rat_sub 1,
  have := this.rat_mul (show (0.5 : ℚ) ≠ 0, by norm_num),
  convert this,
  field_simp
end

/-!
## Links with Fibonacci sequence
-/

theorem binet : ∀ n, (nat.fib n : ℝ) = (φ^n - ψ^n) / real.sqrt 5
| 0 := by simp
| 1 := by rw [golden_ratio, golden_conj, nat.fib_one]; ring_exp; rw mul_inv_cancel; norm_num
| (n + 2) :=
begin
  rw [nat.fib_succ_succ, nat.cast_add, binet, binet],
  simp only [pow_add, gold_sq, gold_conj_sq, pow_one],
  ring,
end
