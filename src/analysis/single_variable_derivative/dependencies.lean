import data.real.basic
import analysis.exponential

open real

theorem pow_lt {x y : ℝ} {n : ℕ} (Hxy : x < y) (Hxpos : 0 < x) (Hnpos : 0 < n) : x ^ n < y ^ n :=
begin
  rw ←nat.sub_add_cancel Hnpos,
  induction (n - 1), { simpa only [pow_one] },
  rw [pow_add, pow_add, nat.succ_eq_add_one, pow_one, pow_one],
  apply mul_lt_mul ih (le_of_lt Hxy) Hxpos (le_of_lt (pow_pos (lt_trans Hxpos Hxy) _))
end

theorem pow_right_inj {x y : ℝ} {n : ℕ} (Hxpos : 0 < x) (Hypos : 0 < y) (Hnpos : 0 < n) (Hxyn : x ^ n = y ^ n) : x = y :=
begin
  rcases lt_trichotomy x y with hxy | rfl | hyx,
  { exact absurd Hxyn (ne_of_lt (pow_lt hxy Hxpos Hnpos)) },
  { refl },
  { exact absurd Hxyn (ne_of_gt (pow_lt hyx Hypos Hnpos)) },
end

noncomputable definition nth_root (x : ℝ) (n : ℕ) : ℝ := 
if x = 0 then 0 else exp ((log x) / n)

theorem exp_mul (x : ℝ) : ∀ n : ℕ, real.exp(n*x) = (real.exp(x))^n
| 0 := by rw [nat.cast_zero, zero_mul, real.exp_zero, pow_zero]
| (nat.succ n) := by rw [pow_succ', nat.cast_add_one, add_mul, real.exp_add, ←exp_mul, one_mul]

theorem nth_root_pos {x n} : x ≠ 0 → nth_root x n > 0 := by intro; simp [a, nth_root]; apply exp_pos

theorem nth_root_power {x : ℝ} {n} (Hxpos : 0 < x) (Hnpos : 0 < n): (nth_root x n) ^ n = x := 
begin
  simp [ne_of_gt Hxpos, nth_root],
  rw [←exp_mul, mul_div_cancel', exp_log Hxpos], 
  rw nat.cast_ne_zero, exact ne_of_gt Hnpos
end

theorem nth_root_unique {x y : ℝ} {n : ℕ}
(Hxpos : 0 < x) (Hypos : 0 < y) (Hnpos : 0 < n) (Hynx : y ^ n = x) : y = nth_root x n 
:= pow_right_inj Hypos (nth_root_pos (ne_of_gt Hxpos)) Hnpos (Hynx.trans (nth_root_power Hxpos Hnpos).symm)

theorem abs_pow (x : ℝ) : ∀ n : ℕ, abs(x ^ n) = (abs x) ^ n
| 0 := by simp
| (nat.succ n) := by rw [pow_succ, pow_succ, abs_mul, abs_pow]

theorem exp_lt_exp_iff (x y : ℝ) : x < y ↔ exp x < exp y :=
begin
  split,
  { exact exp_lt_exp },
  { intro,
    cases classical.em (x < y),
    { exact h },
    { exfalso,
      cases (eq_or_lt_of_le(le_of_not_lt h)) with hl he,
      { rw hl at a, apply ne_of_lt a rfl },
      { apply not_lt_of_gt a (exp_lt_exp he) } } }
end

theorem log_pos {x : ℝ} (hx : 1 < x) : log x > 0 :=
begin
  have hx' := hx, rw ←exp_log (lt_trans (by norm_num) hx') at hx,
  rwa [←exp_zero, ←exp_lt_exp_iff] at hx,
end
