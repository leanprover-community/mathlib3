import data.int.parity
import tactic.interval_cases2
import tactic

--set_option profiler true

lemma mod8_odd' (b : ℤ) (hlo : 0 ≤ b) (hhi : b < 8) (hodd : odd b) :
  b = 1 ∨ b = 3 ∨ b = 5 ∨ b = 7 :=
begin
  rw int.odd_iff at hodd,
  interval_cases' b; norm_num at hodd; norm_num,
end

example (n : ℕ) (w₁ : n ≥ 3) (w₂ : n < 5) : n = 3 ∨ n = 4 :=
begin
  interval_cases' n,
  all_goals {simp},
end

example (n : ℕ) (f : ℕ → ℤ) (w₁ : f n > -2) (w₂ : f n < 2) : f n ∈ ({-1, 0, 1} : set ℤ) :=
begin
  interval_cases' f n with h,
  all_goals { simp [h] },
end


example (n : ℕ) (h : n ∈ set.Ico 1 4) : n * n < 16 :=
begin
  interval_cases' n using [set.mem_Ico.mp h]; norm_num
end

example (n : ℕ) (h : 3 ≤ n ∧ n ≤ 40) : (22^n + 8) % 24 = 0 :=
begin
  interval_cases' n; norm_num,
end
