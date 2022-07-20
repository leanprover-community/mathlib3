import data.real.basic

meta def test_repr (r : ℝ) (s : string) : tactic unit := guard (repr r = s)

run_cmd test_repr 0 "0"
run_cmd test_repr 1 "1"
run_cmd test_repr (37 : ℕ) "37"
run_cmd test_repr (3.7 : ℚ) "37/10"
run_cmd test_repr ⟨cau_seq.completion.mk $ ⟨λ n, 2^(-n:ℤ), sorry⟩⟩
                  "(⟨sorry /- 1,1/2,1/4,1/8,1/16,... -/⟩ : ℝ)"
