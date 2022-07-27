import data.real.basic

meta def test_repr (r : ℝ) (s : string) : tactic unit :=
guard (repr r = s) <|> fail!"got {repr r}"

run_cmd test_repr 0 "real.of_cauchy (sorry /- 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ... -/)"
run_cmd test_repr 1 "real.of_cauchy (sorry /- 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, ... -/)"
run_cmd test_repr (37 : ℕ) "real.of_cauchy (sorry /- 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, ... -/)"
run_cmd test_repr (2 + 3) "real.of_cauchy (sorry /- 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, ... -/)"
run_cmd test_repr ⟨cau_seq.completion.mk $ ⟨λ n, 2^(-n:ℤ), sorry⟩⟩
                  "real.of_cauchy (sorry /- 1, 1/2, 1/4, 1/8, 1/16, 1/32, 1/64, 1/128, 1/256, 1/512, ... -/)"
