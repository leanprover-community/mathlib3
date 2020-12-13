import tactic.norm_cast
import data.int.cast

set_option pp.numerals false
set_option pp.notation false
-- set_option trace.simplify.rewrite true

run_cmd norm_cast.numeral_to_coe `(0 : ℤ)
run_cmd norm_cast.numeral_to_coe `(1 : ℤ)
run_cmd norm_cast.numeral_to_coe `(2 : ℤ)
run_cmd norm_cast.numeral_to_coe `(3 : ℤ)

run_cmd norm_cast.coe_to_numeral `((0 : ℕ) : ℤ)
run_cmd norm_cast.coe_to_numeral `((1 : ℕ) : ℤ)
run_cmd norm_cast.coe_to_numeral `((2 : ℕ) : ℤ)
run_cmd norm_cast.coe_to_numeral `((3 : ℕ) : ℤ)

example : ((42 : ℕ) : ℤ) = 42 := by norm_cast
