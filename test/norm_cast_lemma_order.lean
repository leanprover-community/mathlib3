import data.nat.cast
import tactic.norm_cast

constant ℝ : Type
@[instance] constant real.add_monoid : add_monoid ℝ
@[instance] constant real.has_one : has_one ℝ

-- set_option trace.simplify.rewrite true
set_option pp.notation false
set_option pp.numerals false

-- should work
run_cmd norm_cast.numeral_to_coe `(0 : ℝ)
run_cmd norm_cast.numeral_to_coe `(1 : ℝ)
run_cmd norm_cast.numeral_to_coe `(2 : ℝ)
run_cmd norm_cast.numeral_to_coe `(3 : ℝ)

run_cmd norm_cast.coe_to_numeral `((0 : ℕ) : ℝ)
run_cmd norm_cast.coe_to_numeral `((1 : ℕ) : ℝ)
run_cmd norm_cast.coe_to_numeral `((2 : ℕ) : ℝ)
run_cmd norm_cast.coe_to_numeral `((3 : ℕ) : ℝ)
