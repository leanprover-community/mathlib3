import tactic.suggest
import analysis.special_functions.exp

open real

/- Turn off trace messages so they don't pollute the test build: -/
set_option trace.silence_library_search true

example {a b : ℝ} (h: a ≤ b) : exp a ≤ exp b := by library_search
