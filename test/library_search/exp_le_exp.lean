import tactic.suggest
import analysis.special_functions.exp_log

open real

example {a b : ℝ} (h: a ≤ b) : exp a ≤ exp b := by library_search
