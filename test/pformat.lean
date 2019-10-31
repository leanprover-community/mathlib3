import tactic.core
open tactic

run_cmd do
  e ← to_expr ``(3 + 7),
  r ← pformat!"{e} : {infer_type e}",
  guard $ to_string r = "3 + 7 : ℕ",
  skip
