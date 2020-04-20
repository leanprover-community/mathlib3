import meta.expr

open tactic

run_cmd do
  l ← mk_local' `l binder_info.default `(ℕ),
  m ← mk_local' `m binder_info.default `(ℕ),
  guard $ `(%%l + %%l = 3).has_local_constant l,
  guard $ bnot $ `(%%l + %%l = 3).has_local_constant m,
  guard $ `(%%l + %%m = 3).has_local_constant l,
  guard $ `(%%l + %%m = 3).has_local_constant m

/- `expr_lens` tests -/

meta def my_test_expr : expr :=
expr.app
  (expr.app (expr.const `myfun1 []) (expr.const `myarg2 []))
  (expr.app (expr.const `myfun2 []) (expr.const `myarg2 []))

meta def test_expect_success (ls : list side) : tactic unit :=
do (l, e) ← expr_lens.entire.zoom ls my_test_expr,
   if ¬(l.to_sides = ls)   then tactic.fail "failed" else tactic.skip,
   if ¬(my_test_expr = l.fill e) then tactic.fail "failed" else tactic.skip

meta def test_expect_fail (ls : list side) : tactic unit :=
do res ← do { test_expect_success ls, return tt } <|> return ff,
   if res then tactic.fail "failed" else tactic.skip

/- Check no descent -/
run_cmd (test_expect_success [])

/- Check descent on the left -/
run_cmd (test_expect_success [side.L])
run_cmd (test_expect_success [side.L, side.R])
run_cmd (test_expect_success [side.L, side.L])

/- Check descent on the right -/
run_cmd (test_expect_success [side.R])
run_cmd (test_expect_success [side.R, side.R])
run_cmd (test_expect_success [side.R, side.L])

/- Check impossible descent -/
run_cmd (test_expect_fail [side.L, side.L, side.R])
run_cmd (test_expect_fail [side.R, side.L, side.R])
