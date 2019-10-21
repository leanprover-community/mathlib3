import data.rat.meta

run_cmd guard $ (reflect (3/15 : ℚ) : expr) = `((3/15 : ℚ))

constants (α : Type) (h : field α)

attribute [instance] h

run_cmd guard $ expr.eval_rat `(1/3 - 100/6 : α) = some (-49/3)

run_cmd guard $ (expr.eval_rat ∘ rat.reflect) (-(5/3) : ℚ) = some (-5/3)
