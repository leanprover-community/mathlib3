import algebra.order.hom.basic
import tactic.positivity

namespace tactic
open positivity

/-- Extension for the `positivity` tactic: nonnegative maps take nonnegative values. -/
@[positivity]
meta def positivity_map : expr → tactic strictness
| (expr.app `(⇑%%f) `(%%a)) := nonnegative <$> mk_app ``map_nonneg [f, a]
| _ := failed

end tactic
