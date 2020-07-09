import tactic.core

namespace tactic

setup_tactic_parser

/-- `mk_opaque x y z`, with `x`, `y`, `z` local definitions, transforms them into
normal local constants -/
meta def interactive.mk_opaque (ns : parse ident*) : tactic unit :=
ns.mmap' $ λ n,
do h ← get_local n,
   n ← revert h,
   (expr.elet v t d b) ← target | fail "not a let expression",
   let e := expr.pi v binder_info.default t b,
   g ← mk_meta_var e,
   tactic.exact $ g d,
   gs ← get_goals,
   set_goals $ g :: gs,
   intron n

end tactic
