/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import tactic.core

/-!
# mk_opaque

Tactic mk_opaque turns local definitions into local constants
-/

namespace tactic

setup_tactic_parser

/-- `mk_opaque x y z`, with `x`, `y`, `z` local definitions, transforms them into
normal local constants

In the goal:

```lean
x y : ℤ,
z : ℤ := x + y
⊢ P
```

`mk_opaque z` yields the following goal:

```lean
x y : ℤ,
z : ℤ
⊢ P
```
-/
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
