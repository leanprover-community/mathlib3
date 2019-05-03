-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Mario Carneiro

open tactic

/--
Returns a pair (e, t), where `e ← mk_const d.to_name`, and `t = d.type`
but with universe params updated to match the fresh universe metavariables in `e`.

This should have the same effect as just
```
do e ← mk_const d.to_name,
   t ← infer_type e,
   return (e, t)
```
but is hopefully faster.
-/
meta def decl_mk_const (d : declaration) : tactic (expr × expr) :=
do subst ← d.univ_params.mmap $ λ u, prod.mk u <$> mk_meta_univ,
   let e : expr := expr.const d.to_name (prod.snd <$> subst),
   return (e, d.type.instantiate_univ_params subst)
