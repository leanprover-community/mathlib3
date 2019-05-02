-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import data.list.defs

open tactic

meta def update_univ (p : list (level × level)) (l : level) : level :=
((p.find (λ q : level × level, q.1 = l)).map prod.snd).get_or_else l

meta def update_univs (p : list (level × level)) : expr → expr
| (expr.var n)        := expr.var n
| (expr.sort l)       := expr.sort (update_univ p l)
| (expr.const n ls)   := expr.const n (ls.map (update_univ p))
| (expr.mvar n m e)   := expr.mvar n m (update_univs e)
| (expr.local_const n m bi e) := expr.local_const n m bi (update_univs e)
| (expr.app f x)      := expr.app (update_univs f) (update_univs x)
| (expr.lam n bi d t) := expr.lam n bi (update_univs d) (update_univs t)
| (expr.pi n bi d t)  := expr.pi n bi (update_univs d) (update_univs t)
| (expr.elet n a b c) := expr.elet n (update_univs a) (update_univs b) (update_univs c)
| (expr.macro d es)   := expr.macro d (es.map update_univs)

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
do let old := d.univ_params.map level.param,
   e ← mk_const d.to_name,
   new ← match e with
   | (expr.const _ l) := some l
   | _ := none
   end,
   return (e, update_univs (old.zip new) d.type)
