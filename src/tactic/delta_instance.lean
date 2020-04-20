/-
Copyright (c) 2019 Rob Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob Lewis
-/
import tactic.simp_result

namespace tactic

/--
`delta_instance ids` tries to solve the goal by calling `apply_instance`,
first unfolding the definitions in `ids`.
-/
-- We call `dsimp_result` here because otherwise
-- `delta_target` will insert an `id` in the result.
-- See the note [locally reducible category instances]
-- https://github.com/leanprover-community/mathlib/blob/c9fca15420e2ad443707ace831679fd1762580fe/src/algebra/category/Mon/basic.lean#L27
-- for an example where this used to cause a problem.
meta def delta_instance (ids : list name) : tactic unit :=
dsimp_result
  (intros >> reset_instance_cache >> delta_target ids >> apply_instance >> done)
  { fail_if_unchanged := ff, } tt [] [simp_arg_type.expr ``(id)] -- this is `dsimp_result only [id]`

namespace interactive
setup_tactic_parser

meta def delta_instance (ids : parse ident*) : itactic :=
tactic.delta_instance ids
end interactive

/--
Tries to derive instances by unfolding the newly introduced type and applying type class resolution.

For example,
```lean
@[derive ring] def new_int : Type := ℤ
```
adds an instance `ring new_int`, defined to be the instance of `ring ℤ` found by `apply_instance`.

Multiple instances can be added with `@[derive [ring, module ℝ]]`.

This derive handler applies only to declarations made using `def`, and will fail on such a
declaration if it is unable to derive an instance. It is run with higher priority than the built-in
handlers, which will fail on `def`s.
-/
@[derive_handler, priority 2000] meta def delta_instance_handler : derive_handler :=
λ cls new_decl_name,
do env ← get_env,
if env.is_inductive new_decl_name then return ff else
do new_decl_type ← declaration.type <$> get_decl new_decl_name,
   new_decl_pexpr ← resolve_name new_decl_name,
   tgt ← to_expr $ apply_under_pis cls new_decl_pexpr new_decl_type,
   (_, inst) ← solve_aux tgt $ delta_instance [new_decl_name],
   inst ← instantiate_mvars inst,
   inst ← replace_univ_metas_with_univ_params inst,
   tgt ← instantiate_mvars tgt,
   nm ← get_unused_decl_name $ new_decl_name ++
     match cls with
     -- the postfix is needed because we can't protect this name. using nm.last directly can
     -- conflict with open namespaces
     | (expr.const nm _) := (nm.last ++ "_1" : string)
     | _ := "inst"
     end,
   add_decl $ mk_definition nm inst.collect_univ_params tgt inst,
   set_basic_attribute `instance nm tt,
   return tt

end tactic
