/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/
import tactic.core


/-!
# Better `rename` tactic

This module defines a variant of the standard `rename` tactic, with the
following improvements:

* You can rename multiple hypotheses at the same time.
* Renaming a hypothesis does not change its location in the context.
-/


open lean lean.parser interactive native


namespace tactic

/-- Get the revertible part of the local context. These are the hypotheses that
appear after the last frozen local instance in the local context. We call them
revertible because `revert` can revert them, unlike those hypotheses which occur
before a frozen instance. -/
meta def revertible_local_context : tactic (list expr) := do
  ctx ← local_context,
  frozen ← frozen_local_instances,
  pure $
    match frozen with
    | none := ctx
    | some [] := ctx
    | some (h :: _) := ctx.after (eq h)
    end

/-- Rename local hypotheses according to the given `name_map`. The `name_map`
contains as keys those hypotheses that should be renamed; the associated values
are the new names.

This tactic can only rename hypotheses which occur after the last frozen local
instance. If you need to rename earlier hypotheses, try
`unfreeze_local_instances`.

If `strict` is true, we fail if `name_map` refers to hypotheses that do not
appear in the local context or that appear before a frozen local instance.
Conversely, if `strict` is false, some entries of `name_map` may be silently
ignored.

Note that we allow shadowing, so renamed hypotheses may have the same name
as other hypotheses in the context.
-/
meta def rename' (renames : name_map name) (strict := tt) : tactic unit := do
  ctx ← revertible_local_context,
  when strict (do
    let ctx_names := rb_map.set_of_list (ctx.map expr.local_pp_name),
    let invalid_renames :=
      (renames.to_list.map prod.fst).filter (λ h, ¬ ctx_names.contains h),
    when ¬ invalid_renames.empty $ fail $ format.join
      [ "Cannot rename these hypotheses:\n"
      , format.intercalate ", " (invalid_renames.map to_fmt)
      , format.line
      , "This is because these hypotheses either do not occur in the\n"
      , "context or they occur before a frozen local instance.\n"
      , "In the latter case, try `tactic.unfreeze_local_instances`."
      ]),
  let new_name := λ current_name,
    (renames.find current_name).get_or_else current_name,
  let intro_names := list.map (new_name ∘ expr.local_pp_name) ctx,
  revert_lst ctx,
  intro_lst intro_names,
  pure ()

end tactic


namespace tactic.interactive

/-- Parse a current name and new name for `rename'`. -/
meta def rename'_arg_parser : parser (name × name) :=
  prod.mk <$> ident <*> (optional (tk "->") *> ident)

/-- Parse the arguments of `rename'`. -/
meta def rename'_args_parser : parser (list (name × name)) :=
  (functor.map (λ x, [x]) rename'_arg_parser)
  <|>
  (tk "[" *> sep_by (tk ",") rename'_arg_parser <* tk "]")

/--
Rename one or more local hypotheses. The renamings are given as follows:

```
rename' x y             -- rename x to y
rename' x → y           -- ditto
rename' [x y, a b]      -- rename x to y and a to b
rename' [x → y, a → b]  -- ditto
```

Brackets are necessary if multiple hypotheses should be renamed in parallel.
-/
meta def rename' (renames : parse rename'_args_parser) : tactic unit :=
  tactic.rename' (rb_map.of_list renames)

end tactic.interactive
