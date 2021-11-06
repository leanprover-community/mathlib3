/-
Copyright (c) 2020 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import logic.basic
import data.rbmap.basic

/-!
# Derive handler for `inhabited` instances

This file introduces a derive handler to automatically generate `inhabited`
instances for structures and inductives. We also add various `inhabited`
instances for types in the core library.
-/

namespace tactic

/--
Tries to derive an `inhabited` instance for inductives and structures.

For example:
```
@[derive inhabited]
structure foo :=
(a : ℕ := 42)
(b : list ℕ)
```
Here, `@[derive inhabited]` adds the instance `foo.inhabited`, which is defined as
`⟨⟨42, default (list ℕ)⟩⟩`.  For inductives, the default value is the first constructor.

If the structure/inductive has a type parameter `α`, then the generated instance will have an
argument `inhabited α`, even if it is not used.  (This is due to the implementation using
`instance_derive_handler`.)
-/
@[derive_handler] meta def inhabited_instance : derive_handler :=
instance_derive_handler ``inhabited $ do
applyc ``inhabited.mk,
`[refine {..}] <|> (constructor >> skip),
all_goals' $ do
  applyc ``default <|> (do s ← read,
    fail $ to_fmt "could not find inhabited instance for:\n" ++ to_fmt s)

end tactic

attribute [derive inhabited]
  vm_decl_kind vm_obj_kind
  tactic.new_goals tactic.transparency tactic.apply_cfg
  smt_pre_config ematch_config cc_config smt_config
  rsimp.config
  tactic.dunfold_config tactic.dsimp_config tactic.unfold_proj_config
  tactic.simp_intros_config tactic.delta_config tactic.simp_config
  tactic.rewrite_cfg
  interactive.loc
  tactic.unfold_config
  param_info subsingleton_info fun_info
  format.color
  pos
  environment.projection_info
  reducibility_hints
  congr_arg_kind
  ulift
  plift
  string_imp string.iterator_imp
  rbnode.color
  ordering
  unification_constraint pprod unification_hint
  doc_category
  tactic_doc_entry

instance {α} : inhabited (bin_tree α) := ⟨bin_tree.empty⟩

instance : inhabited unsigned := ⟨0⟩
instance : inhabited string.iterator := string.iterator_imp.inhabited

instance {α} : inhabited (rbnode α) := ⟨rbnode.leaf⟩
instance {α lt} : inhabited (rbtree α lt) := ⟨mk_rbtree _ _⟩
instance {α β lt} : inhabited (rbmap α β lt) := ⟨mk_rbmap _ _ _⟩
