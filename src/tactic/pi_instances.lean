/-
Copyright (c) 2018 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import order.basic

/-!
# `pi_instance`

Automation for creating instances of mathematical structures for pi types
-/

namespace tactic

open tactic.interactive

/-- Attempt to clear a goal obtained by refining a `pi_instance` goal. -/
meta def pi_instance_derive_field : tactic unit :=
do b ← target >>= is_prop,
   field ← get_current_field,
   if b then do
     vs ← introv [] <|> pure [],
     hs ← intros <|> pure [],
     reset_instance_cache,
     xn ← get_unused_name,
     try (() <$ ext1 [rcases_patt.one xn] <|> () <$ intro xn),
     xv ← option.iget <$> try_core (get_local xn),
     applyc field,
     hs.mmap (λ h, try $
       () <$ (to_expr ``(congr_fun %%h %%xv) >>= apply) <|>
       () <$ apply (h xv) <|>
       () <$ (to_expr ``(set.mem_image_of_mem _ %%h) >>= apply) <|>
       () <$ solve_by_elim),
     return ()
   else focus1 $ do
     expl_arity ← mk_const field >>= get_expl_arity,
     xs ← (list.iota expl_arity).mmap $ λ _, intro1,
     x ← intro1,
     applyc field,
     xs.mmap' (λ h, try $
      () <$ (apply (h x) <|> apply h) <|>
      refine ``(set.image ($ %%x) %%h)) <|> fail "args",
     return ()

/--
`pi_instance` constructs an instance of `my_class (Π i : I, f i)`
where we know `Π i, my_class (f i)`. If an order relation is required,
it defaults to `pi.partial_order`. Any field of the instance that
`pi_instance` cannot construct is left untouched and generated as a new goal.
-/
meta def pi_instance : tactic unit :=
refine_struct ``( { ..pi.partial_order, .. } );
  propagate_tags (try $ pi_instance_derive_field >> done)

run_cmd add_interactive [`pi_instance]

add_tactic_doc
{ name                     := "pi_instance",
  category                 := doc_category.tactic,
  decl_names               := [`tactic.interactive.pi_instance],
  tags                     := ["type class"] }

end tactic
