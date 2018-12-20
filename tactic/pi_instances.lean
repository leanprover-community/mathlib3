/-
Copyright (c) 2018 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Automation for creating instances of mathematical structures for pi types
-/

import tactic.interactive order.basic

namespace tactic

open interactive interactive.types lean.parser expr
open functor has_seq list nat tactic.interactive

meta def derive_field : tactic unit :=
do b ← target >>= is_prop,
   field ← get_current_field,
   if b then do
     field ← get_current_field,
     vs ← introv [] <|> pure [],
     hs ← intros <|> pure [],
     resetI,
     x ← get_unused_name,
     try (() <$ ext1 [rcases_patt.one x] <|> () <$ intro x),
     x' ← try_core (get_local x),
     applyc field,
     hs.mmap (λ h, try $
       () <$ (to_expr ``(congr_fun %%h %%(x'.iget)) >>= apply) <|>
       () <$ apply (h x'.iget) <|>
       () <$ (to_expr ``(set.mem_image_of_mem _ %%h) >>= apply) <|>
       () <$ (solve_by_elim) ),
     return ()
   else focus1 $ do
     field ← get_current_field,
     e ← mk_const field,
     expl_arity ← get_expl_arity e,
     xs ← (iota expl_arity).mmap $ λ _, intro1,
     x ← intro1,
     applyc field,
     xs.mmap' (λ h, try $ () <$ (apply (h x) <|> apply h) <|> refine ``(set.image ($ %%x) %%h)) <|> fail "args",
     return ()

/--
`pi_instance` constructs an instance of `my_class (Π i : I, f i)`
where we know `Π i, my_class (f i)`. If an order relation is required,
it defaults to `pi.partial_order`. Any field of the instance that
`pi_instance` cannot construct is left untouched and generated as a new goal.
-/
meta def pi_instance : tactic unit :=
refine_struct ``( {  ..pi.partial_order, .. } );
  propagate_tags (try (derive_field ; done))

run_cmd add_interactive [`pi_instance]

end tactic
