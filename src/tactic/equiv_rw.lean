/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.equiv.basic

/-!
# The `equiv_rw` tactic, which transports goals or hypotheses along equivalences.

This is a very preliminary implementation.
Really, we would like to be able to be able to rewrite under functors,
but this will require more tooling.
-/

namespace tactic

/--
Attempt to replace the hypothesis with name `x : α`
by transporting it along the equivalence in `e : α ≃ β`.
-/
meta def equiv_rw_hyp (x : name) (e : expr) : tactic unit :=
do x' ← get_local x,
   ty ← infer_type x',
   -- We establish `h : x = e.symm (e x)`.
   eq ← to_expr ``(%%x' = equiv.symm %%e (%%e %%x')),
   prf ← to_expr ``((equiv.symm_apply_apply %%e %%x').symm),
   h ← assertv_fresh eq prf,
   -- Revert the new hypothesis, so it is also part of the goal.
   revert h,
   ex ← to_expr ``(%%e %%x'),
   -- Now call `generalize`,
   -- attempting to replace all occurrences of `e x`,
   -- calling it for now `j : β`, with `k : x = e.symm j`.
   generalize ex (by apply_opt_param) transparency.none,
   j ← mk_fresh_name,
   intro j,
   k ← mk_fresh_name,
   -- Finally, we subst along `k`, hopefully removing all the occurrences of the original `x`,
   intro k >>= subst,
   -- and then rename `j` back to `x`.
   rename j x,
   skip

/--
`unroll_functors` will run the tactic `t`,
calling `apply functor.map` as many times as necessary first.
-/
meta def unroll_functors (t : tactic unit) :=
t <|> (`[apply functor.map] >> unroll_functors)

end tactic


namespace tactic.interactive
open lean.parser
open interactive interactive.types
open tactic

local postfix `?`:9001 := optional

/--
`equiv_rw e at h`, where `h : α` is a hypothesis, and `e : α ≃ β`,
will attempt to transport `h` along `e`, producing a new hypothesis `h : β`,
with all occurrences of `h` in other hypotheses and the goal replaced with `e.symm h`.

`equiv_rw e` tries `apply e.inv_fun`,
so with `e : α ≃ β`, it turns a goal of `⊢ α` into `⊢ β`.
It will also try rewriting under functors, so it can also turn
a goal of `⊢ option α` into `⊢ option β`.

(Note that rewriting hypotheses does not understand functors.)
-/
-- PROJECT Rewriting hypotheses under functors.
-- PROJECT More generally, rewriting along isomorphisms, under functors.
-- (See the `hygienic` branch of mathlib.)
meta def equiv_rw (e : parse texpr) (loc : parse $ (tk "at" *> ident)?) : itactic :=
do e ← to_expr e,
   match loc with
   | (some hyp) := tactic.equiv_rw_hyp hyp e
   | none := do s ← to_expr ``(equiv.inv_fun %%e),
                unroll_functors (tactic.apply s >> skip)
   end

add_tactic_doc
{ name        := "equiv_rw",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.equiv_rw],
  tags        := ["rewriting", "equiv", "transport"] }

end tactic.interactive
