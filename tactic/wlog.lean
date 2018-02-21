
import .tauto
import meta.expr

namespace tactic

open tactic
open lean.parser
open tactic.interactive (specialize)
open interactive
open interactive.types

local postfix `?`:9001 := optional
local postfix *:9001 := many

meta def subst_locals (s : list (expr × expr)) (e : expr) : expr :=
(e.abstract_locals (s.map (expr.local_uniq_name ∘ prod.fst)).reverse).instantiate_vars (s.map prod.snd)

meta def set_binder : expr → list binder_info → expr
 | e [] := e
 | (expr.pi v _ d b) (bi :: bs) := expr.pi v bi d (set_binder b bs)
 | e _ := e

open list

/-- `wlog h : i ≤ j using i j`: without loss of generality, let us assume `h : i ≤ j`
    If `using i j` is omitted, the last two free variables found in `i ≤ j` will be used.
  -/
meta def wlog (h : parse ident?)
              (p : parse (tk ":" *> texpr))
              (xy : parse (tk "using" *> monad.sequence [ident,ident])?)
: tactic unit :=
do p' ← to_expr p,
   (x :: y :: _) ← xy.to_monad >>= mmap get_local <|> pure p'.list_local_const,
   n ← tactic.revert_lst [x,y],
   x ← intro1, y ← intro1,
   p ← to_expr p,
   when (¬ x.occurs p ∨ ¬ x.occurs p) (do
     p ← pp p,
     fail format!"{p} should reference {x} and {y}"),
   let p' := subst_locals [(x,y),(y,x)] p,
   t ← target,
   let g := p.imp t,
   g ← tactic.pis [x,y] g,
   this ← assert `this (set_binder g [binder_info.default,binder_info.default]),
   tactic.clear x, tactic.clear y,
   intron 2,
   intro $ h.get_or_else `a, intron (n-2), tactic.swap,
   let h := h.get_or_else `this,
   h' ← to_expr ``(%%p ∨ %%p') >>= assert h,
   clear this,
   assumption <|> `[exact le_total _ _] <|> tactic.swap,
   (() <$ tactic.cases h' [`h,`h])
   ; specialize ```(%%this _ _ h)
   ; intron (n-2) ; try (auto <|> tauto <|> (intros >> cc)),
   return ()

run_cmd add_interactive [`wlog]

end tactic
