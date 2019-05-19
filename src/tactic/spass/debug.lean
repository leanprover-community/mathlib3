/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  Tactics for debugging the spass tacric.
-/

import tactic.spass.main

open tactic

meta def recipe.derives_debug (m : mat) : recipe → tactic cla
| (recipe.hyp k)   :=
  (do c ← m.nth k,
      trace (k.repr ++ "-th clause retrieved : " ++ c.repr),
      return c)
  <|> (trace "Failed Hyp" >> failed)
| (recipe.prm d ρ) :=
   do c ← ρ.derives_debug,
      if cla.exteq c d
      then return d
      else do trace "failed prm, cannot permutate ",
              trace c,
              trace " into ",
              trace d,
              failed
| (recipe.sub μ ρ) :=
  ( do trace "Enter sub",
     c ← ρ.derives_debug,
     trace "Returning sub : ",
     trace (c.subst μ),
     return (c.subst μ) ) <|> (trace "failed sub" >> failed)
| (recipe.con ff k ρ) :=
  ( do c ← ρ.derives_debug,
     t ← c.fst.nth k,
     guard (t ∈ c.fst.remove_nth k),
     return (c.fst.remove_nth k, c.snd) ) <|> (trace "failed con" >> failed)
| (recipe.con tt k ρ) :=
  ( do c ← ρ.derives_debug,
       t ← c.snd.nth k,
       guard (t ∈ c.snd.remove_nth k),
       return (c.fst, c.snd.remove_nth k) ) <|>
  (trace "failed con" >> failed)
| (recipe.res k n ρ σ) :=
  ( do trace "Enter Res",
     c ← ρ.derives_debug,
     d ← σ.derives_debug,
     t ← c.snd.nth k,
     s ← d.fst.nth n,
     trace "Test guard",
     guard (t = s),
     trace "Guard passed",
     return (c.fst ++ d.fst.remove_nth n,
      c.snd.remove_nth k ++ d.snd) )
  <|> (trace "failed res" >> failed)

meta def prove_arifix_debug (αx ix : expr) (p : form₂) : tactic recipe :=
do s ← spass_output (mat.print $ clausify p),
   ls ← parse.lines s,
   ρx ← compile (clausify p) ls,
   eval_expr recipe ρx

meta def spass_debug : tactic unit :=
do (dx, ix, p) ← reify,
   yx ← prove_arifix_debug dx ix p,
   c ← (yx.derives_debug $ clausify p),
   skip
