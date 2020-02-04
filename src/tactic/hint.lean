/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.tidy
import tactic.norm_num
import tactic.omega
import tactic.linarith

namespace tactic

namespace hint

meta def default_tactics : list (tactic string) :=
[ reflexivity                                 >> pure "refl",
  `[exact dec_trivial]                        >> pure "exact dec_trivial",
  propositional_goal >> assumption            >> pure "assumption",
  intros1                                     >>= λ ns, pure ("intros " ++ (" ".intercalate (ns.map (λ e, e.to_string)))),
  auto_cases,
  `[apply_auto_param]                         >> pure "apply_auto_param",
  `[dsimp at *]                               >> pure "dsimp at *",
  `[simp at *]                                >> pure "simp at *",
  tidy.ext1_wrapper,
  fsplit                                      >> pure "fsplit",
  injections_and_clear                        >> pure "injections_and_clear",
  propositional_goal >> (`[solve_by_elim])    >> pure "solve_by_elim",
  `[unfold_coes]                              >> pure "unfold_coes",
  `[unfold_aux]                               >> pure "unfold_aux",
  `[split_ifs]                                >> pure "split_ifs",
  `[norm_num]                                 >> pure "norm_num",
  `[ring]                                     >> pure "ring",
  `[linarith]                                 >> pure "linarith",
  `[finish]                                   >> pure "finish",
  `[tauto]                                    >> pure "tauto" ]

end hint

/-- report a list of tactics that can make progress against the current goal -/
meta def hint : tactic (list string) :=
try_all tactic.hint.default_tactics

namespace interactive

/-- report a list of tactics that can make progress against the current goal -/
meta def hint :=
do hints ← tactic.hint,
   if hints.length = 0 then
     fail "no hints available"
   else
     do trace "the following tactics make progress:\n----",
        hints.mmap tactic.trace

end interactive

end tactic
