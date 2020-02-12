/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.tidy

-- TODO once the customisable hints infrastructure has settled, hook up:
-- norm_num, ring, linarith, tauto, omega

namespace tactic

namespace hint

meta def hint_attribute : user_attribute := {
  name := `hint,
  descr := "A tactic that should be tried by `hint`."
}

run_cmd attribute.register ``hint_attribute

open lean lean.parser interactive

meta def add_tactic_hint (n : name) (t : expr) : tactic unit :=
do
  add_decl $ declaration.defn n [] `(tactic string) t reducibility_hints.opaque ff,
  hint_attribute.set n () tt

@[user_command] meta def add_hint (_ : parse (tk "add_hint")) : parser unit :=
do t ← parser.pexpr,
   n ← parser.pexpr,
   -- gross: strip quotes off
   let h := n.to_string.to_list.tail.reverse.tail.reverse.as_string ++ "_hint",
   of_tactic $ do
   t ← to_expr ``(do %%t, pure %%n),
   add_tactic_hint h t.

-- TODO can we get away with just one argument here, since they're always "the same"? which?
add_hint `[refl] "refl"
add_hint `[exact dec_trivial] "exact dec_trivial"
add_hint `[assumption] "assumption" -- since `assumption` is already a `tactic unit`, the `[ ... ] is not strictly necessary here
add_hint `[intros] "intros" -- tidy does something better here: it suggests the actual "intros X Y f" string
-- Since `auto_cases` is already a "self-reporting tactic",
-- i.e. a `tactic string` that returns a tactic script,
-- we can just add the attribute:
attribute [hint] auto_cases
add_hint `[apply_auto_param]  "apply_auto_param"
add_hint `[dsimp at *] "dsimp at *"
add_hint `[simp at *] "simp at *" -- TODO hook up to squeeze_simp?
attribute [hint] tidy.ext1_wrapper
add_hint `[fsplit] "fsplit"
add_hint `[injections_and_clear] "injections_and_clear"
add_hint `[solve_by_elim] "solve_by_elim"
add_hint `[unfold_coes] "unfold_coes"
add_hint `[unfold_aux] "unfold_aux"

end hint

/-- report a list of tactics that can make progress against the current goal -/
meta def hint : tactic (list string) :=
do names ← attribute.get_instances `hint,
   try_all (names.reverse.map tidy.name_to_tactic)

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
