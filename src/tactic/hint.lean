/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.tidy

namespace tactic

namespace hint

/-- An attribute marking a `tactic unit` or `tactic string` which should be used by the `hint` tactic. -/
meta def hint_attribute : user_attribute := {
  name := `hint,
  descr := "A tactic that should be tried by `hint`."
}

run_cmd attribute.register ``hint_attribute

open lean lean.parser interactive

private meta def add_tactic_hint (n : name) (t : expr) : tactic unit :=
do
  add_decl $ declaration.defn n [] `(tactic string) t reducibility_hints.opaque ff,
  hint_attribute.set n () tt,
  nolint_attr.set n () tt

/--
`add_hint t` runs the tactic `t` whenever `hint` is invoked.
The typical use case is `add_hint "foo"` for some interactive tactic `foo`.
-/
@[user_command] meta def add_hint (_ : parse (tk "add_hint")) : parser unit :=
do n ← parser.pexpr,
   e ← to_expr n,
   s ← eval_expr string e,
   let t := "`[" ++ s ++ "]",
   (t, _) ← with_input parser.pexpr t,
   of_tactic $ do
   let h := s ++ "_hint",
   t ← to_expr ``(do %%t, pure %%n),
   add_tactic_hint h t.

add_hint "refl"
add_hint "exact dec_trivial"
add_hint "assumption"
add_hint "intros" -- tidy does something better here: it suggests the actual "intros X Y f" string; perhaps add a wrapper?
-- Since `auto_cases` is already a "self-reporting tactic",
-- i.e. a `tactic string` that returns a tactic script,
-- we can just add the attribute:
attribute [hint] auto_cases
add_hint "apply_auto_param"
add_hint "dsimp at *"
add_hint "simp at *" -- TODO hook up to squeeze_simp?
attribute [hint] tidy.ext1_wrapper
add_hint "fsplit"
add_hint "injections_and_clear"
add_hint "solve_by_elim"
add_hint "unfold_coes"
add_hint "unfold_aux"

end hint

/-- report a list of tactics that can make progress against the current goal -/
meta def hint : tactic (list string) :=
do names ← attribute.get_instances `hint,
   try_all (names.reverse.map tidy.name_to_tactic)

namespace interactive

/-- report a list of tactics that can make progress against the current goal -/
meta def hint : tactic unit :=
do hints ← tactic.hint,
   if hints.length = 0 then
     fail "no hints available"
   else
     do trace "the following tactics make progress:\n----",
        hints.mmap tactic.trace

end interactive

end tactic
