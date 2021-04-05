/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.solve_by_elim
import tactic.interactive

namespace tactic

namespace hint

/-- An attribute marking a `tactic unit` or `tactic string` which should be used by the `hint`
tactic. -/
@[user_attribute] meta def hint_tactic_attribute : user_attribute := {
  name := `hint_tactic,
  descr := "A tactic that should be tried by `hint`."
}

add_tactic_doc
{ name                     := "hint_tactic",
  category                 := doc_category.attr,
  decl_names               := [`tactic.hint.hint_tactic_attribute],
  tags                     := ["rewrite", "search"] }

open lean lean.parser interactive

private meta def add_tactic_hint (n : name) (t : expr) : tactic unit :=
do
  add_decl $ declaration.defn n [] `(tactic string) t reducibility_hints.opaque ff,
  hint_tactic_attribute.set n () tt

/--
`add_hint_tactic t` runs the tactic `t` whenever `hint` is invoked.
The typical use case is `add_hint_tactic "foo"` for some interactive tactic `foo`.
-/
@[user_command] meta def add_hint_tactic (_ : parse (tk "add_hint_tactic")) : parser unit :=
do n ← parser.pexpr,
   e ← to_expr n,
   s ← eval_expr string e,
   let t := "`[" ++ s ++ "]",
   (t, _) ← with_input parser.pexpr t,
   of_tactic $ do
   let h := s <.> "_hint",
   t ← to_expr ``(do %%t, pure %%n),
   add_tactic_hint h t.

add_tactic_doc
{ name                     := "add_hint_tactic",
  category                 := doc_category.cmd,
  decl_names               := [`tactic.hint.add_hint_tactic],
  tags                     := ["search"] }

add_hint_tactic "refl"
add_hint_tactic "exact dec_trivial"
add_hint_tactic "assumption"
-- tidy does something better here: it suggests the actual "intros X Y f" string.
-- perhaps add a wrapper?
add_hint_tactic "intro"
add_hint_tactic "apply_auto_param"
add_hint_tactic "dsimp at *"
add_hint_tactic "simp at *" -- TODO hook up to squeeze_simp?
add_hint_tactic "fconstructor"
add_hint_tactic "injections_and_clear"
add_hint_tactic "solve_by_elim"
add_hint_tactic "unfold_coes"
add_hint_tactic "unfold_aux"

end hint

/--
Report a list of tactics that can make progress against the current goal,
and for each such tactic, the number of remaining goals afterwards.
-/
meta def hint : tactic (list (string × ℕ)) :=
do
  names ← attribute.get_instances `hint_tactic,
  focus1 $ try_all_sorted (names.reverse.map name_to_tactic)

namespace interactive

/--
Report a list of tactics that can make progress against the current goal.
-/
meta def hint : tactic unit :=
do
  hints ← tactic.hint,
  if hints.length = 0 then
    fail "no hints available"
  else do
    t ← hints.nth 0,
    if t.2 = 0 then do
      trace "the following tactics solve the goal:\n----",
      (hints.filter (λ p : string × ℕ, p.2 = 0)).mmap' (λ p, tactic.trace format!"Try this: {p.1}")
    else do
      trace "the following tactics make progress:\n----",
      hints.mmap' (λ p, tactic.trace format!"Try this: {p.1}")

/--
`hint` lists possible tactics which will make progress (that is, not fail) against the current goal.

```lean
example {P Q : Prop} (p : P) (h : P → Q) : Q :=
begin
  hint,
  /- the following tactics make progress:
     ----
     Try this: solve_by_elim
     Try this: finish
     Try this: tauto
  -/
  solve_by_elim,
end
```

You can add a tactic to the list that `hint` tries by either using
1. `attribute [hint_tactic] my_tactic`, if `my_tactic` is already of type `tactic string`
(`tactic unit` is allowed too, in which case the printed string will be the name of the
tactic), or
2. `add_hint_tactic "my_tactic"`, specifying a string which works as an interactive tactic.
-/
add_tactic_doc
{ name        := "hint",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.hint],
  tags        := ["search", "Try this"] }

end interactive

end tactic
