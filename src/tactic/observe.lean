/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import tactic.suggest

/-!
# observe

The `observe` tactic is mainly intended for demo/educational purposes.
Calling `observe hp : p` is equivalent to `have hp : p, { library_search }`.
-/

open tactic tactic.interactive
setup_tactic_parser

/-- `observe hp : p` asserts the proposition `p`, and tries to prove it using `library_search`.
If no proof is found, the tactic fails.
In other words, this tactic is equivalent to `have hp : p, { library_search }`.

If `hp` is omitted, then the placeholder `this` is used.

The variant `observe? hp : p` will emit a trace message of the form `have hp : p := proof_term`.
This may be particularly useful to speed up proofs. -/
meta def tactic.interactive.observe (trc : parse $ optional (tk "?"))
  (h : parse ident?) (t : parse (tk ":" *> texpr)) : tactic unit := do
  let h' := h.get_or_else `this,
  t ← to_expr ``(%%t : Prop),
  assert h' t,
  s ← focus1 (tactic.library_search { try_this := ff }) <|> fail "observe failed",
  s ← s.get_rest "Try this: exact ",
  ppt ← pp t,
  let pph : string := (h.map (λ n : name, n.to_string ++ " ")).get_or_else "",
  when trc.is_some $ trace! "Try this: have {pph}: {ppt} := {s}"

add_tactic_doc
{ name       := "observe",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.observe],
  tags       := ["search", "Try this"] }
