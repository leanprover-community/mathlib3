import data.nat.prime
import tactic
import tactic.by_contra


namespace tactic
namespace interactive
setup_tactic_parser

/-- `observe hp : p` asserts the proposition `p`, and tries to prove it using `library_search`.
If no proof is found, the tactic fails.
In other words, this tactic is equivalent to `have hp : p, { library_search }`.

If `hp` is omitted, then the placeholder `this` is used.
The variant `observe? hp : p` will omit a trace message of the form `have hp : p := proof_term`. -/
meta def observe (trc : parse $ optional (tk "?"))
  (h : parse ident?) (t : parse (tk ":" *> texpr)) : tactic unit := do
  let h' := h.get_or_else `this,
  t ← to_expr ``(%%t : Prop),
  ppt ← pp t,
  assert h' t,
  s ← focus1 (tactic.library_search { try_this := ff }) <|> fail "observe failed",
  s ← s.get_rest "Try this: exact ",
  let pph : string := (h.map (λ n : name, n.to_string ++ " ")).get_or_else "",
  when trc.is_some $ trace! "Try this: have {pph}: {ppt.to_string} := {s}"

end interactive
end tactic
