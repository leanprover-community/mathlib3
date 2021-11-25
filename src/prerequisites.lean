import data.nat.prime
import tactic
import tactic.by_contra


namespace tactic
namespace interactive
setup_tactic_parser

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
