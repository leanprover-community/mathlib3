import .store

open tcache
open lean.parser interactive interaction_monad

@[user_command]
meta def clear_cmd (_ : parse $ tk "#clear") : lean.parser unit := do
  n ← ident,
  match n with
  | `tcache := clear_tcache >> tactic.trace "cache cleared"
  | _ := fail "unknown item to clear"
  end