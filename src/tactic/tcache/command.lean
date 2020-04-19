import tactic.core
import tactic.tcache.executor
import tactic.tcache.store

open tcache
open lean.parser interactive interaction_monad

@[user_command]
meta def cache_enable_cmd (_ : parse $ tk "cache_enable") : lean.parser unit :=
emit_code_here "local attribute [instance, priority 2000] tcache.executor"

@[user_command]
meta def clear_cmd (_ : parse $ tk "#clear") : lean.parser unit := do
  n ← ident,
  match n with
  | `tcache := clear_tcache >> tactic.trace "cache cleared"
  | _ := fail "unknown item to clear"
  end
