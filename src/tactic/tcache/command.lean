import tactic.tcache.executor
import tactic.tcache.store

open tcache
open lean.parser interactive interaction_monad

@[user_command]
meta def cache_file_cmd (_ : parse $ tk "cache_file") : lean.parser unit :=
emit_code_here $ "local attribute [instance, priority 2000] tcache.executor"

@[user_command]
meta def cache_file_verbose_cmd (_ : parse $ tk "cache_file?") : lean.parser unit :=
emit_code_here $ "local attribute [instance, priority 2000] tcache.executor\n"
  ++ "set_option trace.tcache true"

@[user_command]
meta def cache_section_cmd (_ : parse $ tk "cache_section") : lean.parser unit :=
emit_code_here "local attribute [instance, priority 2000] tcache.executor"

@[user_command]
meta def cache_clear_cmd (_ : parse $ tk "cache_clear") : lean.parser unit := do
  n ← ident,
  match n with
  | `tcache := clear_tcache >> tactic.trace "cache cleared"
  | _ := fail "unknown item to clear"
  end
