import tactic.localized
import system.io  -- these are required
import all

open lean.parser
-- open_locale lex
-- @[user_command] meta def open_locale_cmd (_ : parse $ tk "open_locale") : parser unit :=
-- open_locale topological_space
meta def open_all_locales : tactic unit :=
do m ← localized_attr.get_cache,
  let m := m.erase `witt,
  let m := m.erase `list.func,
  let m := m.erase `parser,
  let m := m.erase `lex,
  run $ m.mfold () (λ n cmds _, (trace n.to_string $ trace (",".intercalate cmds) $ cmds.mmap' $ λ t , trace t emit_code_here t)),
  -- run $ (native.mk_rb_map.insert `kronecker $ m.find `kronecker).mfold () (λ n cmds _, (trace n.to_string $ trace (",".intercalate cmds) $ cmds.mmap' emit_code_here)),
  return ()
/-- ok -/
@[user_command] meta def open_all_locales_cmd (_ : interactive.parse (tk "#open_all_locales")): lean.parser unit :=
open_all_locales
.
#open_all_locales
