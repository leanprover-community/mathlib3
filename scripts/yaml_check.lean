import data.buffer.parser
import system.io
import tactic.core
import all

open native

section
variables {F : Type → Type} [alternative F]

def fails {α} (x : F α) : F bool := (x $> ff) <|> pure tt
end

open io io.fs tactic

meta instance coe_tactic_to_io {α} : has_coe (tactic α) (io α) :=
⟨run_tactic⟩


meta def list.to_key_val_pairs : list string → list (string × name)
| (key::val::nl::l) := if nl = "" then (key, name.from_string val)::list.to_key_val_pairs l else []
| _ := []

/--
Reads the `nolints.txt`, and returns it as an `rb_lmap` from linters to declarations.
-/
meta def read_nolints_file (fn : string) : io (list (string × name)) := do
cont ← io.fs.read_file fn,
let lines := cont.to_string.split (= '\n'),
return lines.to_key_val_pairs

meta def find_failures (l : list (string × name)) : tactic (list (string × name)) :=
l.mfilter $ λ ⟨key, decl⟩, fails $ get_decl decl

def databases : list (string × string) := [
  ("undergrad.txt", "Entries in `docs/undergrad.yaml` refer to declarations that don't exist. Please correct the following:"),
  ("overview.txt", "Entries in `docs/overview.yaml` refer to declarations that don't exist. Please correct the following:"),
  ("100.txt", "Entries in `docs/100.yaml` refer to declarations that don't exist. Please correct the following:")
]

meta def process_db : string × string → io bool | (file, msg) := do
entries ← read_nolints_file file,
failures ← find_failures entries,
when (failures.length > 0) (do
  trace msg,
  failures.mmap' $ λ p, trace format!"{p.1} : {p.2}"),
return $ failures.length = 0

-- we don't use `list.mall` because we don't want to short circuit on the first failure
meta def main : io unit := do
databases.mfoldl (λ b p, do r ← process_db p, return $ b && r) tt >>= guardb
