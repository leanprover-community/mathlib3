import tactic.doc_commands

open tactic

/-- ok -/
add_decl_doc division_ring

#eval do
ds ← doc_string ``division_ring,
guard $ ds = "ok"

namespace bar

def foo := 5

/-- ok -/
add_decl_doc foo

#eval do
ds ← doc_string ``foo,
guard $ ds = "ok"

end bar
