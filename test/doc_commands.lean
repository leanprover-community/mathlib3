import tactic.doc_commands

open tactic

namespace bar

def foo := 5

/-- ok -/
add_decl_doc foo

run_cmd do
ds ← doc_string ``foo,
guard $ ds = "ok"

end bar
