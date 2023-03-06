
import .find_unused_decl2

def this_is_unused := ()

@[main_declaration]
def main_thing := used_somewhere_else

run_cmd do
  ds ← tactic.all_unused [none],
  let es := [`this_is_unused],
  guard (ds.keys = es) <|>
    fail!"wrong declarations: {ds.keys},\nexpected: {es}"

run_cmd do
  ds ← tactic.all_unused ["test/find_unused_decl2.lean"],
  let es := [`used_somewhere_else,`unused_type,`unused1],
  guard (ds.keys = [`used_somewhere_else,`unused_type,`unused1]) <|>
    fail!"wrong declarations: {ds.keys},\nexpected: {es}"

run_cmd do
  ds ← tactic.all_unused [none, "test/find_unused_decl2.lean"],
  let es := [`this_is_unused,`unused_type,`unused1],
  guard (ds.keys = [`this_is_unused,`unused_type,`unused1]) <|>
    fail!"wrong declarations: {ds.keys},\nexpected: {es}"
