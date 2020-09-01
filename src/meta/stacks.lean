import tactic.core

namespace stacks

@[derive has_reflect, derive inhabited]
structure stacks_tag : Type := (tag : string) (comment : option string)

open tactic

/-- the parser for the arguments to `@[stacks]` -/
meta def parser : lean.parser stacks_tag :=
do
  tag_e ← lean.parser.pexpr,
  tag ← ((to_expr tag_e >>= eval_expr string) : tactic string),
  -- FIXME this doesn't actually work: Lean says "function expected" when you provide two strings.
  doc_e ← optional interactive.types.texpr,
  doc ← match doc_e with
      | some e := some <$> ((to_expr e >>= eval_expr string) : tactic string)
      | none := pure none
      end,
  return ⟨tag, doc⟩

/-- A user attribute denoting a correspondence to the Stacks project -/
@[user_attribute]
meta def stacks_attribute : user_attribute unit stacks_tag :=
{ name := `stacks,
  descr := "A declaration corresponding to a tag from the Stacks project.",
  parser := parser }

end stacks
