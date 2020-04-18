/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.core

/-!
## #simp
A user command to run the simplifier.
-/

setup_tactic_parser

namespace tactic

/--
The basic usage is `#simp e`, where `e` is an expression,
which will print the simplified form of `e`.

You can specify additional simp lemmas as usual for example using
`#simp [f, g] : e`, or `#simp with attr : e`.
(The colon is optional, but helpful for the parser.)

`#simp` does not understand local variables,
so you will need to use lambda-expressions
to introduce parameters.
-/
@[user_command] meta def simp_cmd (meta_info : decl_meta_info)
  (_ : parse $ tk "#simp") : lean.parser unit :=
do
  no_dflt ← only_flag,
  hs ← simp_arg_list,
  attr_names ← with_ident_list,
  o ← optional (tk ":"),
  e ← types.texpr,
  parser.of_tactic $ do
    e ← to_expr e,
    prod.fst <$> e.simp {} failed no_dflt attr_names hs >>= trace.

add_tactic_doc
{ name                     := "#simp",
  category                 := doc_category.cmd,
  decl_names               := [`tactic.simp_cmd],
  tags                     := ["simplification"] }

end tactic
