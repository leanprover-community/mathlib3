/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.dlist tactic.rcases

open lean
open lean.parser

local postfix `?`:9001 := optional
local postfix *:9001 := many

namespace tactic
namespace interactive
open interactive interactive.types expr

meta def rcases_parse : parser (list rcases_patt) :=
let p :=
  (rcases_patt.one <$> ident_) <|>
  (rcases_patt.many <$> brackets "⟨" "⟩" (sep_by (tk ",") rcases_parse)) in
list.cons <$> p <*> (tk "|" *> p)*

meta def rcases_parse.invert : list rcases_patt → list (list rcases_patt) :=
let invert' (l : list rcases_patt) : rcases_patt := match l with
| [k] := k
| _ := rcases_patt.many (rcases_parse.invert l)
end in
list.map $ λ p, match p with
| rcases_patt.one n := [rcases_patt.one n]
| rcases_patt.many l := invert' <$> l
end

meta def rcases (p : parse texpr) (ids : parse (tk "with" *> rcases_parse)?) : tactic unit :=
tactic.rcases p $ rcases_parse.invert $ ids.get_or_else [default _]

end interactive
end tactic
