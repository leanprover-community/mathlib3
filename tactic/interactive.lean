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
with_desc "patt" $ let p :=
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

/--
The `rcases` tactic is the same as `cases`, but with more flexibility in the
`with` pattern syntax to allow for recursive case splitting. The pattern syntax
uses the following recursive grammar:

```
patt ::= (patt_list "|")* patt_list
patt_list ::= id | "_" | "⟨" (patt ",")* patt "⟩"
```

A pattern like `⟨a, b, c⟩ | ⟨d, e⟩` will do a split over the inductive datatype,
naming the first three parameters of the first constructor as `a,b,c` and the
first two of the second constructor `d,e`. If the list is not as long as the
number of arguments to the constructor or the number of constructors, the
remaining variables will be automatically named. If there are nested brackets
such as `⟨⟨a⟩, b | c⟩ | d` then these will cause more case splits as necessary.
If there are too many arguments, such as `⟨a, b, c⟩` for splitting on
`∃ x, ∃ y, p x`, then it will be treated as `⟨a, ⟨b, c⟩⟩`, splitting the last
parameter as necessary.
-/
meta def rcases (p : parse texpr) (ids : parse (tk "with" *> rcases_parse)?) : tactic unit :=
tactic.rcases p $ rcases_parse.invert $ ids.get_or_else [default _]

/--
This is a "finishing" tactic modification of `simp`. The tactic `simpa [rules, ...] using e`
will simplify the hypothesis `e` using `rules`, then simplify the goal using `rules`, and
try to close the goal using `assumption`. If `e` is a term instead of a local constant,
it is first added to the local context using `have`.
-/
meta def simpa (no_dflt : parse only_flag) (hs : parse simp_arg_list) (attr_names : parse with_ident_list)
  (tgt : parse (tk "using" *> texpr)?) (cfg : simp_config_ext := {}) : tactic unit :=
do lc ← match tgt with
| none := get_local `this >> pure [some `this, none] <|> pure [none]
| some (local_const _ lc _ _) := pure [some lc, none]
| some e := do
    e ← i_to_expr e,
    t ← infer_type e,
    assertv `this t e >> pure [some `this, none]
end,
simp no_dflt hs attr_names (loc.ns lc) cfg >> (assumption <|> trivial)

meta def try_for (max : parse parser.pexpr) (tac : itactic) : tactic unit :=
do max ← i_to_expr_strict max >>= tactic.eval_expr nat,
   tactic.try_for max tac <|> 
     (tactic.trace "try_for timeout, using sorry" >> admit)

end interactive
end tactic
