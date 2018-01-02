/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.dlist tactic.rcases tactic.generalize_proofs

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
let simp_at (lc) := simp no_dflt hs attr_names (loc.ns lc) cfg >> try (assumption <|> trivial) in
match tgt with
| none := get_local `this >> simp_at [some `this, none] <|> simp_at [none]
| some e :=
  (do e ← i_to_expr e,
    match e with
    | local_const _ lc _ _ := simp_at [some lc, none]
    | e := do
      t ← infer_type e,
      assertv `this t e >> simp_at [some `this, none]
    end) <|> (do
      simp_at [none],
      ty ← target,
      e ← i_to_expr_strict ``(%%e : %%ty), -- for positional error messages, don't care about the result
      pty ← pp ty, ptgt ← pp e,
      -- Fail deliberately, to advise regarding `simp; exact` usage
      fail ("simpa failed, 'using' expression type not directly " ++
        "inferrable. Try:\n\nsimpa ... using\nshow " ++
        to_fmt pty ++ ",\nfrom " ++ ptgt : format))
end

meta def try_for (max : parse parser.pexpr) (tac : itactic) : tactic unit :=
do max ← i_to_expr_strict max >>= tactic.eval_expr nat,
   tactic.try_for max tac <|> 
     (tactic.trace "try_for timeout, using sorry" >> admit)

meta def substs (l : parse ident*) : tactic unit :=
l.mmap' (λ h, get_local h >>= tactic.subst)

meta def unfold_coes (loc : parse location) : tactic unit :=
unfold [``coe,``lift_t,``has_lift_t.lift,``coe_t,``has_coe_t.coe,``coe_b,``has_coe.coe,
        ``coe_fn, ``has_coe_to_fun.coe, ``coe_sort, ``has_coe_to_sort.coe] loc

meta def recover : tactic unit :=
do r ← tactic.result,
   tactic.set_goals $ r.fold [] $ λ e _ l,
     match e with
     | expr.mvar _ _ _ := insert e l
     | _ := l
     end

meta def continue (tac : itactic) : tactic unit :=
λ s, result.cases_on (tac s)
 (λ a, result.success ())
 (λ e ref, result.success ())

meta def swap (n := 2) : tactic unit :=
if n = 2 then tactic.swap else tactic.rotate n

meta def generalize_proofs : parse ident_* → tactic unit :=
tactic.generalize_proofs

/-- Clear all hypotheses starting with `_`, like `_match` and `_let_match`. -/
meta def clear_ : tactic unit := tactic.repeat $ do
  l ← local_context,
  l.reverse.mfirst $ λ h, do
    name.mk_string s p ← return $ local_pp_name h,
    guard (s.front = '_'),
    cl ← infer_type h >>= is_class, guard (¬ cl),
    tactic.clear h

meta def congr_n : nat → tactic unit
| 0     := failed
| (n+1) := focus1 (try assumption >> congr_core >>
  all_goals (try reflexivity >> try (congr_n n)))

end interactive
end tactic
