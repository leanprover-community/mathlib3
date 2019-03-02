/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison

Case bashing:
* on `x ∈ A`, for `A : finset α` or `A : list α`, or
* on `x : A`, with `[fintype A]`.
-/
import data.fintype
import tactic.norm_num

namespace tactic
open lean.parser
open interactive interactive.types expr
open conv.interactive

/-- Checks that the expression looks like `x ∈ A` for `A : finset α`, `multiset α` or `A : list α`,
    and returns the type α. -/
meta def guard_mem_fin (e : expr) : tactic expr :=
do t ← infer_type e,
   match t with
   | `(%%x ∈ %%A) :=
      do t ← infer_type A,
        match t with
        | `(finset %%α)   := return α
        | `(multiset %%α) := return α
        | `(list %%α)     := return α
        | _ := failed
        end
   | `(@list.mem %%α %%x %%A) := return α
   | _ := failed
   end

meta def fin_cases_at : list expr → expr → tactic unit
| with_list e :=
(do ty ← try_core $ guard_mem_fin e,
    match ty with
    | none :=
      -- Deal with `x : A`, where `[fintype A]` is available:
      (do
        ty ← infer_type e,
        i ← to_expr ``(fintype %%ty) >>= mk_instance <|> fail "Failed to find `fintype` instance.",
        t ← to_expr ``(%%e ∈ @fintype.elems %%ty %%i),
        v ← to_expr ``(@fintype.complete %%ty %%i %%e),
        h ← assertv `h t v,
        fin_cases_at with_list h)
    | (some ty) :=
      -- Deal with `x ∈ A` hypotheses:
      (do
        numeric ← option.is_some <$> try_core (unify ty `(ℕ) <|> unify ty `(ℤ) <|> unify ty `(ℚ)),
        result ← cases_core e,
        match result with
        -- We have a goal with an equation `s`, and a second goal with a smaller `e : x ∈ _`.
        | [(_, [s], _), (_, [e], _)] :=
          do let sn := local_pp_name s,
              ng ← num_goals,
              -- tidy up the new value
              tactic.interactive.conv (some sn) none
                (to_rhs >> match with_list.nth 0 with
                | (some h) := conv.interactive.change (to_pexpr h)
                | _ := `[try { conv.interactive.simp ff [] [] }] >> when numeric `[try { conv.interactive.norm_num [] }]
                end),
              s ← get_local sn,
              try `[subst %%s],
              ng' ← num_goals,
              when (ng = ng') (rotate_left 1),
              fin_cases_at with_list.tail e
        -- No cases; we're done.
        | [] := skip
        | _ := failed
        end)-- <|> fail "Something went wrong while performing `cases`."
    end)

meta def fin_cases_at' (with_list : list expr) (e : expr) : tactic unit :=
focus1 $ fin_cases_at with_list e

meta def expr_list_to_list_expr : expr → tactic (list expr)
| `(list.cons %%h %%t) := do t ← expr_list_to_list_expr t, return (h :: t)
| `([]) := return []
| _ := failed

namespace interactive
private meta def hyp := tk "*" *> return none <|> some <$> ident
local postfix `?`:9001 := optional

/--
`fin_cases h` performs case analysis on a hypothesis of the form
`h : A`, where `[fintype A]` is available, or
`h ∈ A`, where `A : finset X`, `A : multiset X` or `A : list X`.

`fin_cases *` performs case analysis on all suitable hypotheses.

As an example, in
```
example (f : ℕ → Prop) (p : fin 3) (h0 : f 0) (h1 : f 1) (h2 : f 2) : f p.val :=
begin
  fin_cases *; simp,
  all_goals { assumption }
end
```
after `fin_cases p; simp`, there are three goals, `f 0`, `f 1`, and `f 2`.
-/
meta def fin_cases : parse hyp → parse (tk "with" *> texpr)? → tactic unit
| none none := do ctx ← local_context,
                  ctx.mfirst (fin_cases_at' []) <|> fail "No hypothesis of the forms `x ∈ A`, where `A : finset X`, `A : list X`, or `A : multiset X`, or `x : A`, with `[fintype A]`."
| none (some _) := fail "Specify a single hypothesis when using a `with` argument."
| (some n) with_list :=
  do
    h ← get_local n,
    with_list ← match with_list with
        | (some e) := i_to_expr e >>= expr_list_to_list_expr
        | none := return []
        end,
    fin_cases_at' with_list h

end interactive

end tactic
