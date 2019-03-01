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

/-- Checks that the expression looks like `x ∈ A` for `A : finset α` or `A : list α`,
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

meta def fin_cases_at : expr → tactic unit
| e :=
focus1 $
-- Deal with `x ∈ A` hypotheses first:
(do ty ← guard_mem_fin e,
   numeric ← option.is_some <$> try_core (unify ty `(ℕ) <|> unify ty `(ℤ) <|> unify ty `(ℚ)),
   result ← cases_core e,
   match result with
   -- We have a goal with an equation `s`, and a second goal with a smaller `e : x ∈ _`.
   | [(_, [s], _), (_, [e], _)] :=
     do let sn := local_pp_name s,
        when numeric
          -- tidy up with norm_num
          (tactic.interactive.conv (some sn) none (to_rhs >> `[try { norm_num }])),
        s ← get_local sn,
        try `[subst %%s],
        rotate_left 1,
        fin_cases_at e
   -- No cases; we're done.
   | [] := skip
   | _ := failed
   end) <|>
-- Otherwise deal with `x : A`, where `[fintype A]` is available:
(do
   ty ← infer_type e,
   i ← to_expr ``(fintype %%ty) >>= mk_instance,
   t ← to_expr ``(%%e ∈ @fintype.elems %%ty %%i),
   v ← to_expr ``(@fintype.complete %%ty %%i %%e),
   h ← assertv `h t v,
   fin_cases_at h)

namespace interactive
private meta def hyp := tk "*" *> return none <|> some <$> ident

/--
`fin_cases h` performs case analysis on a hypothesis of the form
1) `h : A`, where `[fintype A]` is available, or
2) `h ∈ A`, where `A : finset X` or `A : list X`.

`fin_cases *` performs case analysis on all suitable hypotheses.

As an example, in
```
example (f : ℕ → Prop) (p : fin 3) (h0 : f 0) (h1 : f 1) (h2 : f 2) : f p.val :=
begin
  fin_cases p,
  all_goals { assumption }
end
```
after `fin_cases p`, there are three goals, `f 0`, `f 1`, and `f 2`.
-/
meta def fin_cases : parse hyp → tactic unit
| none := do ctx ← local_context,
             ctx.mfirst fin_cases_at <|> fail "No hypothesis of the forms `x ∈ A`, where `A : finset ℕ`, or `x : A`, with `[fintype A]`."
| (some n) := do h ← get_local n, fin_cases_at h

end interactive

end tactic
