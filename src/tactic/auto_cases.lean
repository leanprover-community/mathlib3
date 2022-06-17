/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Scott Morrison
-/
import tactic.hint

namespace tactic

namespace auto_cases

/-- Structure representing a tactic which can be used by `tactic.auto_cases`. -/
meta structure auto_cases_tac :=
(name : string)
{α : Type}
(tac : expr → tactic α)

/-- The `auto_cases_tac` for `tactic.cases`. -/
meta def tac_cases : auto_cases_tac := ⟨"cases", cases⟩

/-- The `auto_cases_tac` for `tactic.induction`. -/
meta def tac_induction : auto_cases_tac := ⟨"induction", induction⟩

/-- Find an `auto_cases_tac` which matches the given `type : expr`. -/
meta def find_tac : expr → option auto_cases_tac
| `(empty)     := tac_cases
| `(pempty)    := tac_cases
| `(false)     := tac_cases
| `(unit)      := tac_cases
| `(punit)     := tac_cases
| `(ulift _)   := tac_cases
| `(plift _)   := tac_cases
| `(prod _ _)  := tac_cases
| `(and _ _)   := tac_cases
| `(sigma _)   := tac_cases
| `(psigma _)  := tac_cases
| `(subtype _) := tac_cases
| `(Exists _)  := tac_cases
| `(fin 0)     := tac_cases
| `(sum _ _)   := tac_cases -- This is perhaps dangerous!
| `(or _ _)    := tac_cases -- This is perhaps dangerous!
| `(iff _ _)   := tac_cases -- This is perhaps dangerous!
/- `cases` can be dangerous on `eq` and `quot`, producing mysterious errors during type checking.
   instead we attempt `induction`. -/
| `(eq _ _)    := tac_induction
| `(quot _)    := tac_induction
| _            := none

end auto_cases

/-- Applies `cases` or `induction` on the local_hypothesis `hyp : expr`. -/
meta def auto_cases_at (hyp : expr) : tactic string :=
do t ← infer_type hyp >>= whnf,
   match auto_cases.find_tac t with
   | some atac := do
     atac.tac hyp,
     pp ← pp hyp,
     return sformat!"{atac.name} {pp}"
   | none := fail "hypothesis type unsupported"
   end

/-- Applies `cases` or `induction` on certain hypotheses. -/
@[hint_tactic]
meta def auto_cases : tactic string :=
do l ← local_context,
   results ← successes $ l.reverse.map auto_cases_at,
   when (results.empty) $
     fail "`auto_cases` did not find any hypotheses to apply `cases` or `induction` to",
   return (string.intercalate ", " results)

end tactic
