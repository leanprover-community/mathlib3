/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.equiv.basic

namespace tactic

meta def equiv_rw_hyp (x : name) (e : expr) : tactic unit :=
do x' ← get_local x,
   ty ← infer_type x',
   eq ← to_expr ``(%%x' = equiv.symm %%e (%%e %%x')),
   prf ← to_expr ``((equiv.symm_apply_apply %%e %%x').symm),
   h ← assertv_fresh eq prf,
   revert h,
   ex ← to_expr ``(%%e %%x'),
   generalize ex (by apply_opt_param) transparency.none,
   j ← mk_fresh_name,
   intro j,
   k ← mk_fresh_name,
   intro k >>= subst,
   rename j x,
   skip

end tactic


namespace tactic.interactive
open lean.parser
open interactive interactive.types
open tactic

local postfix `?`:9001 := optional

meta def equiv_rw (e : parse texpr) (loc : parse $ (tk "at" *> ident)?) : itactic :=
do e ← to_expr e,
   match loc with
   | (some hyp) := tactic.equiv_rw_hyp hyp e
   | none := do s ← to_expr ``(equiv.inv_fun %%e),
                tactic.apply s,
                skip
   end

end tactic.interactive


example {α β : Type} (e : α ≃ β) (f : α → ℕ) (h : ∀ j : β, f (e.symm j) = 0) (i : α) : f i = 0 :=
begin
  equiv_rw e at i,
  apply h,
end

example {α β : Type} (e : α ≃ β) (b : β) : α :=
begin
  equiv_rw e,
  exact b,
end
