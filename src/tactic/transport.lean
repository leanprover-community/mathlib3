import data.equiv.basic

namespace tactic

meta def transport (x : name) (e : expr) : tactic unit :=
do x' ← get_local x,
   eq ← to_expr ``(%%x' = equiv.symm %%e (%%e %%x')),
   prf ← to_expr ``((equiv.symm_apply_apply %%e %%x').symm),
   h ← assertv_fresh eq prf,
   revert h,
   ex ← to_expr ``(%%e %%x'),
   generalize ex,
   j ← mk_fresh_name,
   k ← mk_fresh_name,
   intro j,
   intro k,
   get_local k >>= subst,
   rename j x,
   skip

end tactic


namespace tactic.interactive
open lean
open lean.parser
open interactive interactive.types expr
open tactic

meta def transport (x : parse ident) (e : parse texpr) : itactic :=
do e ← to_expr e,
   tactic.transport x e

end tactic.interactive

example {α β : Type} (e : α ≃ β) (f : α → ℕ) (i : α) : f i = 0 :=
begin
  transport i e,
end

--TODO how do we not already have this tactic?! `transport i e`
example {α β : Type} (e : α ≃ β) (f : α → ℕ) (i : α) : f i = 0 :=
begin
  have h : i = e.symm (e i) := by simp,
  revert h,
  generalize : e i = j,
  intro h,
  subst h,
  rename j i,
end
