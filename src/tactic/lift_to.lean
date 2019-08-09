import tactic.rcases

universe variables u v

run_cmd mk_simp_attr `can_lift

class can_lift (α : Type u) (β : Type v) : Type (max u v) :=
(coe : α → β)
(cond : β → Prop)
(prf : ∀(y : β), cond y → ∃(x : α), coe x = y)

@[can_lift, reducible]
instance : can_lift ℕ ℤ :=
⟨coe, λ n, n ≥ 0, λ n hn, ⟨n.nat_abs, int.nat_abs_of_nonneg hn⟩⟩

lemma can_lift.prf2 (α : Type u) (β : Type v) (h : can_lift α β) (y : β) (hy : can_lift.cond α y) :
  ∃(x : α), can_lift.coe β x = y :=
can_lift.prf y hy




namespace tactic
#print ite

meta def foo : tactic unit :=
do e ← mk_mapp `eq [`(nat), `(0), `(1)],
trace e,
  skip

run_cmd foo

/-- Lift expression `p` to type `t` using proof obligation `h` with new name `n`.
  Clears `h` from local context, assuming that `h` is a local constant and clear_h is tt. -/
meta def lift_to (p : pexpr) (t : pexpr) (h : option pexpr) (n : list name)
  (clear_h : bool := tt) : tactic unit :=
do let dsimp := interactive.dsimp tt [] [`can_lift],
   e ← i_to_expr p,
   old_tp ← infer_type e,
   new_tp ← i_to_expr t,
  --  new_univ ← expr.level infer_type new_tp,
   inst ← mk_app ``can_lift [new_tp, old_tp] >>= mk_instance, -- todo: generalize universe levels
   prf ← if h_some : h.is_some then
    (do prf ← i_to_expr (option.get h_some), prf_ty ← infer_type prf,
      expected_prf_ty ← mk_app `can_lift.cond [new_tp, old_tp, inst, e],
      unify prf_ty expected_prf_ty,
      return prf)
     else (do prf_nm ← get_unused_name,
       prf ← mk_app `can_lift.cond [new_tp, old_tp, inst, e] >>= assert prf_nm,
       focus1 (dsimp $ interactive.loc.ns [none]), swap, return prf),
   let prf_nm := if prf.is_local_constant ∧ clear_h then some prf.local_pp_name else none,
   trace prf,
   ex1 ← mk_app ``can_lift [new_tp, old_tp],
   trace ex1,
   foo ← mk_meta_var new_tp,
   ex2 ← mk_app ``can_lift.coe [new_tp, old_tp, inst, foo],
   trace ex2,
  --  ex_lift ← mk_app `can_lift.prf [new_tp, old_tp, inst, e, prf],
   let ex_lift := `(@can_lift.prf.{0 0} %%new_tp %%old_tp %%inst %%e %%prf),
   new_nm ← if n ≠ [] then return n.head
     else if e.is_local_constant then return e.local_pp_name
     else get_unused_name,
   eq_nm ← if hn : 1 < n.length then return (n.nth_le 1 hn)
     else if e.is_local_constant then return `rfl
     else get_unused_name `h,
   temp_nm ← get_unused_name,
   temp_e ← note temp_nm none ex_lift,
   dsimp (interactive.loc.ns [temp_nm]),
   rcases (pexpr.of_expr temp_e) [[rcases_patt.one new_nm, rcases_patt.one eq_nm]],
   if h_prf_nm : prf_nm.is_some then get_local (option.get h_prf_nm) >>= clear else skip

open lean lean.parser interactive interactive.types

local postfix `?`:9001 := optional
meta def using_texpr := (tk "using" *> texpr)?

namespace interactive

reserve notation `to`

meta def lift (p : parse texpr) (t : parse (tk "to" *> texpr))
  (h : parse using_texpr) (n : parse with_ident_list) : tactic unit :=
tactic.lift_to p t h n

end interactive
end tactic

set_option trace.app_builder true
example (n m k : ℤ) (h : n ≥ 0) (hk : k + n ≥ 0) : n = m :=
begin
  lift n to ℕ using h, -- new goal: ↑n = m
  lift m to ℕ, -- new goals: ↑n = ↑m and m ≥ 0
  lift (k + n) to ℕ using hk with l hl, -- new assumptions: l : ℕ and hl : ↑l = k + ↑n
  sorry, sorry
end
