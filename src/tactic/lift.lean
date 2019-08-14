/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import tactic.rcases

/-!
# lift tactic

This file defines the lift tactic, allowing the user to lift elements from one type to another
under a specified condition.

## Tags

lift, tactic
-/

universe variables u v

run_cmd mk_simp_attr `can_lift

/-- A class specifying that you can lift elements from `α` to `β` assuming `cond` is true.
  Used by the tactic `lift`. For the proper functioning of the lift tactic, make sure that all
  instances of this class have attribute `[can_lift]`. -/
class can_lift (α : Type u) (β : Type v) : Type (max u v) :=
(coe : β → α)
(cond : α → Prop)
(prf : ∀(x : α), cond x → ∃(y : β), coe y = x)

@[can_lift] instance : can_lift ℤ ℕ :=
⟨coe, λ n, 0 ≤ n, λ n hn, ⟨n.nat_abs, int.nat_abs_of_nonneg hn⟩⟩

namespace tactic

/- Construct the proof of `cond x` in the lift tactic.
  If the proof was specified, we check whether it has the correct type.
    If it doesn't have the correct type, we display an error message
    (but first call dsimp on the expression in the message).
  If the proof was not specified, we create assert it as a local constant.
  (The name of this local constant doesn't matter, since `lift` will remove it from the context) -/
meta def get_lift_prf (h : option pexpr) (old_tp new_tp inst e : expr) : tactic expr :=
if h_some : h.is_some then
  (do prf ← i_to_expr (option.get h_some), prf_ty ← infer_type prf,
  expected_prf_ty ← mk_app `can_lift.cond [old_tp, new_tp, inst, e],
  unify prf_ty expected_prf_ty <|>
    (do expected_prf_ty2 ← expected_prf_ty.dsimp {} tt [`can_lift],
      pformat!"lift tactic failed. The type of\n  {prf}\nis\n  {prf_ty}\nbut it is expected to be\n  {expected_prf_ty2}" >>= fail),
  return prf)
  else (do prf_nm ← get_unused_name,
    prf ← mk_app `can_lift.cond [old_tp, new_tp, inst, e] >>= assert prf_nm,
    focus1 (interactive.dsimp tt [] [`can_lift] $ interactive.loc.ns [none]), swap, return prf)

meta def lift (p : pexpr) (t : pexpr) (h : option pexpr) (n : list name) : tactic unit :=
do
  e ← i_to_expr p,
  old_tp ← infer_type e,
  new_tp ← i_to_expr t,
  inst_type ← mk_app ``can_lift [old_tp, new_tp],
  inst ← mk_instance inst_type <|>
    pformat!"Failed to find a lift from {old_tp} to {new_tp}. Provide an instance of\n  {inst_type}"
    >>= fail,
  prf_cond ← get_lift_prf h old_tp new_tp inst e,
  let prf_nm := if prf_cond.is_local_constant then some prf_cond.local_pp_name else none,
  /- We use mk_mapp to apply `can_lift.prf` to all but one argument, and then just use expr.app
  for the last argument. For some reason we get an error when applying mk_mapp it to all
  arguments. -/
  prf_ex0 ← mk_mapp `can_lift.prf [old_tp, new_tp, inst, e],
  let prf_ex := prf_ex0 prf_cond,
  /- Find the name of the new variable -/
  new_nm ← if n ≠ [] then return n.head
    else if e.is_local_constant then return e.local_pp_name
    else get_unused_name,
  /- Find the name of the proof of the equation -/
  eq_nm ← if hn : 1 < n.length then return (n.nth_le 1 hn)
    else if e.is_local_constant then return `rfl
    else get_unused_name `h,
  /- We add the proof of the existential statement to the context and then apply
  `dsimp only with can_lift` to it. -/
  temp_nm ← get_unused_name,
  temp_e ← note temp_nm none prf_ex,
  interactive.dsimp tt [] [`can_lift] (interactive.loc.ns [temp_nm]),
  /- We case on the existential. We use `rcases` because `eq_nm` could be `rfl`. -/
  rcases (pexpr.of_expr temp_e) [[rcases_patt.one new_nm, rcases_patt.one eq_nm]],
  /- If the lifted variable is not a local constant, try to rewrite it away using the new equality-/
  when (¬ e.is_local_constant) (get_local eq_nm >>=
    λ e, interactive.rw ⟨[⟨⟨0, 0⟩, tt, (pexpr.of_expr e)⟩], none⟩ interactive.loc.wildcard),
  /- If the proof `prf_cond` is a local constant, remove it from the context,
    unless `n` specifies to keep it. -/
  if h_prf_nm : prf_nm.is_some ∧ n.nth 2 ≠ prf_nm then
    get_local (option.get h_prf_nm.1) >>= clear else skip

open lean.parser interactive interactive.types

local postfix `?`:9001 := optional
meta def using_texpr := (tk "using" *> texpr)?
reserve notation `to`
meta def to_texpr := (tk "to" *> texpr)

namespace interactive

/-- Lift an expression to another type.
  * Usage: `'lift' expr 'to' expr ('using' expr)? ('with' id (id id?)?)?.`
  * If `n : ℤ` and `hn : n ≥ 0` then the tactic `lift n to ℕ using hn` creates a new
    constant of type ℕ, also named `n` and replaces all occurrences of the old variable `(n : ℤ)`
    with `↑n` (where `n` in the new variable). It will remove `n` and `hn` from the context.
  * The argument `using hn` is optional, the tactic `lift n to ℕ` does the same, but also creates a
    new subgoal that `n ≥ 0` (where `n` is the old variable).
  * You can also use `lift n to ℕ using e` where `e` is any expression of type `n ≥ 0`.
  * Use `lift n to ℕ with k` to specify the name of the new variable.
  * Use `lift n to ℕ with k hk` to also specify the name of the equality `↑k = n`. In this case, `n`
    will remain in the context. You can use `rfl` for the name of `hk` to substitute it away.
  * You can also use `lift e to ℕ with k hk` where `e` is any expression of type `ℤ`.
    In this case, the `hk` will always stay in the context, but it will be used to rewrite `e` in
    all hypotheses and the target.
  * The tactic `lift n to ℕ using h` will remove `h` from the context. If you want to keep it,
    specify it again as the third argument to `with`, like this: `lift n to ℕ using h with n rfl h`.
  * More generally, this can lift an expression from `α` to `β` assuming that there is an instance
    of `can_lift α β`. In this case the proof obligation is specified by `can_lift.cond`.
  * If you declare a new instance of the `can_lift` class, give it the `[can_lift]` attribute,
    like so: `@[can_lift] instance : can_lift ℤ ℕ := ⟨_, _, _⟩`.
-/
meta def lift (p : parse texpr) (t : parse to_texpr) (h : parse using_texpr)
  (n : parse with_ident_list) : tactic unit :=
tactic.lift p t h n

end interactive
end tactic
