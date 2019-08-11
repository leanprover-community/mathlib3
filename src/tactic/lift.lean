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
  Used by the tactic `lift`. -/
class can_lift (α : Type u) (β : Type v) : Type (max u v) :=
(coe : β → α)
(cond : α → Prop)
(prf : ∀(x : α), cond x → ∃(y : β), coe y = x)

@[can_lift] instance : can_lift ℤ ℕ :=
⟨coe, λ n, 0 ≤ n, λ n hn, ⟨n.nat_abs, int.nat_abs_of_nonneg hn⟩⟩

namespace tactic

meta def lift (p : pexpr) (t : pexpr) (h : option pexpr) (n : list name) : tactic unit :=
do
  let dsimp := interactive.dsimp tt [] [`can_lift],
  e ← i_to_expr p,
  old_tp ← infer_type e,
  new_tp ← i_to_expr t,
  inst_type ← mk_app ``can_lift [old_tp, new_tp],
  inst ← mk_instance inst_type <|>
    pformat!"Failed to find a lift from {old_tp} to {new_tp}. Provide an instance of\n  {inst_type}"
    >>= fail,
  prf ← if h_some : h.is_some then
    (do prf ← i_to_expr (option.get h_some), prf_ty ← infer_type prf,
    expected_prf_ty ← mk_app `can_lift.cond [old_tp, new_tp, inst, e],
    unify prf_ty expected_prf_ty <|>
      (do expected_prf_ty2 ← expected_prf_ty.dsimp {} tt [`can_lift],
        pformat!"lift tactic failed. The type of\n  {prf}\nis\n  {prf_ty}\nbut it is expected to be\n  {expected_prf_ty2}" >>= fail),
    return prf)
    else (do prf_nm ← get_unused_name,
      prf ← mk_app `can_lift.cond [old_tp, new_tp, inst, e] >>= assert prf_nm,
      focus1 (dsimp $ interactive.loc.ns [none]), swap, return prf),
  let prf_nm := if prf.is_local_constant then some prf.local_pp_name else none,
  /- We use mk_mapp to apply `can_lift.prf` to all but one argument, and then just use expr.app
  for the last argument. For some reason we get an error when applying mk_mapp it to all
  arguments. -/
  prf_ex_partial ← mk_mapp `can_lift.prf [old_tp, new_tp, inst, e],
  let prf_ex := prf_ex_partial prf,
  new_nm ← if n ≠ [] then return n.head
    else if e.is_local_constant then return e.local_pp_name
    else get_unused_name,
  eq_nm ← if hn : 1 < n.length then return (n.nth_le 1 hn)
    else if e.is_local_constant then return `rfl
    else get_unused_name `h,
  temp_nm ← get_unused_name,
  temp_e ← note temp_nm none prf_ex,
  dsimp (interactive.loc.ns [temp_nm]),
  rcases (pexpr.of_expr temp_e) [[rcases_patt.one new_nm, rcases_patt.one eq_nm]],
  when (¬ e.is_local_constant) (get_local eq_nm >>=
    λ e, interactive.rw ⟨[⟨⟨0, 0⟩, tt, (pexpr.of_expr e)⟩], none⟩ interactive.loc.wildcard),
  if h_prf_nm : prf_nm.is_some ∧ n.nth 2 ≠ prf_nm then
    get_local (option.get h_prf_nm.1) >>= clear else skip

open lean.parser interactive interactive.types

local postfix `?`:9001 := optional
meta def using_texpr := (tk "using" *> texpr)?
reserve notation `to`
meta def to_texpr := (tk "to" *> texpr)

namespace interactive

/-- The tactic `lift p to t using h` lifts expression `p` to type `t` using proof obligation `h`.
  * Example usage: if `n : ℤ` and `hn : n ≥ 0` then the following tactic lifts `n` to `ℕ`.
    ```
      lift n to ℕ using hn
    ```
  * This tactic will create a new variable `k` of type `t` and a proof `hk` stating that
    `k` mapped to `type_p` is equal to `p` (where `type_p` is the type of `p`).
  * This tactic requires an instance of `can_lift type_p t`.
  * If `h` is not provided, this tactic creates a new goal for `h`.
  * Use `lift p to t using h with k hk` to specify the names of `k` and `hk`.
  * If the name for `hk` is not provided and `p` is a local constant, then the proof `hk` will be
    used to substitute `p` everywhere (removing `p` and `hk` from the context).
  * If `p` is not a local constant, the equation `hk` will be used to rewrite the expression `p`
    wherever possible (keeping `hk` in the context).
  * If the name for `k` is not provided and `p` is a local constant,
    then the name of `p` will be used for `k`.
  * If `h` is a local constant then `h` is cleared from local context, unless you write `h` as the
    third entry after `with`.
  * If you want to keep `h` in the local context, but still do the substitution on `p`, you can use
    `rfl` for the second element of `n`, like the following example.
    ```
      lift p to t using h with p rfl h
    ```
-/
meta def lift (p : parse texpr) (t : parse to_texpr) (h : parse using_texpr)
  (n : parse with_ident_list) : tactic unit :=
tactic.lift p t h n

end interactive
end tactic
