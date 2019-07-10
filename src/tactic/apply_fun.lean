/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/

import tactic.monotonicity
import order.basic

open tactic interactive (parse) interactive (loc.ns)
     interactive.types (texpr location) lean.parser (tk)

local postfix `?`:9001 := optional

meta def apply_fun_name (e : pexpr) (h : name) (M : option pexpr) : tactic unit :=
do {
  H ← get_local h,
  t ← infer_type H,
  match t with
  | `(%%l = %%r) := do
      ltp ← infer_type l,
      mv ← mk_mvar,
      to_expr ``(congr_arg (%%e : %%ltp → %%mv) %%H) >>= note h,
      clear H
  | `(%%l ≤ %%r) := do
       if M.is_some then do
         Hmono ← M >>= tactic.i_to_expr,
         to_expr ``(%%Hmono %%H) >>= note h >> skip
       else do {
         n ← get_unused_name `mono,
         to_expr ``(monotone %%e) >>= assert n,
         do { intro_lst [`x, `y, `h], `[dsimp, mono], skip } <|> swap,
         Hmono ← get_local n,
         to_expr ``(%%Hmono %%H) >>= note h >> skip },
       clear H
  | _ := skip
  end,
  -- let's try to force β-reduction at `h`
  try (tactic.interactive.dsimp tt [] [] (loc.ns [h])
         {eta := false, beta := true})
} <|> fail ("failed to apply " ++ to_string e ++ " at " ++ to_string h)

namespace tactic.interactive
/-- Apply a function to some local assumptions which are either equalities or
    inequalities. For instance, if the context contains `h : a = b` and
    some function `f` then `apply_fun f at h` turns `h` into `h : f a = f b`.
    When the assumption is an inequality `h : a ≤ b`, a side goal `monotone f`
    is created, unless this condition is provided using
    `apply_fun f at h using P` where `P : monotone f`, or the `mono` tactic can
    prove it. -/
meta def apply_fun (q : parse texpr) (locs : parse location)
  (lem : parse (tk "using" *> texpr)?) : tactic unit :=
--do e ← tactic.i_to_expr q,
   match locs with
   | (loc.ns l) := do
      l.mmap' (λ l, match l with
      | some h :=  apply_fun_name q h lem
      | none := skip
      end)
   | wildcard := do ctx ← local_context,
                    ctx.mmap' (λ h, apply_fun_name q h.local_pp_name lem)
   end
end tactic.interactive
