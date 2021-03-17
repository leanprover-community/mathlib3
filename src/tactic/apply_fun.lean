/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Patrick Massot
-/
import tactic.monotonicity

namespace tactic

/-- Apply the function `f` given by `e : pexpr` to the local hypothesis `hyp`, which must either be
of the form `a = b` or `a ≤ b`, replacing the type of `hyp` with `f a = f b` or `f a ≤ f b`. If
`hyp` names an inequality then a new goal `monotone f` is created, unless the name of a proof of
this fact is passed as the optional argument `mono_lem`, or the `mono` tactic can prove it.
-/
meta def apply_fun_to_hyp (e : pexpr) (mono_lem : option pexpr) (hyp : expr) : tactic unit :=
do {
  t ← infer_type hyp,
  prf ← match t with
  | `(%%l = %%r) := do
      ltp ← infer_type l,
      mv ← mk_mvar,
      to_expr ``(congr_arg (%%e : %%ltp → %%mv) %%hyp)
  | `(%%l ≤ %%r) := do
       Hmono ← match mono_lem with
        | some mono_lem :=
          tactic.i_to_expr mono_lem
        | none := do
          n ← get_unused_name `mono,
          to_expr ``(monotone %%e) >>= assert n,
          -- In order to resolve implicit arguments in `%%e`,
          -- we build (and discard) the expression `%%n %%hyp` before calling the `mono` tactic.
          swap,
          n ← get_local n,
          to_expr ``(%%n %%hyp),
          swap,
          do { intro_lst [`x, `y, `h], `[try { dsimp }, mono] } <|> swap,
          return n
        end,
       to_expr ``(%%Hmono %%hyp)
  | _ := fail!"failed to apply {e} at {hyp}"
  end,
  clear hyp,
  hyp ← note hyp.local_pp_name none prf,
  -- let's try to force β-reduction at `h`
  try $ tactic.dsimp_hyp hyp simp_lemmas.mk [] { eta := false, beta := true }
}

/--
Attempt to "apply" a function `f` represented by the argument `e : pexpr` to the goal.

If the goal is of the form `a ≠ b`, we obtain the new goal `f a ≠ f b`.
If the goal is of the form `a = b`, we obtain a new goal `f a = f b`, and a subsidiary goal
`injective f`.
(We attempt to discharge this subsidiary goal automatically, or using the optional argument.)
If the goal is of the form `a ≤ b` (or similarly for `a < b`), and `f` is an `order_iso`,
we obtain a new goal `f a ≤ f b`.
-/
meta def apply_fun_to_goal (e : pexpr) (lem : option pexpr) : tactic unit :=
do t ← target,
  match t with
  | `(%%l ≠ %%r) := to_expr ``(ne_of_apply_ne %%e) >>= apply >> skip
  | `(¬%%l = %%r) := to_expr ``(ne_of_apply_ne %%e) >>= apply >> skip
  | `(%%l ≤ %%r) := to_expr ``((order_iso.le_iff_le %%e).mp) >>= apply >> skip
  | `(%%l < %%r) := to_expr ``((order_iso.lt_iff_lt %%e).mp) >>= apply >> skip
  | `(%%l = %%r) := focus1 (do
      to_expr ``(%%e %%l), -- build and discard an application, to fill in implicit arguments
      n ← get_unused_name `inj,
      to_expr ``(function.injective %%e) >>= assert n,
      -- Attempt to discharge the `injective f` goal
      (focus1 $
      assumption <|>
        (to_expr ``(equiv.injective) >>= apply >> done) <|>
        -- We require that applying the lemma closes the goal, not just makes progress:
        (lem.mmap (λ l, to_expr l >>= apply) >> done))
        <|> swap, -- return to the main goal if we couldn't discharge `injective f`.
      n ← get_local n,
      apply n,
      clear n)
  | _ := fail!"failed to apply {e} to the goal"
  end

namespace interactive

setup_tactic_parser


/--
Apply a function to an equality or inequality in either a local hypothesis or the goal.

* If we have `h : a = b`, then `apply_fun f at h` will replace this with `h : f a = f b`.
* If we have `h : a ≤ b`, then `apply_fun f at h` will replace this with `h : f a ≤ f b`,
  and create a subsidiary goal `monotone f`.
  `apply_fun` will automatically attempt to discharge this subsidiary goal using `mono`,
  or an explicit solution can be provided with `apply_fun f at h using P`, where `P : monotone f`.
* If the goal is `a ≠ b`, `apply_fun f` will replace this with `f a ≠ f b`.
* If the goal is `a = b`, `apply_fun f` will replace this with `f a = f b`,
  and create a subsidiary goal `injective f`.
  `apply_fun` will automatically attempt to discharge this subsidiary goal using local hypotheses,
  or if `f` is actually an `equiv`,
  or an explicit solution can be provided with `apply_fun f using P`, where `P : injective f`.
* If the goal is `a ≤ b` (or similarly for `a < b`), and `f` is actually an `order_iso`,
  `apply_fun f` will replace the goal with `f a ≤ f b`.
  If `f` is anything else (e.g. just a function, or an `equiv`), `apply_fun` will fail.


Typical usage is:
```lean
open function

example (X Y Z : Type) (f : X → Y) (g : Y → Z) (H : injective $ g ∘ f) :
  injective f :=
begin
  intros x x' h,
  apply_fun g at h,
  exact H h
end
```
 -/
meta def apply_fun (q : parse texpr) (locs : parse location) (lem : parse (tk "using" *> texpr)?)
  : tactic unit :=
locs.apply (apply_fun_to_hyp q lem) (apply_fun_to_goal q lem)

add_tactic_doc
{ name       := "apply_fun",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.apply_fun],
  tags       := ["context management"] }

end interactive

end tactic
