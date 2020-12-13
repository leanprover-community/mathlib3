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
                 do { intro_lst [`x, `y, `h], `[dsimp, mono], skip } <|> swap,
                 get_local n
               end,
       to_expr ``(%%Hmono %%hyp)
  | _ := fail ("failed to apply " ++ to_string e ++ " at " ++ to_string hyp.local_pp_name)
  end,
  clear hyp,
  hyp ← note hyp.local_pp_name none prf,
  -- let's try to force β-reduction at `h`
  try $ tactic.dsimp_hyp hyp simp_lemmas.mk [] { eta := false, beta := true }
}

namespace interactive

setup_tactic_parser


/--
Apply a function to some local assumptions which are either equalities
or inequalities. For instance, if the context contains `h : a = b` and
some function `f` then `apply_fun f at h` turns `h` into
`h : f a = f b`. When the assumption is an inequality `h : a ≤ b`, a side
goal `monotone f` is created, unless this condition is provided using
`apply_fun f at h using P` where `P : monotone f`, or the `mono` tactic
can prove it.

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
match locs with
| (loc.ns l) := l.mmap' $ option.mmap $ λ h, get_local h >>= apply_fun_to_hyp q lem
| wildcard   := local_context >>= list.mmap' (apply_fun_to_hyp q lem)
end

add_tactic_doc
{ name       := "apply_fun",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.apply_fun],
  tags       := ["context management"] }

end interactive

end tactic
