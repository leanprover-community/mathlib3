/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.core

/-!
# The `generalizes` tactic

This module defines the `tactic.generalizes'` tactic and its interactive version
`tactic.interactive.generalizes`. These work like `generalize`, but they can
generalize over multiple expressions at once. This is particularly handy when
there are dependencies between the expressions, in which case `generalize` will
usually fail but `generalizes` may succeed.

## Implementation notes

To generalize the target `T` over expressions `j₁ : J₁, ..., jₙ : Jₙ`, we first
create the new target type

    T' = ∀ (k₁ : J₁) ... (kₙ : Jₙ) (k₁_eq : k₁ = j₁) ... (kₙ_eq : kₙ == jₙ), U

where `U` is `T` with any occurrences of the `jᵢ` replaced by the corresponding
`kᵢ`. Note that some of the `kᵢ_eq` may be heterogeneous; this happens when
there are dependencies between the `jᵢ`. The construction of `T'` is performed
by `generalizes.step1` and `generalizes.step2`.

Having constructed `T'`, we can `assert` it and use it to construct a proof of
the original target by instantiating the binders with

    j₁ ... jₙ (eq.refl j₁) ... (heq.refl jₙ).

This leaves us with a generalized goal. This construction is performed by
`generalizes.step3`.
-/

universes u v w

namespace tactic

open expr

namespace generalizes

/--
Input:

- Target expression `e`.
- List of expressions `jᵢ` to be generalised, along with a name for the local
  const that will replace them. The `jᵢ` must be in dependency order:
  `[n, fin n]` is okay but `[fin n, n]` is not.

Output:

- List of new local constants `kᵢ`, one for each `jᵢ`.
- `e` with the `jᵢ` replaced by the `kᵢ`, i.e. `e[jᵢ := kᵢ]...[j₀ := k₀]`.

Note that the substitution also affects the types of the `kᵢ`: If `jᵢ : Jᵢ` then
`kᵢ : Jᵢ[jᵢ₋₁ := kᵢ₋₁]...[j₀ := k₀]`.

The transparency `md` and the boolean `unify` are passed to `kabstract` when we
abstract over occurrences of the `jᵢ` in `e`.
-/
meta def step1 (md : transparency) (unify : bool)
  (e : expr) (to_generalize : list (name × expr)) : tactic (expr × list expr) := do
  let go : name × expr → expr × list expr → tactic (expr × list expr) :=
        λ ⟨n, j⟩ ⟨e, ks⟩, do {
          J ← infer_type j,
          k ← mk_local' n binder_info.default J,
          e ← kreplace e j k md unify,
          ks ← ks.mmap $ λ k', kreplace k' j k md unify,
          pure (e, k :: ks) },
  to_generalize.mfoldr go (e, [])

/--
Input: for each equation that should be generated: the equation name, the
argument `jᵢ` and the corresponding local constant `kᵢ` from step 1.

Output: for each element of the input list a new local constant of type
`jᵢ = kᵢ` or `jᵢ == kᵢ` and a proof of `jᵢ = jᵢ` or `jᵢ == jᵢ`.

The transparency `md` is used when determining whether the type of `jᵢ` is defeq
to the type of `kᵢ` (and thus whether to generate a homogeneous or heterogeneous
equation).
-/
meta def step2 (md : transparency)
  (to_generalize : list (name × expr × expr))
  : tactic (list (expr × expr)) :=
to_generalize.mmap $ λ ⟨n, j, k⟩, do
  J ← infer_type j,
  K ← infer_type k,
  sort u ← infer_type K |
    fail! "generalizes'/step2: expected the type of {K} to be a sort",
  homogeneous ← succeeds $ is_def_eq J K md,
  let ⟨eq_type, eq_proof⟩ :=
    if homogeneous
      then ((const `eq  [u]) K k j  , (const `eq.refl  [u]) J j)
      else ((const `heq [u]) K k J j, (const `heq.refl [u]) J j),
  eq ← mk_local' n binder_info.default eq_type,
  pure (eq, eq_proof)

/--
Input: The `jᵢ`; the local constants `kᵢ` from step 1; the equations and their
proofs from step 2.

This step is the first one that changes the goal (and also the last one
overall). It asserts the generalized goal, then derives the current goal from
it. This leaves us with the generalized goal.
-/
meta def step3 (e : expr) (js ks eqs eq_proofs : list expr)
  : tactic unit :=
focus1 $ do
  let new_target_type := (e.pis eqs).pis ks,
  type_check new_target_type <|> fail!
    "generalizes': unable to generalize the target because the generalized target type does not type check:\n{new_target_type}",
  n ← mk_fresh_name,
  new_target ← assert n new_target_type,
  swap,
  let target_proof := new_target.mk_app $ js ++ eq_proofs,
  exact target_proof

end generalizes

open generalizes


/--
Generalizes the target over each of the expressions in `args`. Given
`args = [(a₁, h₁, arg₁), ...]`, this changes the target to

    ∀ (a₁ : T₁) ... (h₁ : a₁ = arg₁) ..., U

where `U` is the current target with every occurrence of `argᵢ` replaced by
`aᵢ`. A similar effect can be achieved by using `generalize` once for each of
the `args`, but if there are dependencies between the `args`, this may fail to
perform some generalizations.

The replacement is performed using keyed matching/unification with transparency
`md`. `unify` determines whether matching or unification is used. See
`kabstract`.

The `args` must be given in dependency order, so `[n, fin n]` is okay but
`[fin n, n]` will result in an error.

After generalizing the `args`, the target type may no longer type check.
`generalizes'` will then raise an error.
-/
meta def generalizes' (args : list (name × option name × expr))
  (md := semireducible) (unify := tt) : tactic unit := do
  tgt ← target,
  let stage1_args := args.map $ λ ⟨n, _, j⟩, (n, j),
  ⟨e, ks⟩ ← step1 md unify tgt stage1_args,
  let stage2_args : list (option (name × expr × expr)) :=
    args.map₂ (λ ⟨_, eq_name, j⟩ k, eq_name.map $ λ eq_name, (eq_name, j, k)) ks,
  let stage2_args := stage2_args.reduce_option,
  eqs_and_proofs ← step2 md stage2_args,
  let eqs := eqs_and_proofs.map prod.fst,
  let eq_proofs := eqs_and_proofs.map prod.snd,
  let js := args.map (prod.snd ∘ prod.snd),
  step3 e js ks eqs eq_proofs

/--
Like `generalizes'`, but also introduces the generalized constants and their
associated equations into the context.
-/
meta def generalizes_intro (args : list (name × option name × expr))
  (md := semireducible) (unify := tt) : tactic (list expr × list expr) := do
  generalizes' args md unify,
  ks ← intron' args.length,
  eqs ← intron' $ args.countp $ λ x, x.snd.fst.is_some,
  pure (ks, eqs)

namespace interactive

open interactive
open lean.parser

private meta def generalizes_arg_parser_eq : pexpr → lean.parser (pexpr × name)
| (app (app (macro _ [const `eq _ ])  e) (local_const x _ _ _)) := pure (e, x)
| (app (app (macro _ [const `heq _ ]) e) (local_const x _ _ _)) := pure (e, x)
| _ := failure

private meta def generalizes_arg_parser : lean.parser (name × option name × pexpr) :=
with_desc "(id :)? expr = id" $ do
  lhs ← lean.parser.pexpr 0,
  (tk ":" >> match lhs with
    | local_const hyp_name _ _ _ := do
      (arg, arg_name) ← lean.parser.pexpr 0 >>= generalizes_arg_parser_eq,
      pure (arg_name, some hyp_name, arg)
    | _ := failure
    end) <|>
  (do
    (arg, arg_name) ← generalizes_arg_parser_eq lhs,
    pure (arg_name, none, arg))

private meta def generalizes_args_parser
  : lean.parser (list (name × option name × pexpr)) :=
with_desc "[(id :)? expr = id, ...]" $
  tk "[" *> sep_by (tk ",") generalizes_arg_parser <* tk "]"

/--
Generalizes the target over multiple expressions. For example, given the goal

    P : ∀ n, fin n → Prop
    n : ℕ
    f : fin n
    ⊢ P (nat.succ n) (fin.succ f)

you can use `generalizes [n'_eq : nat.succ n = n', f'_eq : fin.succ f == f']` to
get

    P : ∀ n, fin n → Prop
    n : ℕ
    f : fin n
    n' : ℕ
    n'_eq : n' = nat.succ n
    f' : fin n'
    f'_eq : f' == fin.succ f
    ⊢ P n' f'

The expressions must be given in dependency order, so
`[f'_eq : fin.succ f == f', n'_eq : nat.succ n = n']` would fail since the type
of `fin.succ f` is `nat.succ n`.

You can choose to omit some or all of the generated equations. For the above
example, `generalizes [nat.succ n = n', fin.succ f == f']` gets you

    P : ∀ n, fin n → Prop
    n : ℕ
    f : fin n
    n' : ℕ
    f' : fin n'
    ⊢ P n' f'

After generalization, the target type may no longer type check. `generalizes`
will then raise an error.
-/
meta def generalizes (args : parse generalizes_args_parser) : tactic unit :=
propagate_tags $ do
  args ← args.mmap $ λ ⟨arg_name, hyp_name, arg⟩, do {
    arg ← to_expr arg,
    pure (arg_name, hyp_name, arg) },
  generalizes_intro args,
  pure ()

add_tactic_doc
{ name       := "generalizes",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.generalizes],
  tags       := ["context management"],
  inherit_description_from := `tactic.interactive.generalizes }

end interactive
end tactic
