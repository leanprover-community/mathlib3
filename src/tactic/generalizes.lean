/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/

import tactic.core

universes u v w

namespace tactic

open expr

/--
`generalizes'_aux₁ md unify e [] args` iterates through the `args` from left to
right. In each step of the iteration, any occurrences of the expression from
`args` in `e` is replaced by a new local constant. The local constant's pretty
name is the name given in `args`. The `args` must be given in reverse dependency
order: `[fin n, n]` is okay, but `[n, fin n]` won't work.

The result of `generalizes'_aux₁` is `e` with all the `args` replaced and the
list of new local constants, one for each element of `args`. Note that the local
constants are not added to the local context.

`md` and `unify` control how subterms of `e` are matched against the expressions
in `args`; see `kabstract`.
-/
private meta def generalizes'_aux₁ (md : transparency) (unify : bool)
  : expr → list expr → list (name × expr) → tactic (expr × list expr)
| e cnsts [] := pure (e, cnsts.reverse)
| e cnsts ((n, x) :: xs) := do
  x_type ← infer_type x,
  c ← mk_local' n binder_info.default x_type,
  e ← kreplace e x c md unify,
  cnsts ← cnsts.mmap $ λ c', kreplace c' x c md unify,
  generalizes'_aux₁ e (c :: cnsts) xs

/--
`generalizes'_aux₂` takes as input the expression `e` produced by
`generalizes'_aux₁` and a list containing, for each argument to be generalized:

- a name for the generalisation equation;
- the local constant produced by `generalizes'_aux₁`;
- the argument itself.

From this information, it generates a type of the form

    ∀ (j₁ : T₁) (j₁_eq : j₁ == a₁) (j₂ : T₂) (j₂_eq : j₂ == a₂), e

where the `aᵢ` are the arguments and the `jᵢ` correspond to the local constants.
-/
private meta def generalizes'_aux₂ : expr → list (name × expr × expr) → tactic expr
| e [] := pure e
| e ((eq_name, cnst, arg) :: cs) := do
  cnst_type ← infer_type cnst,
  arg_type ← infer_type arg,
  sort u ← infer_type arg_type,
  let e :=
    pi cnst.local_pp_name binder_info.default cnst_type $
    pi eq_name binder_info.default ((const `heq [u]) cnst_type (var 0) arg_type arg) $
    (e.abstract cnst).lift_vars 0 1,
  generalizes'_aux₂ e cs

/--
Generalizes the target over each of the expressions in `args`. Given
`args = [(a₁, h₁, arg₁), ...]`, this changes the target to

    ∀ (a₁ : T₁) (h₁ : a₁ == arg₁) ..., U

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
meta def generalizes' (args : list (name × name × expr))
  (md := semireducible) (unify := tt) : tactic unit :=
focus1 $ do
  tgt ← target,
  let args_rev := args.reverse,
  (tgt, cnsts) ← generalizes'_aux₁ md unify tgt []
    (args_rev.map (λ ⟨e_name, _, e⟩, (e_name, e))),
  let args' :=
    @list.map₂ (name × name × expr) expr _
      (λ ⟨x_name, eq_name, x⟩ cnst, (eq_name, cnst, x)) args_rev cnsts,
  tgt ← generalizes'_aux₂ tgt args',
  type_check tgt <|> fail!
    "generalizes: unable to generalize the target because the generalized target type does not type check:\n{tgt}",
  n ← mk_fresh_name,
  h ← assert n tgt,
  swap,
  apps ← args.mmap $ λ ⟨_, _, x⟩, do {
    x_type ← infer_type x,
    sort u ← infer_type x_type,
    pure [x, (const `heq.refl [u]) x_type x]
  },
  exact $ h.mk_app apps.join


namespace interactive

open interactive
open lean.parser

private meta def generalizes_arg_parser : lean.parser (name × name × pexpr) :=
with_desc "id : expr = id" $ do
  hyp_name ← ident,
  tk ":",
  arg ← lean.parser.pexpr 0,
  (arg, arg_name) ←
    match arg with
    | (app (app (macro _ [const `eq _ ]) e) (local_const x _ _ _)) := pure (e, x)
    | (app (app (macro _ [const `heq _ ]) e) (local_const x _ _ _)) := pure (e, x)
    | _ := failure
    end,
  pure $ (arg_name, hyp_name, arg)

private meta def generalizes_args_parser
  : lean.parser (list (name × name × pexpr)) :=
with_desc "[id : expr = id, ...]" $
  tk "[" *> sep_by (tk ",") generalizes_arg_parser <* tk "]"

/--
Generalizes the target over multiple expressions. For example, given the goal

    P : ∀ n, fin n → Prop
    n : ℕ
    f : fin n
    ⊢ P (nat.succ n) (fin.succ f)

you can use `generalizes [n'_eq : nat.succ n = n', f'_eq : fin.succ f = f']` to get

    P : ∀ n, fin n → Prop
    n : ℕ
    f : fin n
    n' : ℕ
    n'_eq : n' == nat.succ n
    f' : fin n'
    f'_eq : f' == fin.succ f
    ⊢ P n' f'

The expressions must be given in dependency order, so
`[f'_eq : fin.succ f = f', n'_eq : nat.succ n = n']` would fail since the type of
`fin.succ f` is `nat.succ n`.

After generalization, the target type may no longer type check. `generalizes`
will then raise an error.
-/
meta def generalizes (args : parse generalizes_args_parser) : tactic unit :=
propagate_tags $ do
  args ← args.mmap $ λ ⟨arg_name, hyp_name, arg⟩, do {
    arg ← to_expr arg,
    pure (arg_name, hyp_name, arg)
  },
  n ← generalizes' args,
  intron $ args.length * 2,
  pure ()

end interactive
end tactic
