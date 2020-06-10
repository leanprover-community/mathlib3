/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
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

To generalize the target `T` over expressions `a₁ : T₁, ..., aₙ : Tₙ`, we first
create the new target type

    T' = ∀ (j₁ : T₁) (j₁_eq : j₁ == a₁) ..., T''

where `T''` is `T` with any occurrences of the `aᵢ` replaced by the
corresponding `jᵢ`. Creating this expression is a bit difficult because we must
be careful when there are dependencies between the `aᵢ`. Suppose that `a₁ : T₁`
and `a₂ : P a₁`. Then we want to end up with the target

    T' = ∀ (j₁ : T₁) (j₁_eq : j₁ == a₁) (j₂ : P j₁) (j₂_eq : @heq (P j₁) j₂ (P a₁) a₂), ...

Note the type of the heterogeneous equation `j₂_eq`: When abstracting over `a₁`,
we want to replace `a₁` by `j₁` in the left-hand side to get the correct type
for `j₂`, but not in the right-hand side. This construction is performed by
`generalizes'_aux₁` and `generalizes'_aux₂`.

Having constructed `T'`, we can `assert` it and use it to construct a proof of
the original target by instantiating the binders with `a₁`, `heq.refl a₁`, `a₂`,
`heq.refl a₂` etc. This leaves us with a generalized goal.
-/

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
`generalizes'_aux₂ md []` takes as input the expression `e` produced by
`generalizes'_aux₁` and a list containing, for each argument to be generalized:

- A name for the generalisation equation. If this is `none`, no equation is
  generated.
- The local constant produced by `generalizes'_aux₁`.
- The argument itself.

From this information, it generates a type of the form

    ∀ (j₁ : T₁) (j₁_eq : j₁ = a₁) (j₂ : T₂) (j₂_eq : j₂ == a₂), e

where the `aᵢ` are the arguments and the `jᵢ` correspond to the local constants.

It also returns, for each argument, whether an equation was generated for the
argument and if so, whether the equation is homogeneous (`tt`) or heterogeneous
(`ff`).

The transparency `md` is used when determining whether the types of an argument
and its associated constant are definitionally equal (and thus whether to
generate a homogeneous or a heterogeneous equation).
-/
private meta def generalizes'_aux₂ (md : transparency)
  : list (option bool) → expr → list (option name × expr × expr)
  → tactic (expr × list (option bool))
| eq_kinds e [] := pure (e, eq_kinds.reverse)
| eq_kinds e ((eq_name, cnst, arg) :: cs) := do
  cnst_type ← infer_type cnst,
  arg_type ← infer_type arg,
  sort u ← infer_type arg_type,
  ⟨eq_binder, eq_kind⟩ ← do {
    match eq_name with
    | none := pure ((id : expr → expr), none)
    | some eq_name := do
        homogeneous ← succeeds $ is_def_eq cnst_type arg_type,
        let eq_type :=
          if homogeneous
            then ((const `eq [u]) cnst_type (var 0) arg)
            else ((const `heq [u]) cnst_type (var 0) arg_type arg),
        let eq_binder : expr → expr := λ e,
          pi eq_name binder_info.default eq_type (e.lift_vars 0 1),
        pure (eq_binder, some homogeneous )
    end
  },
  let e :=
    pi cnst.local_pp_name binder_info.default cnst_type $
    eq_binder $
    e.abstract cnst,
  generalizes'_aux₂ (eq_kind :: eq_kinds) e cs

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
meta def generalizes' (args : list (name × option name × expr))
  (md := semireducible) (unify := tt) : tactic unit :=
focus1 $ do
  tgt ← target,
  let args_rev := args.reverse,
  (tgt, cnsts) ← generalizes'_aux₁ md unify tgt []
    (args_rev.map (λ ⟨e_name, _, e⟩, (e_name, e))),
  let args' :=
    @list.map₂ (name × option name × expr) expr _
      (λ ⟨_, eq_name, x⟩ cnst, (eq_name, cnst, x)) args_rev cnsts,
  ⟨tgt, eq_kinds⟩ ← generalizes'_aux₂ md [] tgt args',
  let eq_kinds := eq_kinds.reverse,
  type_check tgt <|> fail!
    "generalizes: unable to generalize the target because the generalized target type does not type check:\n{tgt}",
  n ← mk_fresh_name,
  h ← assert n tgt,
  swap,
  let args' :=
    @list.map₂ (name × option name × expr) (option bool) _
      (λ ⟨_, _, x⟩ eq_kind, (x, eq_kind)) args eq_kinds,
  apps ← args'.mmap $ λ ⟨x, eq_kind⟩, do {
    match eq_kind with
    | none := pure [x]
    | some eq_is_homogeneous := do
      x_type ← infer_type x,
      sort u ← infer_type x_type,
      let eq_proof :=
        if eq_is_homogeneous
          then (const `eq.refl [u]) x_type x
          else (const `heq.refl [u]) x_type x,
      pure [x, eq_proof]
    end
  },
  exact $ h.mk_app apps.join

/--
Like `generalizes'`, but also introduces the generalized constants and their
associated equations into the context.
-/
meta def generalizes_intro (args : list (name × option name × expr))
  (md := semireducible) (unify := tt) : tactic (list expr) := do
  generalizes' args md unify,
  let binder_nos := args.map (λ ⟨_, hyp, _⟩, 1 + if hyp.is_some then 1 else 0),
  intron' binder_nos.sum

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
example, `generalizes [(nat.succ n = n'), (fin.succ f == f')]` gets you

    P : ∀ n, fin n → Prop
    n : ℕ
    f : fin n
    n' : ℕ
    f' : fin n'
    ⊢ P n' f'

Note the parentheses; these are necessary to avoid parsing issues.

After generalization, the target type may no longer type check. `generalizes`
will then raise an error.
-/
meta def generalizes (args : parse generalizes_args_parser) : tactic unit :=
propagate_tags $ do
  args ← args.mmap $ λ ⟨arg_name, hyp_name, arg⟩, do {
    arg ← to_expr arg,
    pure (arg_name, hyp_name, arg)
  },
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
