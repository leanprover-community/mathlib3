/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Mario Carneiro
-/

import tactic.core

/-!
# `choose` tactic

Performs Skolemization, that is, given `h : ∀ a:α, ∃ b:β, p a b |- G` produces
`f : α → β, hf: ∀ a, p a (f a) |- G`.
-/

namespace tactic

/-- Given `α : Sort u`, `nonemp : nonempty α`, `p : α → Prop`, a context of local variables
`ctxt`, and a pair of an element `val : α` and `spec : p val`,
`mk_sometimes u α nonemp p ctx (val, spec)` produces another pair `val', spec'`
such that `val'` does not have any free variables from elements of `ctxt` whose types are
propositions. This is done by applying `function.sometimes` to abstract over all the propositional
arguments. -/
meta def mk_sometimes (u : level) (α nonemp p : expr) :
  list expr → expr × expr → tactic (expr × expr)
| [] (val, spec) := pure (val, spec)
| (e :: ctxt) (val, spec) := do
  (val, spec) ← mk_sometimes ctxt (val, spec),
  t ← infer_type e,
  b ← is_prop t,
  pure $ if b then
    let val' := expr.bind_lambda val e in
    (expr.const ``function.sometimes [level.zero, u] t α nonemp val',
     expr.const ``function.sometimes_spec [u] t α nonemp p val' e spec)
  else (val, spec)

/-- Changes `(h : ∀xs, ∃a:α, p a) ⊢ g` to `(d : ∀xs, a) (s : ∀xs, p (d xs)) ⊢ g` and
`(h : ∀xs, p xs ∧ q xs) ⊢ g` to `(d : ∀xs, p xs) (s : ∀xs, q xs) ⊢ g`.
`choose1` returns a pair of the second local constant it introduces,
and the error result (see below).

If `nondep` is true and `α` is inhabited, then it will remove the dependency of `d` on
all propositional assumptions in `xs`. For example if `ys` are propositions then
`(h : ∀xs ys, ∃a:α, p a) ⊢ g` becomes `(d : ∀xs, a) (s : ∀xs ys, p (d xs)) ⊢ g`.

The second value returned by `choose1` is the result of nondep elimination:
* `none`: nondep elimination was not attempted or was not applicable
* `some none`: nondep elimination was successful
* ``some (some `(nonempty α))``: nondep elimination was unsuccessful
  because we could not find a `nonempty α` instance
-/
meta def choose1 (nondep : bool) (h : expr) (data : name) (spec : name) :
  tactic (expr × option (option expr)) := do
  t ← infer_type h,
  (ctxt, t) ← whnf t >>= open_pis,
  t ← whnf t transparency.all,
  match t with
  | `(@Exists %%α %%p) := do
    α_t ← infer_type α,
    expr.sort u ← whnf α_t transparency.all,
    (ne_fail, nonemp) ← if nondep then do
      let ne := expr.const ``nonempty [u] α,
      nonemp ← try_core (mk_instance ne <|> retrieve' (do
        m ← mk_meta_var ne,
        set_goals [m],
        ctxt.mmap' (λ e, do
          b ← is_proof e,
          monad.unlessb b $
            (mk_app ``nonempty.intro [e] >>= note_anon none) $> ()),
        unfreeze_local_instances >> apply_instance,
        instantiate_mvars m)),
      pure (some (option.guard (λ _, nonemp.is_none) ne), nonemp)
    else pure (none, none),
    ctxt' ← if nonemp.is_some then ctxt.mfilter (λ e, bnot <$> is_proof e) else pure ctxt,
    value ← mk_local_def data (α.pis ctxt'),
    t' ← head_beta (p.app (value.mk_app ctxt')),
    spec ← mk_local_def spec (t'.pis ctxt),
    (value_proof, spec_proof) ← nonemp.elim pure (λ nonemp, mk_sometimes u α nonemp p ctxt)
      (expr.const ``classical.some [u] α p (h.mk_app ctxt),
       expr.const ``classical.some_spec [u] α p (h.mk_app ctxt)),
    dependent_pose_core [(value, value_proof.lambdas ctxt'), (spec, spec_proof.lambdas ctxt)],
    try (tactic.clear h),
    intro1,
    e ← intro1,
    pure (e, ne_fail)
  | `(%%p ∧ %%q) := do
    mk_app ``and.elim_left [h.mk_app ctxt] >>= lambdas ctxt >>= note data none,
    hq ← mk_app ``and.elim_right [h.mk_app ctxt] >>= lambdas ctxt >>= note spec none,
    try (tactic.clear h),
    pure (hq, none)
  | _ := fail "expected a term of the shape `∀xs, ∃a, p xs a` or `∀xs, p xs ∧ q xs`"
  end

/-- Changes `(h : ∀xs, ∃as, p as ∧ q as) ⊢ g` to a list of functions `as`,
and a final hypothesis on `p as` and `q as`. If `nondep` is true then the functions will
be made to not depend on propositional arguments, when possible.

The last argument is an internal recursion variable, indicating whether nondep elimination
has been useful so far. The tactic fails if `nondep` is true, and nondep elimination is
attempted at least once, and it fails every time it is attempted, in which case it returns
an error complaining about the first attempt.
-/
meta def choose (nondep : bool) : expr → list name →
  opt_param (option (option expr)) none → tactic unit
| h [] _ := fail "expect list of variables"
| h [n] (some (some ne)) := do
  g ← mk_meta_var ne, set_goals [g], -- make a reasonable error state
  fail "choose: failed to synthesize nonempty instance"
| h [n] _ := do
  cnt ← revert h,
  intro n,
  intron (cnt - 1),
  return ()
| h (n::ns) ne_fail₁ := do
  (v, ne_fail₂) ← get_unused_name >>= choose1 nondep h n,
  choose v ns $
    match ne_fail₁, ne_fail₂ with
    | none, _ := ne_fail₂
    | some none, _ := some none
    | _, some none := some none
    | _, _ := ne_fail₁
    end

namespace interactive
setup_tactic_parser

/-- `choose a b h h' using hyp` takes an hypothesis `hyp` of the form
`∀ (x : X) (y : Y), ∃ (a : A) (b : B), P x y a b ∧ Q x y a b`
for some `P Q : X → Y → A → B → Prop` and outputs
into context a function `a : X → Y → A`, `b : X → Y → B` and two assumptions:
`h : ∀ (x : X) (y : Y), P x y (a x y) (b x y)` and
`h' : ∀ (x : X) (y : Y), Q x y (a x y) (b x y)`. It also works with dependent versions.

`choose! a b h h' using hyp` does the same, except that it will remove dependency of
the functions on propositional arguments if possible. For example if `Y` is a proposition
and `A` and `B` are nonempty in the above example then we will instead get
`a : X → A`, `b : X → B`, and the assumptions
`h : ∀ (x : X) (y : Y), P x y (a x) (b x)` and
`h' : ∀ (x : X) (y : Y), Q x y (a x) (b x)`.

Examples:

```lean
example (h : ∀n m : ℕ, ∃i j, m = n + i ∨ m + j = n) : true :=
begin
  choose i j h using h,
  guard_hyp i : ℕ → ℕ → ℕ,
  guard_hyp j : ℕ → ℕ → ℕ,
  guard_hyp h : ∀ (n m : ℕ), m = n + i n m ∨ m + j n m = n,
  trivial
end
```

```lean
example (h : ∀ i : ℕ, i < 7 → ∃ j, i < j ∧ j < i+i) : true :=
begin
  choose! f h h' using h,
  guard_hyp f : ℕ → ℕ,
  guard_hyp h : ∀ (i : ℕ), i < 7 → i < f i,
  guard_hyp h' : ∀ (i : ℕ), i < 7 → f i < i + i,
  trivial,
end
```
-/
meta def choose (nondep : parse (tk "!")?) (first : parse ident) (names : parse ident*)
  (tgt : parse (tk "using" *> texpr)?) : tactic unit := do
tgt ← match tgt with
  | none := get_local `this
  | some e := tactic.i_to_expr_strict e
  end,
tactic.choose nondep.is_some tgt (first :: names),
try (interactive.simp none none tt [simp_arg_type.expr
  ``(exists_prop)] [] (loc.ns $ some <$> names)),
try (tactic.clear tgt)

add_tactic_doc
{ name       := "choose",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.choose],
  tags       := ["classical logic"] }

end interactive
end tactic
