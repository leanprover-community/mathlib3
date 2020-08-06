/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/
import tactic.induction.util
import data.nat.basic

/-!
# The `unify_equations` tactic

This module defines `unify_equations`, a first-order unification tactic that
unifies one or more equations in the context. It implements Conor McBride's
Qnify algorithm [^qnify].

The tactic takes as input some equations which it simplifies one after the
other. Each equation is simplified by applying one of several possible
unification steps. Each such step may output other (simpler) equations which are
unified recursively until no unification step applies any more. See
`tactic.interactive.unify_equations` for an example and an explanation of the
different steps.

[^qnify]: Conor McBride. Inverting inductively defined relations in LEGO.
In E. Giménez and C. Paulin-Mohring (eds.), Types for Proofs and Programs 1996.
-/

open expr

namespace tactic
namespace unify_equations

/--
The result of a unification step:

- `simplified hs` means that the step succeeded and produced new (simpler)
  equations `hs`. `hs` can be empty.
- `goal_solved` means that the step succeeded and solved the goal (by deriving a
  contradiction from the given equation).
- `not_simplified` means that the step failed to simplify the equation.
-/
meta inductive unification_step_result
| simplified (next_equations : list name)
| not_simplified
| goal_solved

export unification_step_result

/--
A unification step is a tactic that attempts to simplify a given equation and
returns a `unification_step_result`. The inputs are:

- `equ`, the equation being processed. Must be a local constant.
- `lhs_type` and `rhs_type`, the types of equ's LHS and RHS. For homogeneous
  equations, these are defeq.
- `lhs` and `rhs`, `equ`'s LHS and RHS.
- `lhs_whnf` and `rhs_whnf`, `equ`'s LHS and RHS in WHNF.
- `u`, `equ`'s level.

So `equ : @eq.{u} lhs_type lhs rhs` or `equ : @heq.{u} lhs_type lhs rhs_type rhs`.
-/
@[reducible] meta def unification_step :=
  ∀ (equ lhs_type rhs_type lhs rhs lhs_whnf rhs_whnf : expr) (u : level),
  tactic unification_step_result

/--
For `equ : t == u` with `t : T` and `u : U`, if `T` and `U` are defeq,
we replace `equ` with `equ : t = u`.
-/
meta def unify_heterogeneous : unification_step :=
λ equ lhs_type rhs_type lhs rhs _ _ _,
do {
  is_def_eq lhs_type rhs_type,
  p ← to_expr ``(@eq_of_heq %%lhs_type %%lhs %%rhs %%equ),
  t ← to_expr ``(@eq %%lhs_type %%lhs %%rhs),
  equ ← replace' equ p (some t),
  pure $ simplified [equ.local_pp_name]
} <|>
pure not_simplified

/--
For `equ : t = u`, if `t` and `u` are defeq, we delete `equ`.
-/
meta def unify_defeq : unification_step :=
λ equ lhs_type _ _ _ lhs_whnf rhs_whnf _,
do {
  is_def_eq lhs_whnf rhs_whnf,
  clear equ,
  pure $ simplified []
} <|>
pure not_simplified

/--
For `equ : x = t` or `equ : t = x`, where `x` is a local constant, we
substitute `x` with `t` in the goal.
-/
meta def unify_var : unification_step :=
λ equ type _ lhs rhs lhs_whnf rhs_whnf u,
do {
  let lhs_is_local := lhs_whnf.is_local_constant,
  let rhs_is_local := rhs_whnf.is_local_constant,
  guard $ lhs_is_local ∨ rhs_is_local,
  let t :=
    if lhs_is_local
      then (const `eq [u]) type lhs_whnf rhs
      else (const `eq [u]) type lhs rhs_whnf,
  change_core t (some equ),
  equ ← get_local equ.local_pp_name,
  subst_core equ,
  pure $ simplified []
} <|>
pure not_simplified

-- TODO copied from core (init/meta/injection_tactic.lean)
meta def injection_with (h : expr) (ns : list name)
  (base := `h) (offset := some 1) : tactic (list expr × list name) :=
do
  H ← infer_type h,
  (lhs, rhs, constructor_left, constructor_right, inj_name) ← do {
    (lhs, rhs) ← match_eq H,
    lhs ← whnf_ginductive lhs,
    rhs ← whnf_ginductive rhs,
    env ← get_env,
    (const constructor_left _) ← pure $ get_app_fn lhs,
    (const constructor_right _) ← pure $ get_app_fn rhs,
    inj_name ← resolve_constant $ constructor_left ++ "inj_arrow",
    pure (lhs, rhs, constructor_left, constructor_right, inj_name)
  } <|> fail
    "injection tactic failed, argument must be an equality proof where lhs and rhs are of the form (c ...), where c is a constructor",
  if constructor_left = constructor_right then do
    inj ← mk_const inj_name,
    inj_type ← infer_type inj,
    inj_arity ← get_pi_arity inj_type,
    let num_equations :=
      (inj_type.nth_binding_body (inj_arity - 1)).binding_domain.pi_arity,
    tgt ← target,
    proof ← mk_mapp inj_name (list.repeat none (inj_arity - 3) ++ [some h, some tgt]),
    eapply proof,
    intron_with num_equations ns base offset
  else do
    tgt ← target,
    let inductive_name := constructor_left.get_prefix,
    pr ← mk_app (inductive_name <.> "no_confusion") [tgt, lhs, rhs, h],
    exact pr,
    return ([], ns)

/--
Given `equ : C x₁ ... xₙ = D y₁ ... yₘ` with `C` and `D` constructors of the
same datatype `I`:

- If `C ≠ D`, we solve the goal by contradiction using the no-confusion rule.
- If `C = D`, we clear `equ` and add equations `x₁ = y₁`, ..., `xₙ = yₙ`.
-/
meta def unify_constructor_headed : unification_step :=
λ equ _ _ _ _ _ _ _,
do {
  (next, _) ← injection_with equ [] `_ none,
  try $ clear equ,
  pure $
    if next.empty
      then goal_solved
      else simplified $ next.map expr.local_pp_name
} <|>
pure not_simplified

/--
For `type = I x₁ ... xₙ`, where `I` is an inductive type, `get_sizeof type`
returns the constant `I.sizeof`. Fails if `type` is not of this form or if no
such constant exists.
-/
meta def get_sizeof (type : expr) : tactic pexpr := do
  n ← get_inductive_name type,
  resolve_name $ n ++ `sizeof

lemma plus_gt (n m : ℕ) : m ≠ 0 → n + m > n :=
by { induction m, { contradiction }, { simp } }

lemma n_plus_m_plus_one_ne_n (n m : ℕ) : n + (m + 1) ≠ n :=
by simp [ne_of_gt, plus_gt]
-- Linarith could prove this, but I want to avoid that dependency.

/--
`match_n_plus_m n e` matches `e` of the form `nat.succ (... (nat.succ e')...)`.
It returns `n` plus the number of `succ` constructors and `e'`. The matching is
performed up to normalisation with transparency `md`.
-/
meta def match_n_plus_m (md) : ℕ → expr → tactic (ℕ × expr) :=
λ n e, do
  e ← whnf e md,
  match e with
  | `(nat.succ %%e) := match_n_plus_m (n + 1) e
  | _ := pure (n, e)
  end

/--
Given `equ : n + m = n` or `equ : n = n + m` with `n` and `m` natural numbers
and `m` a nonzero literal, this tactic produces a proof of `false`. More
precisely, the two sides of the equation must be of the form
`nat.succ (... (nat.succ e)...)` with different numbers of `nat.succ`
constructors. Matching is performed with transparency `md`.
-/
meta def contradict_n_eq_n_plus_m (md : transparency) (equ lhs rhs : expr) :
  tactic expr := do
  ⟨lhs_n, lhs_e⟩ ← match_n_plus_m md 0 lhs,
  ⟨rhs_n, rhs_e⟩ ← match_n_plus_m md 0 rhs,
  is_def_eq lhs_e rhs_e md <|> fail
    "internal error in contradict_n_eq_n_plus_m:\nexpected {lhs_e} and {rhs_e} to be definitionally equal at transparency {md}.",
  let common := lhs_e,
  guard (lhs_n ≠ rhs_n) <|> fail
    "internal error in contradict_n_eq_n_plus_m:\nexpected {lhs_n} and {rhs_n} to be different.",
  -- Ensure that lhs_n is bigger than rhs_n. Swap lhs and rhs if that's not
  -- already the case.
  ⟨equ, lhs_n, rhs_n⟩ ←
    if lhs_n > rhs_n
      then pure (equ, lhs_n, rhs_n)
      else do {
        equ ← to_expr ``(eq.symm %%equ),
        pure (equ, rhs_n, lhs_n)
      },
  let diff := lhs_n - rhs_n,
  let rhs_n_expr := reflect rhs_n,
  n ← to_expr ``(%%common + %%rhs_n_expr),
  let m := reflect (diff - 1),
  pure `(n_plus_m_plus_one_ne_n %%n %%m %%equ)

/--
Given `equ : t = u` with `t, u : I` and `I.sizeof t ≠ I.sizeof u`, we solve the
goal by contradiction.
-/
meta def unify_cyclic : unification_step :=
λ equ type _ _ _ lhs_whnf rhs_whnf _,
do {
  -- Establish `sizeof lhs = sizeof rhs`.
  sizeof ← get_sizeof type,
  hyp_lhs ← to_expr ``(%%sizeof %%lhs_whnf),
  hyp_rhs ← to_expr ``(%%sizeof %%rhs_whnf),
  hyp_type ← to_expr ``(@eq ℕ %%hyp_lhs %%hyp_rhs),
  hyp_proof ← to_expr ``(@congr_arg %%type ℕ %%lhs_whnf %%rhs_whnf %%sizeof %%equ),
  hyp_name ← mk_fresh_name,
  hyp ← note hyp_name hyp_type hyp_proof,

  -- Derive a contradiction (if indeed `sizeof lhs ≠ sizeof rhs`).
  falso ← contradict_n_eq_n_plus_m semireducible hyp hyp_lhs hyp_rhs,
  exfalso,
  exact falso,
  pure goal_solved
} <|>
pure not_simplified

/--
Sequence two unification steps. First run step `s`. If this was successful
(i.e. it simplified or solved the goal), stop and return the result of `s`.
Otherwise run `t` and return its result.
-/
meta def sequence_simplifiers (s t : unification_step) : unification_step :=
λ equ lhs_type rhs_type lhs rhs lhs_whnf rhs_whnf u,
do
  r ← s equ lhs_type rhs_type lhs rhs lhs_whnf rhs_whnf u,
  match r with
  | simplified _ := pure r
  | goal_solved := pure r
  | not_simplified := t equ lhs_type rhs_type lhs rhs lhs_whnf rhs_whnf u
  end

/--
For `equ : t = u`, try the following methods in order: `unify_defeq`,
`unify_var`, `unify_constructor_headed`, `unify_cyclic`. If any of them is
successful, stop and return its result. If none is successful, fail.
-/
meta def unify_homogeneous : unification_step :=
list.foldl sequence_simplifiers (λ _ _ _ _ _ _ _ _, pure not_simplified)
  [unify_defeq, unify_var, unify_constructor_headed, unify_cyclic]

end unify_equations


open unify_equations

/--
If `equ` is the display name of a local constant with type `t = u` or `t == u`,
then `unify_equation_once equ` simplifies it once using
`unify_equations.unify_homogeneous` or `unify_equations.unify_heterogeneous`.

Otherwise it fails.
-/
meta def unify_equation_once (equ : name) : tactic unification_step_result := do
  eque ← get_local equ,
  t ← infer_type eque,
  match t with
  | (app (app (app (const `eq [u]) type) lhs) rhs) := do
    lhs_whnf ← whnf_ginductive lhs,
    rhs_whnf ← whnf_ginductive rhs,
    unify_homogeneous eque type type lhs rhs lhs_whnf rhs_whnf u
  | (app (app (app (app (const `heq [u]) lhs_type) lhs) rhs_type) rhs) := do
    lhs_whnf ← whnf_ginductive lhs,
    rhs_whnf ← whnf_ginductive rhs,
    unify_heterogeneous eque lhs_type rhs_type lhs rhs lhs_whnf rhs_whnf u
  | _ := fail! "Expected {equ} to be an equation, but its type is\n{t}."
  end

/--
Given a list of display names of local hypotheses that are (homogeneous or
heterogeneous) equations, `unify_equations` performs first-order unification on
each hypothesis in order. See `tactic.interactive.unify_equations` for an
example and an explanation of what unification does.

Returns true iff the goal has been solved during the unification process.

Note: you must make sure that the input names are unique in the context.
-/
meta def unify_equations : list name → tactic bool
| [] := pure ff
| (h :: hs) := do
  res ← unify_equation_once h,
  match res with
  | simplified hs' := unify_equations $ hs' ++ hs
  | not_simplified := unify_equations hs
  | goal_solved := pure tt
  end


namespace interactive

open lean.parser

/--
`unify_equations eq₁ ... eqₙ` performs a form of first-order unification on the
hypotheses `eqᵢ`. The `eqᵢ` must be homogeneous or heterogeneous equations.
Unification means that the equations are simplified using various facts about
constructors. For instance, consider this goal:

```
P : ∀ n, fin n → Prop
n m : ℕ
f : fin n
g : fin m
h₁ : n + 1 = m + 1
h₂ : f == g
h₃ : P n f
⊢ P m g
```

After `unify_equations h₁ h₂`, we get

```
P : ∀ n, fin n → Prop
n : ℕ
f : fin n
h₃ : P n f
⊢ P n f
```

In the example, `unify_equations` uses the fact that every constructor is
injective to conclude `n = m` from `h₁`. Then it replaces every `m` with `n` and
moves on to `h₂`. The types of `f` and `g` are now equal, so the heterogeneous
equation turns into a homogeneous one and `g` is replaced by `f`. Note that the
equations are processed from left to right, so `unify_equations h₂ h₁` would not
simplify as much.

In general, `unify_equations` uses the following steps on each equation until
none of them applies any more:

- Constructor injectivity: if `nat.succ n = nat.succ m` then `n = m`.
- Substitution: if `x = e` for some hypothesis `x`, then `x` is replaced by `e`
  everywhere.
- No-confusion: `nat.succ n = nat.zero` is a contradiction. If we have such an
  equation, the goal is solved immediately.
- Cycle elimination: `n = nat.succ n` is a contradiction.
- Redundancy: if `t = u` but `t` and `u` are already definitionally equal, then
  this equation is removed.
- Downgrading of heterogeneous equations: if `t == u` but `t` and `u` have the
  same type (up to definitional equality), then the equation is replaced by
  `t = u`.
-/
meta def unify_equations (eqs : interactive.parse (many ident)) :
  tactic unit :=
tactic.unify_equations eqs *> skip

end interactive
end tactic
