/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/
import tactic.induction.util
import data.nat.basic

open expr

namespace tactic
namespace unify_equations

meta inductive simplification_result
| simplified (next_equations : list name)
| not_simplified
| goal_solved

export simplification_result

meta def unify_heterogeneous (equ lhs_type rhs_type lhs rhs : expr) :
  tactic simplification_result :=
do {
  is_def_eq lhs_type rhs_type,
  p ← to_expr ``(@eq_of_heq %%lhs_type %%lhs %%rhs %%equ),
  t ← to_expr ``(@eq %%lhs_type %%lhs %%rhs),
  equ ← replace' equ p (some t),
  pure $ simplified [equ.local_pp_name]
} <|>
pure not_simplified

meta def unify_defeq (equ type lhs rhs lhs_whnf rhs_whnf : expr)
  (u : level) : tactic simplification_result :=
do {
  is_def_eq lhs_whnf rhs_whnf,
  clear equ,
  pure $ simplified []
} <|>
pure not_simplified

meta def unify_var (equ type lhs rhs lhs_whnf rhs_whnf : expr)
  (u : level) : tactic simplification_result :=
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

meta def get_sizeof (type : expr) : tactic pexpr := do
  n ← get_inductive_name type,
  let sizeof_name := n ++ `sizeof,
  sizeof ← resolve_name $ sizeof_name,
  pure sizeof

lemma plus_gt (n m : ℕ) : m ≠ 0 → n + m > n :=
by { induction m, { contradiction }, { simp } }

lemma n_plus_m_plus_one_ne_n (n m : ℕ) : n + (m + 1) ≠ n :=
by simp [ne_of_gt, plus_gt]
-- Linarith could prove this, but I want to avoid that dependency.

meta def match_n_plus_m (md) : ℕ → expr → tactic (ℕ × expr) :=
λ n e, do
  e ← whnf e md,
  match e with
  | `(nat.succ %%e) := match_n_plus_m (n + 1) e
  | _ := pure (n, e)
  end

meta def contradict_n_eq_n_plus_m (md : transparency) (equ lhs rhs : expr) :
  tactic expr := do
  ⟨lhs_n, lhs_e⟩ ← match_n_plus_m md 0 lhs,
  ⟨rhs_n, rhs_e⟩ ← match_n_plus_m md 0 rhs,
  is_def_eq lhs_e rhs_e md <|> fail "TODO",
  let common := lhs_e,
  guard (lhs_n ≠ rhs_n) <|> fail "TODO",
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

meta def unify_cyclic (equ type lhs rhs lhs_whnf rhs_whnf : expr)
  (u : level) : tactic simplification_result :=
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
    -- C.inj_arrow, for a given constructor C of datatype D, has type
    --
    --     ∀ (A₁ ... Aₙ) (x₁ ... xₘ) (y₁ ... yₘ), C x₁ ... xₘ = C y₁ ... yₘ
    --       → ∀ ⦃P : Sort u⦄, (x₁ = y₁ → ... → yₖ = yₖ → P) → P
    --
    -- where the Aᵢ are parameters of D and the xᵢ/yᵢ are arguments of C.
    -- Note that if xᵢ/yᵢ are propositions, no equation is generated, so the
    -- number of equations is not necessarily the constructor arity.

    -- First, we find out how many equations we need to intro later.
    inj ← mk_const inj_name,
    inj_type ← infer_type inj,
    inj_arity ← get_pi_arity inj_type,
    let num_equations :=
      (inj_type.nth_binding_body (inj_arity - 1)).binding_domain.pi_arity,

    -- Now we generate the actual proof of the target.
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

meta def unify_constructor_headed (equ type lhs rhs lhs_whnf rhs_whnf : expr)
  (u : level) : tactic simplification_result :=
do {
  (next, _) ← injection_with equ [] `_ none,
  try $ clear equ,
  pure $
    if next.empty
      then goal_solved
      else simplified $ next.map expr.local_pp_name
} <|>
pure not_simplified

meta def sequence_simplifiers (s t : tactic simplification_result) :
  tactic simplification_result := do
  r ← s,
  match r with
  | simplified _ := pure r
  | goal_solved := pure r
  | not_simplified := t
  end

meta def unify_homogeneous (equ type lhs rhs lhs_whnf rhs_whnf : expr)
  (u : level) : tactic simplification_result := do
  list.foldl sequence_simplifiers (pure not_simplified)
    [ unify_defeq equ type lhs rhs lhs_whnf rhs_whnf u,
      unify_var equ type lhs rhs lhs_whnf rhs_whnf u,
      unify_constructor_headed equ type lhs rhs lhs_whnf rhs_whnf u,
      unify_cyclic equ type lhs rhs lhs_whnf rhs_whnf u ]

end unify_equations


open unify_equations

meta def unify_equation (equ : name) : tactic simplification_result := do
  eque ← get_local equ,
  t ← infer_type eque,
  match t with
  | (app (app (app (const `eq [u]) type) lhs) rhs) := do
    lhs_whnf ← whnf_ginductive lhs,
    rhs_whnf ← whnf_ginductive rhs,
    unify_homogeneous eque type lhs rhs lhs_whnf rhs_whnf u
  | `(@heq %%lhs_type %%lhs %%rhs_type %%rhs) := do
    unify_heterogeneous eque lhs_type rhs_type lhs rhs
  | _ := fail! "Expected {equ} to be an equation, but its type is\n{t}."
  end

meta def unify_equations : list name → tactic bool
| [] := pure ff
| (h :: hs) := do
  res ← unify_equation h,
  match res with
  | simplified hs' := unify_equations $ hs' ++ hs
  | not_simplified := unify_equations hs
  | goal_solved := pure tt
  end


namespace interactive

open lean.parser

meta def simplify_index_equations (eqs : interactive.parse (many ident)) :
  tactic unit :=
tactic.unify_equations eqs *> skip

end interactive
end tactic
