/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Without loss of generality tactic.
-/
import data.list.perm

open expr tactic lean lean.parser

local postfix `?`:9001 := optional
local postfix *:9001 := many

namespace tactic

private meta def update_pp_name : expr → name → expr
| (local_const n _ bi d) pp := local_const n pp bi d
| e n := e

private meta def elim_or : ℕ → expr → tactic (list expr)
| 0       h := fail "zero cases"
| 1       h := return [h]
| (n + 1) h := do
  [(_, [hl], []), (_, [hr], [])] ← induction h, -- there should be no dependent terms
  [gl, gr] ← get_goals,
  set_goals [gr],
  hsr ← elim_or n hr,
  gsr ← get_goals,
  set_goals (gl :: gsr),
  return (hl :: hsr)

private meta def dest_or : expr → tactic (list expr) | e := do
  `(%%a ∨ %%b) ← whnf e | return [e],
  lb ← dest_or b,
  return (a :: lb)

private meta def match_perms (pat : pattern) : expr → tactic (list $ list expr) | t :=
  (do
    m ← match_pattern pat t,
    guard (m.2.all expr.is_local_constant),
    return [m.2]) <|>
  (do
    `(%%l ∨ %%r) ← whnf t,
    m ← match_pattern pat l,
    rs ← match_perms r,
    return (m.2 :: rs))

meta def wlog (vars' : list expr) (h_cases fst_case : expr) (perms : list (list expr)) :
  tactic unit := do
  guard h_cases.is_local_constant,

  -- reorder s.t. context is Γ ⬝ vars ⬝ cases ⊢ ∀deps, …
  nr ← revert_lst (vars' ++ [h_cases]),
  vars ← intron' vars'.length,
  h_cases ← intro h_cases.local_pp_name,

  cases ← infer_type h_cases,
  h_fst_case ←
    mk_local_def h_cases.local_pp_name
      (fst_case.instantiate_locals $ (vars'.zip vars).map $ λ⟨o, n⟩, (o.local_uniq_name, n)),
  ((), pr) ← solve_aux cases (repeat $ exact h_fst_case <|> left >> skip),

  t ← target,
  fixed_vars ← vars.mmap update_type,
  let t' := (instantiate_local h_cases.local_uniq_name pr t).pis (fixed_vars ++ [h_fst_case]),

  (h, [g]) ← local_proof `this t' (do
    clear h_cases,
    vars.mmap clear,
    intron nr),

  h₀ :: hs ← elim_or perms.length h_cases,

  solve1 (do
    exact (h.mk_app $ vars ++ [h₀])),

  focus ((hs.zip perms.tail).map $ λ⟨h_case, perm⟩, do
    let p_v := (vars'.zip vars).map (λ⟨p, v⟩, (p.local_uniq_name, v)),
    let p := perm.map (λp, p.instantiate_locals p_v),
    note `this none (h.mk_app $ p ++ [h_case]),
    clear h,
    return ()),
  gs ← get_goals,
  set_goals (g :: gs)

namespace interactive
open interactive interactive.types expr

private meta def parse_permutations : option (list (list name)) → tactic (list (list expr))
| none                    := return []
| (some [])               := return []
| (some perms@(p₀ :: ps)) := do
  (guard p₀.nodup <|> fail
    "No permutation `xs_i` in `using [xs_1, …, xs_n]` should contain the same variable twice."),
  (guard (perms.all $ λp, p.perm p₀) <|>
    fail ("The permutations `xs_i` in `using [xs_1, …, xs_n]` must be permutations of the same" ++
      " variables.")),
  perms.mmap (λp, p.mmap get_local)

/-- Without loss of generality: reduces to one goal under variables permutations.

Given a goal of the form `g xs`, a predicate `p` over a set of variables, as well as variable
permutations `xs_i`. Then `wlog` produces goals of the form

The case goal, i.e. the permutation `xs_i` covers all possible cases:
  `⊢ p xs_0 ∨ ⋯ ∨ p xs_n`
The main goal, i.e. the goal reduced to `xs_0`:
  `(h : p xs_0) ⊢ g xs_0`
The invariant goals, i.e. `g` is invariant under `xs_i`:
  `(h : p xs_i) (this : g xs_0) ⊢ gs xs_i`

Either the permutation is provided, or a proof of the disjunction is provided to compute the
permutation. The disjunction need to be in assoc normal form, e.g. `p₀ ∨ (p₁ ∨ p₂)`. In many cases
the invariant goals can be solved by AC rewriting using `cc` etc.

Example:
  On a state `(n m : ℕ) ⊢ p n m` the tactic `wlog h : n ≤ m using [n m, m n]` produces the following
  states:
    `(n m : ℕ) ⊢ n ≤ m ∨ m ≤ n`
    `(n m : ℕ) (h : n ≤ m) ⊢ p n m`
    `(n m : ℕ) (h : m ≤ n) (this : p n m) ⊢ p m n`

`wlog` supports different calling conventions. The name `h` is used to give a name to the introduced
case hypothesis. If the name is avoided, the default will be `case`.

(1) `wlog : p xs0 using [xs0, …, xsn]`
  Results in the case goal `p xs0 ∨ ⋯ ∨ ps xsn`, the main goal `(case : p xs0) ⊢ g xs0` and the
  invariance goals `(case : p xsi) (this : g xs0) ⊢ g xsi`.

(2) `wlog : p xs0 := r using xs0`
  The expression `r` is a proof of the shape `p xs0 ∨ ⋯ ∨ p xsi`, it is also used to compute the
  variable permutations.

(3) `wlog := r using xs0`
  The expression `r` is a proof of the shape `p xs0 ∨ ⋯ ∨ p xsi`, it is also used to compute the
  variable permutations. This is not as stable as (2), for example `p` cannot be a disjunction.

(4) `wlog : R x y using x y` and `wlog : R x y`
  Produces the case `R x y ∨ R y x`. If `R` is ≤, then the disjunction discharged using linearity.
  If `using x y` is avoided then `x` and `y` are the last two variables appearing in the
  expression `R x y`. -/
meta def wlog
  (h : parse ident?)
  (pat : parse (tk ":" *> texpr)?)
  (cases : parse (tk ":=" *> texpr)?)
  (perms : parse (tk "using" *> (list_of (ident*) <|> (λx, [x]) <$> ident*))?)
  (discharger : tactic unit :=
    (tactic.solve_by_elim <|> tactic.tautology {classical := tt} <|>
      using_smt (smt_tactic.intros >> smt_tactic.solve_goals))) :
  tactic unit := do
perms ← parse_permutations perms,
(pat, cases_pr, cases_goal, vars, perms) ← (match cases with
| some r := do
  vars::_ ← return perms |
    fail "At least one set of variables expected, i.e. `using x y` or `using [x y, y x]`.",
  cases_pr ← to_expr r,
  cases_pr ← (if cases_pr.is_local_constant
    then return $ match h with some n := update_pp_name cases_pr n | none := cases_pr end
    else do
      note (h.get_or_else `case) none cases_pr),
  cases ← infer_type cases_pr,
  (pat, perms') ← match pat with
  | some pat := do
    pat ← to_expr pat,
    let vars' := vars.filter $ λv, v.occurs pat,
    case_pat ← mk_pattern [] vars' pat [] vars',
    perms' ← match_perms case_pat cases,
    return (pat, perms')
  | none := do
    (p :: ps) ← dest_or cases,
    let vars' := vars.filter $ λv, v.occurs p,
    case_pat ← mk_pattern [] vars' p [] vars',
    perms' ← (p :: ps).mmap (λp, do m ← match_pattern case_pat p, return m.2),
    return (p, perms')
  end,
  let vars_name := vars.map local_uniq_name,
  guard (perms'.all $ λp, p.all $ λv, v.is_local_constant ∧ v.local_uniq_name ∈ vars_name) <|>
    fail "Cases contains variables not declared in `using x y z`",
  perms ← (if perms.length = 1
    then do
      return (perms'.map $ λ p,
        p ++ vars.filter (λ v, p.all (λ v', v'.local_uniq_name ≠ v.local_uniq_name)))
    else do
      guard (perms.length = perms'.length) <|>
        fail "The provided permutation list has a different length then the provided cases.",
      return perms),
  return (pat, cases_pr, @none expr, vars, perms)

| none   := do
  let name_h := h.get_or_else `case,
  some pat ← return pat | fail "Either specify cases or a pattern with permutations",
  pat ← to_expr pat,
  (do
    [x, y] ← match perms with
    | []  := return pat.list_local_consts
    | [l] := return l
    | _   := failed
    end,
    let cases := mk_or_lst
      [pat, pat.instantiate_locals [(x.local_uniq_name, y), (y.local_uniq_name, x)]],
    (do
      `(%%x' ≤ %%y') ← return pat,
      (cases_pr, []) ← local_proof name_h cases (exact ``(le_total %%x' %%y')),
      return (pat, cases_pr, none, [x, y], [[x, y], [y, x]]))
    <|>
    (do
      (cases_pr, [g]) ← local_proof name_h cases skip,
      return (pat, cases_pr, some g, [x, y], [[x, y], [y, x]]))) <|>
  (do
    guard (perms.length ≥ 2) <|>
      fail ("To generate cases at least two permutations are required, i.e. `using [x y, y x]`" ++
        " or exactly 0 or 2 variables"),
    (vars :: perms') ← return perms,
    let names := vars.map local_uniq_name,
    let cases := mk_or_lst (pat :: perms'.map (λp, pat.instantiate_locals (names.zip p))),
    (cases_pr, [g]) ← local_proof name_h cases skip,
    return (pat, cases_pr, some g, vars, perms))
end),
let name_fn := if perms.length = 2 then λ _, `invariant else
  λ i, mk_simple_name ("invariant_" ++ to_string (i + 1)),
with_enable_tags $ tactic.focus1 $ do
  t ← get_main_tag,
  tactic.wlog vars cases_pr pat perms,
  tactic.focus (set_main_tag (mk_num_name `_case 0 :: `main :: t) ::
    (list.range (perms.length - 1)).map (λi, do
      set_main_tag (mk_num_name `_case 0 :: name_fn i :: t),
      try discharger)),
  match cases_goal with
  | some g := do
    set_tag g (mk_num_name `_case 0 :: `cases :: t),
    gs ← get_goals,
    set_goals (g :: gs)
  | none := skip
  end

add_tactic_doc
{ name := "wlog",
  category := doc_category.tactic,
  decl_names := [``wlog],
  tags := ["logic"] }

end interactive

end tactic
