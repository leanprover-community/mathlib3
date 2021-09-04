/-
Copyright (c) 2019 Lucas Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucas Allen, Scott Morrison
-/
import data.mllist
import tactic.solve_by_elim

/-!
# `suggest` and `library_search`

`suggest` and `library_search` are a pair of tactics for applying lemmas from the library to the
current goal.

* `suggest` prints a list of `exact ...` or `refine ...` statements, which may produce new goals
* `library_search` prints a single `exact ...` which closes the goal, or fails
-/

namespace tactic

open native

namespace suggest

open solve_by_elim

/-- Map a name (typically a head symbol) to a "canonical" definitional synonym.
Given a name `n`, we want a name `n'` such that a sufficiently applied
expression with head symbol `n` is always definitionally equal to an expression
with head symbol `n'`.
Thus, we can search through all lemmas with a result type of `n'`
to solve a goal with head symbol `n`.

For example, `>` is mapped to `<` because `a > b` is definitionally equal to `b < a`,
and `not` is mapped to `false` because `¬ a` is definitionally equal to `p → false`
The default is that the original argument is returned, so `<` is just mapped to `<`.

`normalize_synonym` is called for every lemma in the library, so it needs to be fast.
-/
-- TODO this is a hack; if you suspect more cases here would help, please report them
meta def normalize_synonym : name → name
| `gt := `has_lt.lt
| `ge := `has_le.le
| `monotone := `has_le.le
| `not := `false
| n   := n

/--
Compute the head symbol of an expression, then normalise synonyms.

This is only used when analysing the goal, so it is okay to do more expensive analysis here.
-/
-- We may want to tweak this further?
meta def allowed_head_symbols : expr → list name
-- We first have a various "customisations":
--   Because in `ℕ` `a.succ ≤ b` is definitionally `a < b`,
--   we add some special cases to allow looking for `<` lemmas even when the goal has a `≤`.
--   Note we only do this in the `ℕ` case, for performance.
| `(@has_le.le ℕ _ (nat.succ _) _) := [`has_le.le, `has_lt.lt]
| `(@ge ℕ _ _ (nat.succ _)) := [`has_le.le, `has_lt.lt]
| `(@has_le.le ℕ _ 1 _) := [`has_le.le, `has_lt.lt]
| `(@ge ℕ _ _ 1) := [`has_le.le, `has_lt.lt]

-- And then the generic cases:
| (expr.pi _ _ _ t) := allowed_head_symbols t
| (expr.app f _) := allowed_head_symbols f
| (expr.const n _) := [normalize_synonym n]
| _ := [`_]
.

/--
A declaration can match the head symbol of the current goal in four possible ways:
* `ex`  : an exact match
* `mp`  : the declaration returns an `iff`, and the right hand side matches the goal
* `mpr` : the declaration returns an `iff`, and the left hand side matches the goal
* `both`: the declaration returns an `iff`, and the both sides match the goal
-/
@[derive decidable_eq, derive inhabited]
inductive head_symbol_match
| ex | mp | mpr | both

open head_symbol_match

/-- a textual representation of a `head_symbol_match`, for trace debugging. -/
def head_symbol_match.to_string : head_symbol_match → string
| ex   := "exact"
| mp   := "iff.mp"
| mpr  := "iff.mpr"
| both := "iff.mp and iff.mpr"

/-- Determine if, and in which way, a given expression matches the specified head symbol. -/
meta def match_head_symbol (hs : name_set) : expr → option head_symbol_match
| (expr.pi _ _ _ t) := match_head_symbol t
| `(%%a ↔ %%b)      := if hs.contains `iff then some ex else
                       match (match_head_symbol a, match_head_symbol b) with
                       | (some ex, some ex) :=
                           some both
                       | (some ex, _) := some mpr
                       | (_, some ex) := some mp
                       | _ := none
                       end
| (expr.app f _)    := match_head_symbol f
| (expr.const n _)  := if hs.contains (normalize_synonym n) then some ex else none
| _ := if hs.contains `_ then some ex else none

/-- A package of `declaration` metadata, including the way in which its type matches the head symbol
which we are searching for. -/
meta structure decl_data :=
(d : declaration)
(n : name)
(m : head_symbol_match)
(l : ℕ) -- cached length of name

/--
Generate a `decl_data` from the given declaration if
it matches the head symbol `hs` for the current goal.
-/
-- We used to check here for private declarations, or declarations with certain suffixes.
-- It turns out `apply` is so fast, it's better to just try them all.
meta def process_declaration (hs : name_set) (d : declaration) : option decl_data :=
let n := d.to_name in
if !d.is_trusted || n.is_internal then
  none
else
  (λ m, ⟨d, n, m, n.length⟩) <$> match_head_symbol hs d.type

/-- Retrieve all library definitions with a given head symbol. -/
meta def library_defs (hs : name_set) : tactic (list decl_data) :=
do trace_if_enabled `suggest format!"Looking for lemmas with head symbols {hs}.",
   env ← get_env,
   let defs := env.decl_filter_map (process_declaration hs),
   -- Sort by length; people like short proofs
   let defs := defs.qsort(λ d₁ d₂, d₁.l ≤ d₂.l),
   trace_if_enabled `suggest format!"Found {defs.length} relevant lemmas:",
   trace_if_enabled `suggest $ defs.map (λ ⟨d, n, m, l⟩, (n, m.to_string)),
   return defs

/--
We unpack any element of a list of `decl_data` corresponding to an `↔` statement that could apply
in both directions into two separate elements.

This ensures that both directions can be independently returned by `suggest`,
and avoids a problem where the application of one direction prevents
the application of the other direction. (See `exp_le_exp` in the tests.)
-/
meta def unpack_iff_both : list decl_data → list decl_data
| []                     := []
| (⟨d, n, both, l⟩ :: L) := ⟨d, n, mp, l⟩ :: ⟨d, n, mpr, l⟩ :: unpack_iff_both L
| (⟨d, n, m, l⟩ :: L)    := ⟨d, n, m, l⟩ :: unpack_iff_both L

/-- An extension to the option structure for `solve_by_elim`,
to specify a list of local hypotheses which must appear in any solution.
These are useful for constraining the results from `library_search` and `suggest`. -/
meta structure suggest_opt extends opt :=
(compulsory_hyps : list expr := [])

/--
Convert a `suggest_opt` structure to a `opt` structure suitable for `solve_by_elim`,
by setting the `accept` parameter to require that all complete solutions
use everything in `compulsory_hyps`.
-/
meta def suggest_opt.mk_accept (o : suggest_opt) : opt :=
{ accept := λ gs, o.accept gs >>
    (guard $ o.compulsory_hyps.all (λ h, gs.any (λ g, g.contains_expr_or_mvar h))),
  ..o }

/--
Apply the lemma `e`, then attempt to close all goals using
`solve_by_elim opt`, failing if `close_goals = tt`
and there are any goals remaining.

Returns the number of subgoals which were closed using `solve_by_elim`.
-/
-- Implementation note: as this is used by both `library_search` and `suggest`,
-- we first run `solve_by_elim` separately on the independent goals,
-- whether or not `close_goals` is set,
-- and then run `solve_by_elim { all_goals := tt }`,
-- requiring that it succeeds if `close_goals = tt`.
meta def apply_and_solve (close_goals : bool) (opt : suggest_opt := { }) (e : expr) : tactic ℕ :=
do
  trace_if_enabled `suggest format!"Trying to apply lemma: {e}",
  apply e opt.to_apply_cfg,
  trace_if_enabled `suggest format!"Applied lemma: {e}",
  ng ← num_goals,
  -- Phase 1
  -- Run `solve_by_elim` on each "safe" goal separately, not worrying about failures.
  -- (We only attempt the "safe" goals in this way in Phase 1.
  -- In Phase 2 we will do backtracking search across all goals,
  -- allowing us to guess solutions that involve data or unify metavariables,
  -- but only as long as we can finish all goals.)
  -- If `compulsory_hyps` is non-empty, we skip this phase and defer to phase 2.
  try (guard (opt.compulsory_hyps = []) >>
    any_goals (independent_goal >> solve_by_elim opt.to_opt)),
  -- Phase 2
  (done >> return ng) <|> (do
    -- If there were any goals that we did not attempt solving in the first phase
    -- (because they weren't propositional, or contained a metavariable)
    -- as a second phase we attempt to solve all remaining goals at once
    -- (with backtracking across goals).
    ((guard (opt.compulsory_hyps ≠ []) <|> any_goals (success_if_fail independent_goal) >> skip) >>
      solve_by_elim { backtrack_all_goals := tt, ..opt.mk_accept }) <|>
    -- and fail unless `close_goals = ff`
    guard ¬ close_goals,
    ng' ← num_goals,
    return (ng - ng'))

/--
Apply the declaration `d` (or the forward and backward implications separately, if it is an `iff`),
and then attempt to solve the subgoal using `apply_and_solve`.

Returns the number of subgoals successfully closed.
-/
meta def apply_declaration (close_goals : bool) (opt : suggest_opt := { }) (d : decl_data) :
  tactic ℕ :=
let tac := apply_and_solve close_goals opt in
do (e, t) ← decl_mk_const d.d,
   match d.m with
   | ex   := tac e
   | mp   := do l ← iff_mp_core e t, tac l
   | mpr  := do l ← iff_mpr_core e t, tac l
   | both := undefined -- we use `unpack_iff_both` to ensure this isn't reachable
   end

/-- An `application` records the result of a successful application of a library lemma. -/
meta structure application :=
(state     : tactic_state)
(script    : string)
(decl      : option declaration)
(num_goals : ℕ)
(hyps_used : list expr)

end suggest

open solve_by_elim
open suggest

declare_trace suggest         -- Trace a list of all relevant lemmas

-- Call `apply_declaration`, then prepare the tactic script and
-- count the number of local hypotheses used.
private meta def apply_declaration_script
  (g : expr) (hyps : list expr)
  (opt : suggest_opt := { })
  (d : decl_data) :
  tactic application :=
-- (This tactic block is only executed when we evaluate the mllist,
-- so we need to do the `focus1` here.)
retrieve $ focus1 $ do
  apply_declaration ff opt d,
  -- This `instantiate_mvars` is necessary so that we count used hypotheses correctly.
  g ← instantiate_mvars g,
  guard $ (opt.compulsory_hyps.all (λ h, h.occurs g)),
  ng ← num_goals,
  s ← read,
  m ← tactic_statement g,
  return
  { application .
    state := s,
    decl := d.d,
    script := m,
    num_goals := ng,
    hyps_used := hyps.filter (λ h, h.occurs g) }

-- implementation note: we produce a `tactic (mllist tactic application)` first,
-- because it's easier to work in the tactic monad, but in a moment we squash this
-- down to an `mllist tactic application`.
private meta def suggest_core' (opt : suggest_opt := { }) :
  tactic (mllist tactic application) :=
do g :: _ ← get_goals,
   hyps ← local_context,

   -- Check if `solve_by_elim` can solve the goal immediately:
   (retrieve (do
     focus1 $ solve_by_elim opt.mk_accept,
     s ← read,
     m ← tactic_statement g,
     -- This `instantiate_mvars` is necessary so that we count used hypotheses correctly.
     g ← instantiate_mvars g,
     guard (opt.compulsory_hyps.all (λ h, h.occurs g)),
     return $ mllist.of_list [⟨s, m, none, 0, hyps.filter (λ h, h.occurs g)⟩])) <|>
   -- Otherwise, let's actually try applying library lemmas.
   (do
   -- Collect all definitions with the correct head symbol
   t ← infer_type g,
   defs ← unpack_iff_both <$> library_defs (name_set.of_list $ allowed_head_symbols t),

   let defs : mllist tactic _ := mllist.of_list defs,

   -- Try applying each lemma against the goal,
   -- recording the tactic script as a string,
   -- the number of remaining goals,
   -- and number of local hypotheses used.
   let results := defs.mfilter_map (apply_declaration_script g hyps opt),
   -- Now call `symmetry` and try again.
   -- (Because we are using `mllist`, this is essentially free if we've already found a lemma.)
   symm_state ← retrieve $ try_core $ symmetry >> read,
   let results_symm := match symm_state with
   | (some s) :=
     defs.mfilter_map (λ d, retrieve $ set_state s >> apply_declaration_script g hyps opt d)
   | none := mllist.nil
   end,
  return (results.append results_symm))

/--
The core `suggest` tactic.
It attempts to apply a declaration from the library,
then solve new goals using `solve_by_elim`.

It returns a list of `application`s consisting of fields:
* `state`, a tactic state resulting from the successful application of a declaration from
  the library,
* `script`, a string of the form `Try this: refine ...` or `Try this: exact ...` which will
  reproduce that tactic state,
* `decl`, an `option declaration` indicating the declaration that was applied
  (or none, if `solve_by_elim` succeeded),
* `num_goals`, the number of remaining goals, and
* `hyps_used`, the number of local hypotheses used in the solution.
-/
meta def suggest_core (opt : suggest_opt := { }) : mllist tactic application :=
(mllist.monad_lift (suggest_core' opt)).join

/--
See `suggest_core`.

Returns a list of at most `limit` `application`s,
sorted by number of goals, and then (reverse) number of hypotheses used.
-/
meta def suggest (limit : option ℕ := none) (opt : suggest_opt := { }) :
  tactic (list application) :=
do let results := suggest_core opt,
   -- Get the first n elements of the successful lemmas
   L ← if h : limit.is_some then results.take (option.get h) else results.force,
   -- Sort by number of remaining goals, then by number of hypotheses used.
   return $ L.qsort (λ d₁ d₂, d₁.num_goals < d₂.num_goals ∨
    (d₁.num_goals = d₂.num_goals ∧ d₁.hyps_used.length ≥ d₂.hyps_used.length))

/--
Returns a list of at most `limit` strings, of the form `Try this: exact ...` or
`Try this: refine ...`, which make progress on the current goal using a declaration
from the library.
-/
meta def suggest_scripts
  (limit : option ℕ := none) (opt : suggest_opt := { }) :
  tactic (list string) :=
do L ← suggest limit opt,
   return $ L.map application.script

/--
Returns a string of the form `Try this: exact ...`, which closes the current goal.
-/
meta def library_search (opt : suggest_opt := { }) : tactic string :=
(suggest_core opt).mfirst (λ a, do
  guard (a.num_goals = 0),
  write a.state,
  return a.script)

namespace interactive
open tactic
open interactive
open lean.parser
open interactive.types
open solve_by_elim
local postfix `?`:9001 := optional

declare_trace silence_suggest -- Turn off `Try this: exact/refine ...` trace messages for `suggest`

/--
`suggest` tries to apply suitable theorems/defs from the library, and generates
a list of `exact ...` or `refine ...` scripts that could be used at this step.
It leaves the tactic state unchanged. It is intended as a complement of the search
function in your editor, the `#find` tactic, and `library_search`.

`suggest` takes an optional natural number `num` as input and returns the first `num`
(or less, if all possibilities are exhausted) possibilities ordered by length of lemma names.
The default for `num` is `50`.
For performance reasons `suggest` uses monadic lazy lists (`mllist`). This means that
`suggest` might miss some results if `num` is not large enough. However, because
`suggest` uses monadic lazy lists, smaller values of `num` run faster than larger values.

You can add additional lemmas to be used along with local hypotheses
after the application of a library lemma,
using the same syntax as for `solve_by_elim`, e.g.
```
example {a b c d: nat} (h₁ : a < c) (h₂ : b < d) : max (c + d) (a + b) = (c + d) :=
begin
  suggest [add_lt_add], -- Says: `Try this: exact max_eq_left_of_lt (add_lt_add h₁ h₂)`
end
```
You can also use `suggest with attr` to include all lemmas with the attribute `attr`.
-/
meta def suggest (n : parse (with_desc "n" small_nat)?)
  (hs : parse simp_arg_list) (attr_names : parse with_ident_list)
  (use : parse $ (tk "using" *> many ident_) <|> return []) (opt : opt := { }) :
  tactic unit :=
do (lemma_thunks, ctx_thunk) ← mk_assumption_set ff hs attr_names,
   use ← use.mmap get_local,
   L ← tactic.suggest_scripts (n.get_or_else 50)
     { compulsory_hyps := use,
       lemma_thunks := some lemma_thunks,
       ctx_thunk := ctx_thunk, ..opt },
  if is_trace_enabled_for `silence_suggest then
    skip
  else
    if L.length = 0 then
      fail "There are no applicable declarations"
    else
      L.mmap trace >> skip

/--
`suggest` lists possible usages of the `refine` tactic and leaves the tactic state unchanged.
It is intended as a complement of the search function in your editor, the `#find` tactic, and
`library_search`.

`suggest` takes an optional natural number `num` as input and returns the first `num` (or less, if
all possibilities are exhausted) possibilities ordered by length of lemma names.
The default for `num` is `50`.

`suggest using h₁ h₂` will only show solutions that make use of the local hypotheses `h₁` and `h₂`.

For performance reasons `suggest` uses monadic lazy lists (`mllist`). This means that `suggest`
might miss some results if `num` is not large enough. However, because `suggest` uses monadic
lazy lists, smaller values of `num` run faster than larger values.

An example of `suggest` in action,

```lean
example (n : nat) : n < n + 1 :=
begin suggest, sorry end
```

prints the list,

```lean
Try this: exact nat.lt.base n
Try this: exact nat.lt_succ_self n
Try this: refine not_le.mp _
Try this: refine gt_iff_lt.mp _
Try this: refine nat.lt.step _
Try this: refine lt_of_not_ge _
...
```
-/
add_tactic_doc
{ name        := "suggest",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.suggest],
  tags        := ["search", "Try this"] }

-- Turn off `Try this: exact ...` trace message for `library_search`
declare_trace silence_library_search

/--
`library_search` is a tactic to identify existing lemmas in the library. It tries to close the
current goal by applying a lemma from the library, then discharging any new goals using
`solve_by_elim`.

If it succeeds, it prints a trace message `exact ...` which can replace the invocation
of `library_search`.

Typical usage is:
```lean
example (n m k : ℕ) : n * (m - k) = n * m - n * k :=
by library_search -- Try this: exact nat.mul_sub_left_distrib n m k
```

`library_search using h₁ h₂` will only show solutions
that make use of the local hypotheses `h₁` and `h₂`.

By default `library_search` only unfolds `reducible` definitions
when attempting to match lemmas against the goal.
Previously, it would unfold most definitions, sometimes giving surprising answers, or slow answers.
The old behaviour is still available via `library_search!`.

You can add additional lemmas to be used along with local hypotheses
after the application of a library lemma,
using the same syntax as for `solve_by_elim`, e.g.
```
example {a b c d: nat} (h₁ : a < c) (h₂ : b < d) : max (c + d) (a + b) = (c + d) :=
begin
  library_search [add_lt_add], -- Says: `Try this: exact max_eq_left_of_lt (add_lt_add h₁ h₂)`
end
```
You can also use `library_search with attr` to include all lemmas with the attribute `attr`.
-/
meta def library_search (semireducible : parse $ optional (tk "!"))
  (hs : parse simp_arg_list) (attr_names : parse with_ident_list)
  (use : parse $ (tk "using" *> many ident_) <|> return [])
  (opt : opt := { }) : tactic unit :=
do (lemma_thunks, ctx_thunk) ← mk_assumption_set ff hs attr_names,
   use ← use.mmap get_local,
   (tactic.library_search
     { compulsory_hyps := use,
       backtrack_all_goals := tt,
       lemma_thunks := some lemma_thunks,
       ctx_thunk := ctx_thunk,
       md := if semireducible.is_some then
         tactic.transparency.semireducible else tactic.transparency.reducible,
       ..opt } >>=
   if is_trace_enabled_for `silence_library_search then
     (λ _, skip)
   else
     trace) <|>
   fail
"`library_search` failed.
If you aren't sure what to do next, you can also
try `library_search!`, `suggest`, or `hint`.

Possible reasons why `library_search` failed:
* `library_search` will only apply a single lemma from the library,
  and then try to fill in its hypotheses from local hypotheses.
* If you haven't already, try stating the theorem you want in its own lemma.
* Sometimes the library has one version of a lemma
  but not a very similar version obtained by permuting arguments.
  Try replacing `a + b` with `b + a`, or `a - b < c` with `a < b + c`,
  to see if maybe the lemma exists but isn't stated quite the way you would like.
* Make sure that you have all the side conditions for your theorem to be true.
  For example you won't find `a - b + b = a` for natural numbers in the library because it's false!
  Search for `b ≤ a → a - b + b = a` instead.
* If a definition you made is in the goal,
  you won't find any theorems about it in the library.
  Try unfolding the definition using `unfold my_definition`.
* If all else fails, ask on https://leanprover.zulipchat.com/,
  and maybe we can improve the library and/or `library_search` for next time."

add_tactic_doc
{ name        := "library_search",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.library_search],
  tags        := ["search", "Try this"] }

end interactive

/-- Invoking the hole command `library_search` ("Use `library_search` to complete the goal") calls
the tactic `library_search` to produce a proof term with the type of the hole.

Running it on

```lean
example : 0 < 1 :=
{!!}
```

produces

```lean
example : 0 < 1 :=
nat.one_pos
```
-/
@[hole_command] meta def library_search_hole_cmd : hole_command :=
{ name := "library_search",
  descr := "Use `library_search` to complete the goal.",
  action := λ _, do
    script ← library_search,
    -- Is there a better API for dropping the 'Try this: exact ' prefix on this string?
    return [((script.get_rest "Try this: exact ").get_or_else script, "by library_search")] }

add_tactic_doc
{ name        := "library_search",
  category    := doc_category.hole_cmd,
  decl_names  := [`tactic.library_search_hole_cmd],
  tags        := ["search", "Try this"] }

end tactic
