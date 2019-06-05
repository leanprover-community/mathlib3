-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Keeley Hoek

import tactic.basic
import data.list.defs
import data.option.basic
import order.lexicographic

namespace tactic
open native

local attribute [instance] lex_decidable_linear_order

-- Just a check that we're actually using lexicographic ordering here.
example : (5,10) ≤ (10,3) := by exact dec_trivial

namespace back

meta def head_symbol : expr → name
| (expr.pi _ _ _ t) := head_symbol t
| (expr.app f _) := head_symbol f
| (expr.const n _) :=
  match n with
  | `gt := `has_lt.lt
  | `ge := `has_le.le
  | _ := n
  end
| _ := `_

meta def head_symbols : expr → list name
| (expr.pi _ _ _ t) := head_symbols t
| `(%%a ↔ %%b)      := `iff :: head_symbols a ++ head_symbols b
| (expr.app f _)    := head_symbols f
| `(not)            := [`not, `false]
| (expr.const n _)  :=
  match n with
  | `not        := [`not, `false]
  | `gt         := [`has_lt.lt]
  | `ge         := [`has_le.le]
  | `has_lt.lt  := [`has_lt.lt, `has_le.le]
  | _           := [n]
  end
| _                 := [`_]

-- example : true :=
-- begin
--   lock_tactic_state $ (do e ← to_expr ``(nat.lt_of_le_of_lt) >>= infer_type, trace (head_symbols e)),
--   lock_tactic_state $ (do e ← to_expr ``(lt_of_le_of_lt)     >>= infer_type, trace (head_symbols e)),
--   lock_tactic_state $ (do e ← to_expr ``(nat.zero_le)        >>= infer_type, trace (head_symbols e)),

--   trivial
-- end

-- example : true :=
-- begin
--   (do e ← to_expr ``(nat.dvd_add_iff_left) >>= infer_type, trace $ head_symbol e),
--   (do e ← to_expr ``(list.forall_mem_inter_of_forall_left) >>= infer_type, trace $ head_symbol e),
--   (do e ← to_expr ``(nat.dvd_add_iff_left) >>= infer_type, trace $ symbols e),
--   (do e ← to_expr ``(@list.forall_mem_inter_of_forall_left) >>= infer_type, trace $ symbols e),

--   trivial
-- end

@[user_attribute]
meta def back_attribute : user_attribute (rb_map name (list name)) (option unit) := {
  name := `back,
  descr :=
"A lemma that should be applied to a goal whenever possible;
use the tactic `back` to automatically `apply` all lemmas tagged `[back]`.
Lemmas tagged with `[back!]` will be applied even if the
resulting subgoals cannot all be discharged.",
  parser := optional $ lean.parser.tk "!",
  cache_cfg := -- TODO not actually being used
   { mk_cache := λ ls,
     do { ls.mfoldl (λ m dn,
            do d ← get_decl dn,
               pure $ (head_symbols d.type).foldl (λ m i, m.insert_cons i dn) m)
            (rb_map.mk _ _) },
     dependencies := [] }
}

meta structure back_lemma :=
(name         : string) -- oh dear!
(lem          : expr)
(ty           : expr)
/- a flag indicating that is we use this lemma, we must discharge resulting goals -/
(finishing    : bool)
/- a flag indicating that this lemma came from pulling in the whole library -/
(from_library : bool := ff)
-- (local_hyp    : bool)
(index        : ℕ)

meta def back_lemma.is_fact (l : back_lemma) : bool := ¬ expr.is_pi l.ty

-- We fake an instance here for convenience. Correctness is ensured by creating unique index values.
meta instance : decidable_eq back_lemma :=
λ a b, if a.index = b.index then is_true undefined else is_false undefined

@[derive decidable_eq]
inductive apply_step
| facts    -- We're working on lemmas with no hypotheses (likely all local hypotheses).
| relevant -- We're working on lemmas with the same head constant as the goal.
| others   -- We're getting desperate, and working on all remaining lemmas.

open apply_step

def apply_step.weight : apply_step → ℕ
| apply_step.facts := 1
| apply_step.relevant := 4
| apply_step.others := 5

-- An expr representing a goal, along with a list of lemmas which we have not yet tried
-- `apply`ing against that goal.
meta structure apply_state :=
(goal      : expr)
(goal_type : expr) -- We store this explicitly, rather than looking it up with `infer_type` as needed, because we're doing manual tactic_state management
(committed : bool) -- If the goal is not 'committed', we can stash it if we get stuck.
(step      : apply_step)
(lemmas    : list back_lemma)

meta structure back_state :=
(steps         : ℕ := 0)
(fact_steps    : ℕ := 0)
(library_steps : ℕ := 0)
(limit         : ℕ)
(library_limit : ℕ)
/- We carry the full list of lemmas along, as we may want to reorder or discard some.
-- (e.g. we don't use `iff` lemmas more than once, to avoid loops) -/
(facts     : list back_lemma) -- A `fact` is a lemma with no hypotheses; usually a local hypothesis
(lemmas    : list back_lemma) -- All other lemmas
(facts_map : rb_map name (list back_lemma))
(lemma_map : rb_map name (list back_lemma))
/- We carry along an internal `tactic_state`,
-- so metavariables aren't contaminated by other branches of the search. -/
(tactic_state : tactic_state)
(stashed      : list expr := {})   -- Stores goals which we're going to return to the user.
(completed    : list expr := {})   -- Stores completed goals.
(goals        : list apply_state)

meta def back_state.goal_counts (s : back_state) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
(
  (s.goals.filter(λ g : apply_state, g.step = facts    ∧ g.committed)).length,
  (s.goals.filter(λ g : apply_state, g.step = relevant ∧ g.committed)).length,
  (s.goals.filter(λ g : apply_state, g.step = others   ∧ g.committed)).length,
  (s.goals.filter(λ g : apply_state, g.step = facts    ∧ ¬ g.committed)).length,
  (s.goals.filter(λ g : apply_state, g.step = relevant ∧ ¬ g.committed)).length,
  (s.goals.filter(λ g : apply_state, g.step = others   ∧ ¬ g.committed)).length
)

meta instance : has_to_string back_state :=
{ to_string := λ s, to_string
  format!"back_state: ({s.stashed.length}/{s.completed.length}) ({s.goal_counts}) ({s.steps})" }

meta instance has_to_format_back_state : has_to_format back_state :=
{ to_format := λ s, to_string s }

meta instance has_to_tactic_format_back_state : has_to_tactic_format back_state :=
{ to_tactic_format := λ s,
    do return $ to_string s }

meta def back_state.done (s : back_state) : bool :=
s.goals.empty

-- TODO Think hard about what goes here; possibly allow customisation.
meta def back_state.default_complexity (s : back_state) : ℤ × ℕ × ℕ :=
-- It's essential to put `stashed` first, so that stashed goals are not returned until
-- we've exhausted other branches of the search tree.
-- (s.stashed.length, s.done, 2 * s.in_progress_fc.length + 2 * s.committed_fc.length + s.steps, s.steps + s.num_mvars) -- works!
-- (s.stashed.length, s.done, 16 * s.in_progress_fc.length + 16 * s.committed_fc.length + 4 * s.in_progress_new.length + 4 * s.committed_new.length + s.steps, s.steps + s.num_mvars)

(if s.stashed.length > 0 ∧ s.done then - (s.steps : ℤ) else 0, -- Think about this some more!
 -- Goals which haven't been fact-checked yet are cheap; goals which have been are more expensive.
 -- TODO explain why `steps` amd `fact_steps` are here.
 -- The particular weights used here are ... voodoo.
 4 * (list.foldl (+) 0 (s.goals.map (λ as : apply_state, as.step.weight))) + s.steps - s.fact_steps,
 0)
--  s.steps + (s.goals.countp $ λ g, g.goal_type.has_meta_var)) -- cache this?

meta def back_state.depth_first_complexity (s : back_state) : unit := ()

-- Count the number of arguments not determined by later arguments.
meta def count_arrows : expr → ℕ
| `(%%a <-> %%b)     := 1 + min (count_arrows a) (count_arrows b)
| (expr.pi n bi d b) :=
   if b.has_var_idx 0 then count_arrows b
                      else 1 + count_arrows b
| _                  := 0

meta def count_pis : expr → ℕ
| `(%%a <-> %%b)    := 1 + min (count_pis a) (count_pis b)
| (expr.pi _ _ _ b) := 1 + count_pis b
| _                 := 0

/-- Sorts a list of lemmas according to the number of explicit arguments
    (more precisely, arguments which are not determined by later arguments). -/
meta def sort_back_lemmas (L : list back_lemma) : list back_lemma :=
let M := L.map (λ e, ((count_arrows e.ty, count_pis e.ty, e.name.length), e)) in
(list.qsort (λ (p q : (ℕ × ℕ × ℕ) × back_lemma), p.1 ≤ q.1) M).map (λ p, p.2)

declare_trace back
declare_trace back_lemmas

meta def back_state.init (goals : list expr) (lemmas : list back_lemma) (limit library_limit : option ℕ) : tactic back_state :=
λ s, -- We'll need to grab a copy of the tactic state.
(do
   let (lemmas', facts') := lemmas.partition (λ p : back_lemma, expr.is_pi p.ty),

   let facts_map : rb_map name (list back_lemma) :=
     facts'.foldl (λ m l,
            (head_symbols l.ty).erase_dup.foldl (λ m i, m.insert_cons i l) m)
            (rb_map.mk _ _),
   let facts_map := facts_map.map sort_back_lemmas,

   let lemma_map : rb_map name (list back_lemma) :=
     lemmas'.foldl (λ m l,
            (head_symbols l.ty).erase_dup.foldl (λ m i, m.insert_cons i l) m)
            (rb_map.mk _ _),
   let lemma_map := lemma_map.map sort_back_lemmas,

   when (is_trace_enabled_for `back_lemmas) $ (do
     trace "initialising `back`...",
     trace "using facts:",
     trace $ facts'.map (λ f, (f.lem, (head_symbols f.ty).erase_dup)),
     trace "using lemmas:",
     trace $ lemmas'.map (λ f, (f.lem, (head_symbols f.ty).erase_dup))),

   initial_goals ← goals.mmap (λ goal, do goal_type ← infer_type goal, return
   { apply_state .
     goal      := goal,
     goal_type := goal_type,
     committed := ff,
     step      := apply_step.facts,
     lemmas    := (facts_map.find (head_symbol goal_type)).get_or_else [] }),

   return
   { back_state .
     limit         := limit.get_or_else 25,
     library_limit := library_limit.get_or_else 5,
     facts         := facts',
     lemmas        := lemmas',
     facts_map     := facts_map,
     lemma_map     := lemma_map,
     tactic_state  := s, -- We steal the current tactic state, and stash a copy inside.
     goals         := initial_goals }) s

-- keep only uninstantiable metavariables
meta def partition_mvars (L : list expr) : tactic (list expr × list expr) :=
(list.partition (λ e, e.is_meta_var)) <$>
  (L.mmap (λ e, instantiate_mvars e))

meta def partition_apply_state_mvars (L : list apply_state) : tactic (list apply_state × list apply_state) :=
(list.partition (λ as, as.goal.is_meta_var)) <$>
  (L.mmap (λ as, do e' ← instantiate_mvars as.goal, return { goal := e', ..as }))

/--
* Discard any goals which have already been solved,
* increment the `step` counter,
* and remove applied iffs.
-/
meta def back_state.clean (s : back_state) (g : expr) (last_lemma : back_lemma) : tactic back_state :=
do (stashed,     completed_1) ← partition_mvars s.stashed,
   (goals_new,   completed_2) ← partition_apply_state_mvars s.goals,
   let completed := s.completed ++ completed_1 ++ completed_2.map apply_state.goal,
   -- We don't apply `iff` lemmas more than once.
   lemmas ← (iff_mp last_lemma.lem >> pure (s.lemmas.erase last_lemma))
            <|> pure s.lemmas,
   return
   { back_state.
     steps         := s.steps + 1,
     fact_steps    := s.fact_steps + if last_lemma.is_fact then 1 else 0,
     library_steps := s.library_steps + if last_lemma.from_library then 1 else 0,
     stashed       := stashed,
     completed     := g :: completed,
     goals         := goals_new,
     lemmas        := lemmas,
     .. s }

-- Given a tactic that produces a new back_state, we can run that in the context
-- of a tactic_state contained within a back_state...
meta def back_state.run_on_bundled_state (s : back_state) {α : Type*} (tac : tactic (back_state × α)) : tactic (back_state × α) :=
λ ts,
  match tac s.tactic_state with
  | result.success s' sts' := result.success ({ tactic_state := sts', ..s'.1 }, s'.2) ts
  | result.exception msg pos sts' := result.exception msg pos ts
  end

meta def apply_state.insert_into (a : apply_state) : list apply_state → list apply_state
| [] := [a]
| (h :: t) :=
if a.step.weight ≤ h.step.weight then a :: h :: t else h :: (apply_state.insert_into t)

meta def back_state.add_goal (s : back_state) (as : apply_state) :=
{ goals := as.insert_into s.goals .. s }
meta def back_state.add_goals (s : back_state) (as : list apply_state) : back_state :=
as.foldl (λ s a, s.add_goal a) s

meta def back_state.apply_lemma (s : back_state) (g : expr) (e : back_lemma) (step : apply_step) (committed : bool) : tactic (back_state × bool) :=
s.run_on_bundled_state $
do set_goals [g],
   prop ← is_proof g,
   explicit ← (list.empty ∘ expr.list_meta_vars) <$> infer_type g,

   goal_types ← get_goals >>= λ gs, gs.mmap infer_type >>= pp,

    -- TODO get rid of apply_thorough; instead explicitly put the two directions of iff lemmas in the pool.
    /- We apply the lemma, and then eagerly discharge propositional subgoals not containing metavariables, using the facts.
       It's important we leave other subgoals for the outside machinery, so that we can back out of incorrect choices. -/
   seq (apply_thorough e.lem >> skip)
       ((do [g] ← get_goals,
          is_proof g >>= guardb,
          (list.empty ∘ expr.list_meta_vars) <$> infer_type g >>= guardb,
          s.facts.mfirst (λ f, exact f.lem)) <|> skip),

   when (is_trace_enabled_for `back) $ (do
    pp e.lem >>= λ l, trace $ format!"successfully applied {l} to goal {goal_types}",
    get_goals >>= λ gs, gs.mmap infer_type >>= pp >>= λ gs, trace format!"new goals: {gs}"),

   s' ← s.clean g e,
   (done >> return (s', prop ∧ explicit)) <|> do
   gs ← get_goals,
   types ← gs.mmap infer_type,
   /- `back` does not attempt to prove `false`; there are just too many directions you could go. -/
   success_if_fail $ types.mfirst $ λ t, unify t expr.mk_false,
   as ← gs.mmap $ λ g, (do
         t ← infer_type g,
         let relevant_facts := (s.facts_map.find (head_symbol t)).get_or_else [],
         return { apply_state . goal := g, goal_type := t, committed := e.finishing ∨ committed, step := apply_step.facts, lemmas := relevant_facts }),
   return (s'.add_goals as, ff)

meta def back_state.apply (s : back_state) : apply_state → tactic (list back_state)
| as :=
  match as.lemmas with
  | [] := fail "No lemmas applied to the current goal."
  | (h :: t) :=
    do r ← try_core $ s.apply_lemma as.goal h as.step as.committed,
       match r with
       | none := back_state.apply { lemmas := t, .. as }
       | (some (bs, prop_discharged)) :=
         do if prop_discharged then
              /- If we discharged a propositional goal, don't consider other ways to solve it! -/
              return [bs]
            else
              /- Otherwise, we branch; either continue with this application, or try the rest of
                 the lemmas instead. Because of the complexity sorting, trying facts and relevant
                 lemmas on the new state will have higher priority than trying other lemmas -/
              return [bs, s.add_goal { lemmas := t, .. as }]
       end
  end

meta def back_state.children (s : back_state) : tactic (list back_state) :=
match s.goals with
| [] := undefined
| (g :: gs) :=
  do let s' := { goals := gs, ..s },
     g_pp ← pp g.goal_type,
     s'.apply g <|>
     -- If no lemma from that step applied, we move on to the next step
     match (g.committed, g.step) with
     -- After trying to apply all the facts, we assemble the relevant lemmas and try those
     | (_, apply_step.facts)     :=
        do let relevant_lemmas := (s.lemma_map.find (head_symbol g.goal_type)).get_or_else [],
           return [s'.add_goal { lemmas := relevant_lemmas, step := apply_step.relevant, ..g }]
     -- After trying to apply all the relevant lemmas, we just try everything.
     | (_, apply_step.relevant)  :=
        do return [s'.add_goal { lemmas := [] /-s.lemmas-/, step := apply_step.others, ..g }] -- FIXME remove this entire step now?
     -- Finally, if we were committed, we now fail:
     | (tt, apply_step.others)   := return []
     -- But if we were not committed, we stash the goal:
     | (ff, apply_step.others)   := return (if s'.steps > 0 then [{ stashed := g.goal :: s'.stashed, .. s' }] else [])
     end
end

variables {α : Type} [decidable_linear_order α] (C : back_state → α)

private meta def complexity (s : back_state) : ℕ × ℕ × α :=
(-- We postpone back_states with stashed goals.
 s.stashed.length,
 -- But otherwise bring back_states with no remaining goals to the front.
 if s.done then 0 else 1,
 C s)

private meta def insert_new_state : back_state → list back_state → list back_state
| s (h :: t) := if complexity C s ≤ complexity C h then
                  s :: h :: t
                else
                  h :: (insert_new_state s t)
| s [] := [s]

-- An attempt to tweak the ordering...
-- | s (h₁ :: h₂ :: t) := if complexity C s < complexity C h₁ then
--                   s :: h₁ :: h₂ :: t
--                 else if complexity C s < complexity C h₂ then
--                   h₁ :: s :: h₂ :: t
--                 else
--                   h₁ :: (insert_new_state s (h₂ :: t))
-- | s [t] := if complexity C s < complexity C t then
--                   [s, t]
--                 else
--                   [t, s]
-- | s [] := [s]

private meta def insert_new_states : list back_state → list back_state → list back_state
| [] states := states
| (h :: t) states := insert_new_states t (insert_new_state C h states)

-- Either return a completed back_state, or an updated list.
private meta def run_one_step : list back_state → tactic (back_state ⊕ (list back_state))
| [] := failed
| (h :: t) :=
  if h.done then
    return $ sum.inl h
  else
    do if h.steps ≥ h.limit ∨ h.library_steps ≥ h.library_limit then
         return $ sum.inr t
       else do
         c ← h.children,
         return $ sum.inr $ insert_new_states C c t

private meta def run : list back_state → tactic back_state
| states :=
  do
     r ← run_one_step C states,
     match r with
     | (sum.inl success) := return success
     | (sum.inr states) := run states
     end

-- Whee! After selecting a successful back_state, we clobber the tactic_state with its
-- internal tactic_state; it's as if we got it right first try!
private meta def run' : list back_state → tactic back_state
| states :=
  λ ts, match run C states ts with
        | result.success bs ts' := result.success bs bs.tactic_state
        | result.exception msg pos ts' := result.exception msg pos ts'
        end

/--
`back` succeeds if at least one progress lemma was applied, or all goals are discharged.
  -/
meta def back (lemmas : list back_lemma) (limit library_limit : option ℕ := none) : tactic unit :=
do gs ← get_goals,
   i ← back_state.init gs lemmas limit library_limit,
   f ← run' C [i],
  --  set_goals gs,
   gs ← gs.mmap instantiate_mvars,
   set_goals ((gs.map expr.list_meta_vars).join),
   guard (f.steps > 0) -- Make sure some progress was made.

private meta def lookup_tagged_lemma (n : name) : tactic (bool × expr) :=
do is_elim ← back_attribute.get_param n,
   e ← mk_const n,
   return (is_elim.is_none, e)

private meta def collect_tagged_lemmas : list name → tactic (list expr × list expr)
| [] := return ([], [])
| (n :: rest) := do (normals, elims) ← collect_tagged_lemmas rest,
                    (is_elim, e) ← lookup_tagged_lemma n,
                    return $ if is_elim then (normals, e :: elims) else (e :: normals, elims)

open lean lean.parser expr interactive.types

-- `back_arg_type`, and associated definitions, are a close imitation of `simp_arg_type` from core.

@[derive has_reflect]
meta inductive back_arg_type : Type
| all_hyps : back_arg_type
| except   : name  → back_arg_type
| back     : pexpr → back_arg_type
| elim     : pexpr → back_arg_type

meta def back_arg : parser back_arg_type :=
(tk "*" *> return back_arg_type.all_hyps)
<|> (tk "-" *> back_arg_type.except <$> ident)
<|> (tk "!" *> (back_arg_type.back <$> texpr))
<|> (back_arg_type.elim <$> texpr)

meta def back_arg_list : parser (list back_arg_type) :=
(tk "*" *> return [back_arg_type.all_hyps]) <|> list_of back_arg <|> return []

local postfix *:9001 := many

meta def with_back_ident_list : parser (list (name × bool)) :=
(tk "with" *> (((λ n, (n, ff)) <$> ident_) <|> (tk "!" *> (λ n, (n, tt)) <$> ident))*) <|> return []

private meta def resolve_exception_ids (all_hyps : bool) :
  list name → list name → list name → tactic (list name × list name)
| []        gex hex := return (gex.reverse, hex.reverse)
| (id::ids) gex hex := do
  p ← resolve_name id,
  let e := p.erase_annotations.get_app_fn.erase_annotations,
  match e with
  | const n _           := resolve_exception_ids ids (n::gex) hex
  | local_const n _ _ _ := when (not all_hyps) (fail $ sformat! "invalid local exception {id}, '*' was not used") >>
                           resolve_exception_ids ids gex (n::hex)
  | _                   := fail $ sformat! "invalid exception {id}, unknown identifier"
  end

/- Return (pr, fi, gex, hex, all) -/
meta def decode_back_arg_list (hs : list back_arg_type) :
  tactic $ list pexpr × list pexpr × list name × list name × bool :=
do
  let (pr, fi, ex, all) := hs.foldl
    (λ r h,
       match r, h with
       | (ps, fs, ex, all), back_arg_type.all_hyps  := (ps, fs, ex, tt)
       | (ps, fs, ex, all), back_arg_type.except id := (ps, fs, id::ex, all)
       | (ps, fs, ex, all), back_arg_type.elim f    := (ps, f::fs, ex, all)
       | (ps, fs, ex, all), back_arg_type.back p    := (p::ps, fs, ex, all)
       end)
    ([], [], [], ff),
  (gex, hex) ← resolve_exception_ids all ex [] [],
  return (pr.reverse, fi.reverse, gex, hex, all)

-- TODO anything else?
meta def ignored_suffixes :=
["inj_arrow", "inj_eq",
 "rec", "drec", "cases_on", "dcases_on", "rec_on", "drec_on", "induction_on",
 "no_confusion", "no_confusion_type",
 "has_sizeof_inst", "sizeof", "has_sizeof", "sizeof_spec",
 "tfae_nil" -- This one is just unhelpful. TODO
]

meta def all_defs_except (gex : list name): tactic (list (name × expr × expr)) :=
do env ← get_env,
   let decls := env.get_trusted_decls,
   let decls := decls.filter $ λ d, let n := d.to_name in
     n ∉ gex ∧ ¬ n.is_internal ∧ ¬ n.is_private
       ∧ n.last ∉ ignored_suffixes,
   decls.mmap (λ d : declaration, do e ← mk_const d.to_name, return (d.to_name, e, d.type))

/--
Returns a list of "finishing lemmas" (which should only be applied as part of a
chain of applications which discharges the goal), and a list of "progress lemmas",
the successful application of any one of which counting as a success.
-/
--This is a close relative of `mk_assumption_set` in tactic/interactive.lean.
meta def mk_assumption_set (no_dflt : bool) (hs : list back_arg_type) (use : list (name × bool)) :
  tactic (list back_lemma) :=
do (extra_pr_lemmas, extra_fi_lemmas, gex, hex, all_hyps) ← decode_back_arg_list hs,
   /- `extra_lemmas` is explicitly requested lemmas
      `gex` are the excluded names
      `hex` are the excluded local hypotheses
      `all_hyps` means all hypotheses were included, via `*` -/
   extra_pr_lemmas ← extra_pr_lemmas.mmap i_to_expr_for_apply,
   extra_fi_lemmas ← extra_fi_lemmas.mmap i_to_expr_for_apply,
   (tagged_pr_lemmas, tagged_fi_lemmas) ← attribute.get_instances `back >>= collect_tagged_lemmas,

   let use_fi := (use.filter (λ p : name × bool, ¬ p.2)).map (λ p, p.1),
   let use_pr := (use.filter (λ p : name × bool, p.2)).map (λ p, p.1),

   environment ← if `_ ∈ use_fi then all_defs_except gex else return [],
   let use_fi := use_fi.erase `_,

   with_fi_lemmas ← (list.join <$> use_fi.mmap attribute.get_instances) >>= list.mmap mk_const,
   with_pr_lemmas ← (list.join <$> use_pr.mmap attribute.get_instances) >>= list.mmap mk_const,

   -- If the goal is not propositional, we do not include the non-propositional local hypotheses,
   -- unless specifically included via `[*]`.
   prop ← succeeds propositional_goal,
   hypotheses ← list.filter (λ h : expr, h.local_uniq_name ∉ hex) <$>  -- remove explicitly removed hypotheses
   if (¬no_dflt ∧ prop) ∨ all_hyps then
     local_context
   else if no_dflt then
     return []
   else -- it's a non-propositional goal, no `[*]`, no `only`, so conservatively only take propositional hypotheses
     local_context >>= list.mfilter (λ e, is_proof e),

   let filter_excl : list expr → list expr := list.filter $ λ h, h.const_name ∉ gex,

   progress_lemmas ← (filter_excl $ extra_pr_lemmas ++ with_pr_lemmas ++ tagged_pr_lemmas).enum.mmap
     (λ l, do t ← infer_type l.2, n ← pp l.2, return { back_lemma . name := to_string n, lem := l.2, ty := t, finishing := ff, index := l.1 }),
   finishing_lemmas ← (filter_excl $ extra_fi_lemmas ++ with_fi_lemmas ++ hypotheses ++ tagged_fi_lemmas).enum.mmap
     (λ l, do t ← infer_type l.2, n ← pp l.2, return { back_lemma . name := to_string n, lem := l.2, ty := t, finishing := tt, index := l.1 + progress_lemmas.length }),
   let environment_lemmas := environment.enum.map (λ p, { back_lemma . name := to_string p.2.1, lem := p.2.2.1, ty := p.2.2.2, finishing := tt, from_library := tt, index := p.1 + progress_lemmas.length + finishing_lemmas.length }),

   return $ progress_lemmas ++ finishing_lemmas ++ environment_lemmas

meta def replace_mvars (e : expr) : expr :=
e.replace (λ e' _, if e'.is_meta_var then some (unchecked_cast pexpr.mk_placeholder) else none)

end back

open back
open lean lean.parser expr interactive.types
open tactic

namespace interactive

open interactive interactive.types expr

local attribute [instance] lex_decidable_linear_order

meta def back_core
  {α : Type} [preorder α] [@decidable_rel α (≤)] (C : back_state → α)
  (trace : option unit) (no_dflt : bool)
  (hs : list back.back_arg_type) (wth : list (name × bool)) (limit library_limit : option ℕ) : tactic string :=
do gs ← get_goals,
   lemmas ← tactic.back.mk_assumption_set no_dflt hs wth,
   tactic.back.back back_state.default_complexity lemmas limit library_limit,
   gs ← gs.mmap instantiate_mvars,
   gs ← gs.mmap head_beta,
   rs ← gs.mmap (λ g, do p ← pp (replace_mvars g), pure $ if g.has_meta_var then sformat!"refine {p}" else sformat!"exact {p}"),
   let r := string.intercalate ", " rs,
   if trace.is_some then tactic.trace r else skip,
   return r

/--
`back` performs backwards reasoning, recursively applying lemmas against the goals.

Lemmas can be specified via an optional argument, e.g. as `back [foo, bar]`. Every lemma
tagged with an attribute `qux` may be included using the syntax `back with qux`.
Additionally, `back` always includes any lemmas tagged with the attribute `@[back]`,
and all local propositional hypotheses.

(If the goal is a proposition, `back` is more aggressive and includes all hypotheses. This
can be achieved in other cases using `back [*]`.)

Lemmas which were included because of the `@[back]` attribute, or local hypotheses,
can be excluded using the notation `back [-h]`.

Further, lemmas can be tagged with the `@[back!]` attribute, or appear in the arguments with
a leading `!`, e.g. as `back [!foo]` or `back with !qux`. The tactic `back` will return
successfully if it either discharges the goal, or applies at least one `!` lemma.
(More precisely, `back` will apply some non-empty and maximal collection of the lemmas,
subject to the condition that if any lemma not marked with `!` is applied, all resulting
subgoals are later dischargeed.)

Finally, the search depth can be controlled, e.g. as `back 5`. The default value is 20.

`back?` will print a trace message showing the term it constructed. (Possibly with placeholders,
for use with `refine`.)

`back` will apply lemmas even if this introduces new metavariables (so for example it is possible
to apply transitivity lemmas), but with the proviso that any subgoals containing metavariables must
be subsequently discharged in a single step. -- FIXME this is no longer what's implemented!
-/
meta def back
  (trace : parse $ optional (tk "?")) (no_dflt : parse only_flag)
  (hs : parse back_arg_list) (wth : parse with_back_ident_list) (limit library_limit : parse (optional (with_desc "n" small_nat))) : tactic string :=
back_core back_state.default_complexity trace no_dflt hs wth limit library_limit

-- TODO once Kenny's algebra/punit_instances.lean is merged, just use that.
def unit_preorder : preorder unit :=
{ le := λ _ _, true,
  le_refl := λ a, by trivial,
  le_trans := λ a b c h₁ h₂, by trivial }

local attribute [instance] unit_preorder

meta def solve_by_elim'
  (trace : parse $ optional (tk "?")) (no_dflt : parse only_flag)
  (hs : parse back_arg_list) (wth : parse with_back_ident_list) (limit library_limit : parse (optional (with_desc "n" small_nat))) : tactic string :=
back_core back_state.depth_first_complexity trace no_dflt hs wth limit library_limit


-- /--
-- `library_search` calls `back`, passing all imported lemmas. Surprisingly, this sometimes works.
-- By default, `library_search` uses at most two lemmas from the library (but perhaps more local
-- hypotheses or lemmas tagged `@[back]`). This can be adjusted, e.g. as `library_search 1`.
-- -/
-- meta def library_search (hs : parse back_arg_list) (library_limit : parse (optional (with_desc "n" small_nat))): tactic string :=
--   back (some ()) ff hs [(`_, ff)] none (library_limit <|> some 2)

end interactive

end tactic

attribute [back] congr_arg congr_fun

-- Some examples of lemmas that we might want to tag `back` or `back!`.

local attribute [back!] min_le_left min_le_right le_max_left le_max_right le_refl
local attribute [back] lt_min le_min max_lt max_le

-- Even transitivity lemmas are okay; back uses them, but somewhat conservatively.
local attribute [back] lt_of_lt_of_le lt_of_le_of_lt
