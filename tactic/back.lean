-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Keeley Hoek

import tactic.basic

namespace tactic

@[user_attribute]
meta def back_attribute : user_attribute unit (option unit) := {
  name := `back,
  descr :=
"A lemma that should be applied to a goal whenever possible;
use `back` to automatically `apply` all lemmas tagged `[back]`.
Lemmas tagged with `[back!]` will be applied even if the
resulting goals cannot all be discharged.",
  parser := optional $ lean.parser.tk "!"
}

/-- Stub for implementing faster lemma filtering using Pi binders in the goal -/
private meta def is_lemma_applicable (lem : expr) : tactic bool := return true

-- At this point we have a whole pile of experimental methods for limiting the search tree.
-- 1) limiting the total search depth
-- 2) limiting the number of consecutive steps that involve mvars in the types of the goals
-- 3) tracking the list of goals after the most recent application of each lemma, and checking
--    they do not repeat
-- 4) limiting the number of applications of each lemma
-- 5) deleting an iff lemma after it is applied

-- Unfortunately, it's still not as good as I'd like.

-- It seems the only option (besides starting to do forward reasoning too!)
-- is to do something cleverer than a depth first search of applications.

-- We can weigh a node in the search tree by:
-- * Depth from the root
-- * Number of side branches (and on higher nodes)
-- * Number of attempted lemma applications (and on higher nodes)

meta structure back_lemma :=
(lem : expr)
(finishing : bool)
(count : ℕ)

meta structure back_state :=
(steps : ℕ := 0)
(limit : option ℕ)
(lemmas : list back_lemma) -- later we may update this as we go (removing or reordering)
(stashed : list expr := {})   -- Stores goals which we're going to return to the user.
(committed : list expr := {}) -- Stores goals which we must complete.
(in_progress : list expr)     -- Stores goals which we're still working on.

meta def count_arrows : expr → ℕ
| (expr.pi n bi d b) :=
   if b.has_var_idx 0 then count_arrows b
                      else 1 + count_arrows b
| `(%%a <-> %%b) := 1 + min (count_arrows a) (count_arrows b)
| _ := 0

meta def sort_by_arrows (L : list back_lemma) : tactic (list back_lemma) :=
do M ← L.mmap (λ e, do c ← count_arrows <$> infer_type e.lem, return (c, e)),
   return ((list.qsort (λ (p q : ℕ × back_lemma), p.1 ≤ q.1) M).map (λ p, p.2))

meta def back_state.init (progress finishing : list expr) (limit : option ℕ): tactic back_state :=
do g :: _ ← get_goals,
   lemmas ← sort_by_arrows $ (finishing.map (λ e, ⟨e, tt, 0⟩)) ++
                             (progress.map  (λ e, ⟨e, ff, 0⟩)),
   return
   { limit := limit,
     lemmas := lemmas,
     in_progress := [g] }

meta def filter_mvars (L : list expr) : tactic (list expr) :=
(list.filter (λ e, e.is_meta_var)) <$> (L.mmap (λ e, instantiate_mvars e))

meta def patch_nth {α : Type} (f : α → α) : ℕ → list α → list α
| _ []           := []
| 0 (h :: t)     := f h :: t
| (n+1) (h :: t) := h :: patch_nth n t

meta def opatch_nth {α : Type} (f : α → option α) : ℕ → list α → list α
| _ []           := []
| 0 (h :: t)     := match f h with
                    | (some e) := e :: t
                    | none     := t
                    end
| (n+1) (h :: t) := h :: opatch_nth n t

/--
* Discard any goals which have already been solved,
* increment the `step` counter,
* and remove applied iffs.
-/
meta def back_state.clean (s : back_state) (index : ℕ) (last_lemma : expr): tactic back_state :=
do stashed ← filter_mvars s.stashed,
   committed ← filter_mvars s.committed,
   in_progress ← filter_mvars s.in_progress,
   -- We don't apply `iff` lemmas more than once.
   lemmas ← (iff_mp last_lemma >> pure (s.lemmas.remove_nth index))
            <|> pure (opatch_nth (λ b, if b.count ≥ 4 then none else some { count := b.count + 1, .. b }) index s.lemmas),
   return
   { steps := s.steps + 1,
     stashed := stashed,
     committed := committed,
     in_progress := in_progress,
     lemmas := lemmas,
     .. s}

meta def pad_trace (n : ℕ) {α : Type} [has_to_tactic_format α] (a : α) : tactic unit :=
do let s := (list.repeat ' ' n).as_string,
   p ← pp a,
   trace (s ++ sformat!"{p}")

meta def back_state.apply (s : back_state) (index : ℕ) (e : expr) (committed : bool) : tactic back_state :=
do has_mvars ← expr.has_meta_var <$> target,
   apply_thorough e,
   goal_types ← get_goals >>= λ gs, gs.mmap infer_type,
   let nmvars := (goal_types.map (λ t : expr, t.list_meta_vars.length)).foldl (+) 0,
   guard (nmvars ≤ 2),
   pad_trace s.steps e,
   get_goals >>= λ gs, gs.mmap infer_type >>= pad_trace s.steps,
  --  trace nmvars,
  --  done <|> guard ¬has_mvars, -- If there were metavars, we insist on solving in one step.
   s' ← s.clean index e,
   (done >> return s') <|> do
   gs ← get_goals,
   if committed then
     return { committed := gs ++ s.committed, .. s' }
   else
     return { in_progress := gs ++ s.in_progress, .. s' }

meta def back_state.run : Π (s : back_state), tactic back_state
| s :=
  do
  guard (s.steps ≤ s.limit.get_or_else 20),
  match s.committed with
  | [] :=
    -- Let's see if we can do anything with `in_progress` goals
    match s.in_progress with
    | [] := return s -- Great, all done!
    | (p :: ps) :=
    do set_goals [p],
      (s.lemmas.enum.any_of $ λ e, { in_progress := ps, .. s }.apply e.1 e.2.1 e.2.2 >>= back_state.run)
      <|> { in_progress := ps, stashed := p :: s.stashed, .. s }.run
    end
  | (c :: cs) :=
    -- We must discharge `c`.
    do set_goals [c],
      s.lemmas.enum.any_of $ λ e, { committed := cs, .. s }.apply e.1 e.2.1 tt >>= back_state.run
  end

/-- Takes two sets of lemmas, 'progress' lemmas and 'finishing' lemmas.

    Progress lemmas should be applied whenever possible, regardless of new hypotheses.
    Finishing lemmas should be applied only as part of a sequence of applications that close the goals.

    `back` succeeds if at least one progress lemma was applied, or all goals are discharged.
    -/
meta def back (progress finishing : list expr) (limit : option ℕ) : tactic unit :=
do i ← back_state.init progress finishing limit,
   f ← i.run,
   set_goals (f.stashed ++ f.in_progress), -- TODO in_progress should be empty!
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
(tk "with" *> (((λ n, (n, ff)) <$> ident_) <|> (tk "!" *> (λ n, (n, tt)) <$> ident_))*) <|> return []

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

/--
Returns a list of "finishing lemmas" (which should only be applied as part of a
chain of applications which discharges the goal), and a list of "progress lemmas",
the successful application of any one of which counting as a success.
-/
--This is a close relative of `mk_assumption_set` in tactic/interactive.lean.
meta def mk_assumption_set (no_dflt : bool) (hs : list back_arg_type) (use : list (name × bool)) :
  tactic (list expr × list expr) :=
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
   with_fi_lemmas ← (list.join <$> use_fi.mmap attribute.get_instances) >>= list.mmap mk_const,
   with_pr_lemmas ← (list.join <$> use_pr.mmap attribute.get_instances) >>= list.mmap mk_const,

   -- If the goal is not propositional, we do not include the local context unless specifically
   -- included via `[*]`.
   prop ← option.is_some <$> try_core propositional_goal,
   hypotheses ← list.filter (λ h : expr, h.local_uniq_name ∉ hex) <$>  -- remove local exceptions
   if (¬no_dflt ∧ prop) ∨ all_hyps then
     local_context
   else if no_dflt then
     return []
   else -- it's a non-propositional goal, no `[*]`, no `only`, so conservatively only take propositional hypotheses
     local_context >>= list.mfilter (λ e, is_proof e),

   let filter_excl : list expr → list expr := list.filter $ λ h, h.const_name ∉ gex,
   return (/- progress  lemmas -/ filter_excl $ extra_pr_lemmas ++ with_pr_lemmas ++ tagged_pr_lemmas,
           /- finishing lemmas -/ filter_excl $ extra_fi_lemmas ++ with_fi_lemmas ++ hypotheses ++ tagged_fi_lemmas)

meta def replace_mvars (e : expr) : expr :=
e.replace (λ e' _, if e'.is_meta_var then some (unchecked_cast pexpr.mk_placeholder) else none)

namespace interactive

open interactive interactive.types expr

/--
`back` performs backwards reasoning, recursively applying lemmas against the goal.

Lemmas can be specified via an optional argument, e.g. as `back [foo, bar]`. Every lemma
tagged with an attribute `qux` may be included using `back using qux`.
Additionally, `back` always includes any lemmas tagged with the attribute `@[back]`,
and all local propositional hypotheses.

(If the goal is a proposition, `back` is more aggressive and includes all hypotheses. This
can be achieved in other cases using using `back [*]`.)

Lemmas which were included because of the `@[back]` attribute, or local hypotheses,
can be excluded using the notation `back [-h]`.

Further, lemmas can be tagged with the `@[back!]` attribute, or appear in the list with
a leading `!`, e.g. as `back [!foo]` or `back using !qux`. The tactic `back` will return
successfully if it either discharges the goal, or applies at least one `!` lemma.
(More precisely, `back` will apply a non-empty and maximal collection of the lemmas,
subject to the condition that if any lemma not marked with `!` is applied, all resulting
subgoals are later dischargeed.)

Finally, the search depth can be controlled e.g. as `back 5`. The default value is 100.

`back?` will print a trace message showing the term it constructed. (Possibly with placeholders,
for use with `refine`.)

`back` will apply lemmas even if this introduces new metavariables (so for example it is possible
to apply transitivity lemmas), but with the proviso that any subgoals containing metavariables must
be subsequently discharged in a single step.
-/
meta def back
  (trace : parse $ optional (tk "?")) (no_dflt : parse only_flag)
  (hs : parse back_arg_list) (wth : parse with_back_ident_list) (limit : parse (optional small_nat)) : tactic string :=
do g :: _ ← get_goals,
   (pr, fi) ← tactic.mk_assumption_set no_dflt hs wth,
   r ← focus1 $ (do
     tactic.back pr fi limit,
     g ← instantiate_mvars g,
     r ← pp (replace_mvars g),
     pure (if g.has_meta_var then sformat!"refine {r}" else sformat!"exact {r}")),
   if trace.is_some then tactic.trace r else skip,
   return r

end interactive

end tactic

attribute [back] congr_arg congr_fun

-- Some examples of lemmas that we might want to tag `back` or `back!`.

local attribute [back!] min_le_left min_le_right le_max_left le_max_right le_refl
local attribute [back] lt_min le_min max_lt max_le

-- Even transitivity lemmas are okay; back uses them, but somewhat conservatively.
local attribute [back] lt_of_lt_of_le lt_of_le_of_lt
