-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Keeley Hoek

import tactic.basic tactic.ext

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

meta structure back_state :=
(remaining : ℕ := 100)
(lemmas : list (expr × bool)) -- later we might consider updating this as we go (removing or reordering)
(stashed : list expr := {}) -- Stores goals which we're going to return to the user.
(committed : list expr := {}) -- Stores goals which we must complete.
(in_progress : list expr) -- Stores goals which we're still working on.

meta def count_arrows : expr → ℕ
| (expr.pi n bi d b) :=
   if b.has_var_idx 0 then count_arrows b
                      else 1 + count_arrows b
| `(%%a <-> %%b) := 1 + min (count_arrows a) (count_arrows b)
| _ := 0

meta def sort_by_arrows (L : list (expr × bool)) : tactic (list (expr × bool)) :=
do M ← L.mmap (λ e, do c ← count_arrows <$> infer_type e.1, return (c, e)),
   return ((list.qsort (λ (p q : ℕ × (expr × bool)), p.1 ≤ q.1) M).map (λ p, p.2))

meta def back_state.init (progress finishing : list expr) (steps : ℕ): tactic back_state :=
do g :: _ ← get_goals,
   lemmas ← sort_by_arrows $ (finishing.map (λ e, (e, tt))) ++ (progress.map (λ e, (e, ff))),
  --  M ← lemmas.mmap (λ e, do c ← count_arrows <$> infer_type e.1, return (c, e)),
  --  trace M,
   return
   { remaining := steps,
     lemmas := lemmas,
     in_progress := [g] }

meta def filter_mvars (L : list expr) : tactic (list expr) :=
do instantiated ← (L.mmap (λ e, instantiate_mvars e)),
   return (instantiated.filter (λ e, e.is_meta_var))

/-- Discard any goals which have already been solved, and reduce the counter. -/
meta def back_state.clean (s : back_state) : tactic back_state :=
do stashed ← filter_mvars s.stashed,
   committed ← filter_mvars s.committed,
   in_progress ← filter_mvars s.in_progress,
   return
   { remaining := s.remaining - 1,
     stashed := stashed,
     committed := committed,
     in_progress := in_progress,
     .. s}

meta def back_state.collect
 (s : back_state) (committed : bool) (last_lemma : expr) : tactic back_state :=
do gs ← get_goals,
   if committed then
     return { committed := gs ++ s.committed, .. s }
   else
     return { in_progress := gs ++ s.in_progress, .. s }

meta def back_state.apply (s : back_state) (e : expr) (committed : bool) : tactic back_state :=
do has_mvars ← expr.has_meta_var <$> target,
   apply_thorough e,
   done <|> guard ¬has_mvars, -- If there were metavars, we insist on solving in one step.
  --  trace e,
   s' ← s.clean,
   (done >> return s')
   <|> (do s'.collect committed e)

meta def back_state.run : Π (s : back_state), tactic back_state
| s :=
  do
  -- s.in_progress.mmap infer_type >>= trace,
  -- s.committed.mmap infer_type >>= trace,
  guard (s.remaining > 0),
  match s.committed with
  | [] :=
    -- Let's see if we can do anything with `in_progress` goals
    match s.in_progress with
    | [] := return s -- Great, all done!
    | (p :: ps) :=
    do set_goals [p],
      (s.lemmas.any_of $ λ e, { in_progress := ps, .. s }.apply e.1 e.2 >>= back_state.run)
      <|> { in_progress := ps, stashed := p :: s.stashed, .. s }.run
    end
  | (c :: cs) :=
    -- We must discharge `c`.
    do set_goals [c],
      s.lemmas.any_of $ λ e, { committed := cs, .. s }.apply e.1 tt >>= back_state.run
  end

/-- Takes two sets of lemmas, 'progress' lemmas and 'finishing' lemmas.

    Progress lemmas should be applied whenever possible, regardless of new hypotheses.
    Finishing lemmas should be applied only as part of a sequence of applications that close the goals.

    `back` succeeds if at least one progress lemma was applied, or all goals are discharged.
    -/
meta def back (progress finishing : list expr) (steps : ℕ): tactic unit :=
do i ← back_state.init progress finishing steps,
   f ← i.run,
   set_goals (f.stashed ++ f.in_progress),
   guard (f.remaining < steps)

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
meta def mk_assumption_set (no_dflt : bool) (hs : list back_arg_type) :
  tactic (list expr × list expr) :=
do (extra_pr_lemmas, extra_fi_lemmas, gex, hex, all_hyps) ← decode_back_arg_list hs,
   /- `extra_lemmas` is explicitly requested lemmas
      `gex` are the excluded names
      `hex` are the excluded local hypotheses
      `all_hyps` means all hypotheses were included, via `*` -/
   extra_pr_lemmas ← build_list_expr_for_apply extra_pr_lemmas,
   extra_fi_lemmas ← build_list_expr_for_apply extra_fi_lemmas,
   (tagged_pr_lemmas, tagged_fi_lemmas) ← attribute.get_instances `back >>= collect_tagged_lemmas,

   -- If the goal is not propositional, we do not include the local context unless specifically
   -- included via `[*]`.
   prop ← option.is_some <$> try_core propositional_goal,
   hypotheses ← if (¬no_dflt ∧ prop) ∨ all_hyps then
     list.filter (λ h : expr, h.local_uniq_name ∉ hex) <$> local_context -- remove local exceptions
   else return [],

   let filter_excl : list expr → list expr := list.filter $ λ h, h.const_name ∉ gex,
   return (/- progress  lemmas -/ filter_excl $ extra_pr_lemmas ++ tagged_pr_lemmas,
           /- finishing lemmas -/ filter_excl $ extra_fi_lemmas ++ hypotheses ++ tagged_fi_lemmas)

meta def replace_mvars (e : expr) : expr :=
e.replace (λ e' _, if e'.is_meta_var then some (unchecked_cast pexpr.mk_placeholder) else none)

namespace interactive

open interactive interactive.types expr

/--
`back` performs backwards reasoning, recursively applying lemmas against the goal.

Lemmas can be specified via an optional argument, e.g. as `back [foo, bar]`. If one
of these arguments is an attribute, all lemmas tagged with that attribute will be
included. Additionally, `back` always includes any lemmas tagged with the attribute `@[back]`,
and, if the current goal is a proposition, all local hypotheses.

(If the goal is not a proposition, `back` is constructing data and so behaves more conservatively.
In this case, all local hypotheses can be included using `back [*]`.)

Lemmas which were included because of the `@[back]` attribute, or local hypotheses,
can be excluded using the notation `back [-h]`.

Further, lemmas can be tagged with the `@[back!]` attribute, or appear in the list with
a leading `!`, e.g. as `back [!foo]`. The tactic `back` will return successfully if it either
discharges the goal, or applies at least one `!` lemma. (More precisely, `back` will apply a
non-empty and maximal collection of the lemmas, subject to the condition that if any lemma not
marked with `!` is applied, all resulting subgoals are later dischargeed.)

Finally, the search depth can be controlled e.g. as `back 5`. The default value is 100.

`back?` will print a trace message showing the term it constructed. (Possibly with placeholders,
for use with `refine`.)

`back` will apply lemmas even if this introduces new metavariables (so for example it is possible
to apply transitivity lemmas), but with the proviso that any subgoals containing metavariables must
be subsequently discharged in a single step.
-/
meta def back
  (trace : parse $ optional (tk "?")) (no_dflt : parse only_flag)
  (hs : parse back_arg_list) (steps : parse small_nat := 100): tactic string :=
do g :: _ ← get_goals,
   (pr, fi) ← tactic.mk_assumption_set no_dflt hs,
   r ← focus1 $ (do
     tactic.back pr fi steps,
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
