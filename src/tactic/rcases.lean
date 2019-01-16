/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.dlist tactic.cache

open lean lean.parser

namespace tactic

/-
These synonyms for `list` are used to clarify the meanings of the many
usages of lists in this module.

- `listΣ` is used where a list represents a disjunction, such as the
  list of possible constructors of an inductive type.

- `listΠ` is used where a list represents a conjunction, such as the
  list of arguments of an individual constructor.

These are merely type synonyms, and so are not checked for consistency
by the compiler.

The `def`/`local notation` combination makes Lean retain these
annotations in reported types.
-/
@[reducible] def list_Sigma := list
@[reducible] def list_Pi := list
local notation `listΣ` := list_Sigma
local notation `listΠ` := list_Pi

@[reducible] meta def goals := list expr

meta inductive rcases_patt : Type
| one : name → rcases_patt
| many : listΣ (listΠ rcases_patt) → rcases_patt

meta instance rcases_patt.inhabited : inhabited rcases_patt :=
⟨rcases_patt.one `_⟩

meta def rcases_patt.name : rcases_patt → name
| (rcases_patt.one n) := n
| _ := `_

meta instance rcases_patt.has_reflect : has_reflect rcases_patt
| (rcases_patt.one n) := `(_)
| (rcases_patt.many l) := `(λ l, rcases_patt.many l).subst $
  by haveI := rcases_patt.has_reflect; exact list.reflect l

/--
The parser/printer uses an "inverted" meaning for the `many` constructor:
rather than representing a sum of products, here it represents a
product of sums. We fix this by applying `invert`, defined below, to
the result.
-/
meta inductive rcases_patt_inverted : Type
| one : name → rcases_patt_inverted
| many : listΠ (listΣ rcases_patt_inverted) → rcases_patt_inverted

meta instance rcases_patt_inverted.inhabited : inhabited rcases_patt_inverted :=
⟨rcases_patt_inverted.one `_⟩

meta instance rcases_patt_inverted.has_reflect : has_reflect rcases_patt_inverted
| (rcases_patt_inverted.one n) := `(_)
| (rcases_patt_inverted.many l) := `(λ l, rcases_patt_inverted.many l).subst $
  by haveI := rcases_patt_inverted.has_reflect; exact list.reflect l

meta mutual def rcases_patt_inverted.invert, rcases_patt_inverted.invert_list
with rcases_patt_inverted.invert : listΣ rcases_patt_inverted → rcases_patt
| [rcases_patt_inverted.one n] := rcases_patt.one n
| l := rcases_patt.many (rcases_patt_inverted.invert_list l)

with rcases_patt_inverted.invert_list : listΣ rcases_patt_inverted → listΣ (listΠ rcases_patt)
| l := l.map $ λ p,
  match p with
  | rcases_patt_inverted.one n := [rcases_patt.one n]
  | rcases_patt_inverted.many l := rcases_patt_inverted.invert <$> l
  end

meta mutual def rcases_patt.invert, rcases_patt.invert_many, rcases_patt.invert_list, rcases_patt.invert'
with rcases_patt.invert : rcases_patt → listΣ rcases_patt_inverted
| (rcases_patt.one n) := [rcases_patt_inverted.one n]
| (rcases_patt.many ls) := rcases_patt.invert_many ls

with rcases_patt.invert_many : listΣ (listΠ rcases_patt) → listΣ rcases_patt_inverted
| [] := []
| [[rcases_patt.many ls@(_::_::_)]] := rcases_patt.invert_many ls
| (l::ls) := rcases_patt.invert' l :: rcases_patt.invert_many ls

with rcases_patt.invert_list : listΠ rcases_patt → listΠ (listΣ rcases_patt_inverted)
| [] := []
| [rcases_patt.many [l@(_::_::_)]] := rcases_patt.invert_list l
| (p::l) := rcases_patt.invert p :: rcases_patt.invert_list l

with rcases_patt.invert' : listΠ rcases_patt → rcases_patt_inverted
| [rcases_patt.one n] := rcases_patt_inverted.one n
| [] := rcases_patt_inverted.one `_
| ls := rcases_patt_inverted.many (rcases_patt.invert_list ls)

meta mutual def rcases_patt_inverted.format, rcases_patt_inverted.format_list
with rcases_patt_inverted.format : rcases_patt_inverted → format
| (rcases_patt_inverted.one n) := to_fmt n
| (rcases_patt_inverted.many []) := "⟨⟩"
| (rcases_patt_inverted.many ls) := "⟨" ++ format.group (format.nest 1 $
    format.join $ list.intersperse ("," ++ format.line) $
    ls.map (format.group ∘ rcases_patt_inverted.format_list)) ++ "⟩"

with rcases_patt_inverted.format_list : listΣ rcases_patt_inverted → opt_param bool ff → format
| [] br := "⟨⟩"
| [p] br := rcases_patt_inverted.format p
| (p::l) br :=
  let fmt := rcases_patt_inverted.format p ++ " |" ++ format.space ++
    rcases_patt_inverted.format_list l in
  if br then format.bracket "(" ")" fmt else fmt

meta instance rcases_patt_inverted.has_to_format :
  has_to_format rcases_patt_inverted := ⟨rcases_patt_inverted.format⟩

meta def rcases_patt.format (p : rcases_patt) (br := ff) : format :=
rcases_patt_inverted.format_list p.invert br

meta instance rcases_patt.has_to_format : has_to_format rcases_patt := ⟨rcases_patt.format⟩

/--
Takes the number of fields of a single constructor and patterns to
match its fields against (not necessarily the same number). The
returned lists each contain one element per field of the
constructor. The `name` is the name which will be used in the
top-level `cases` tactic, and the `rcases_patt` is the pattern which
the field will be matched against by subsequent `cases` tactics.
-/

meta def rcases.process_constructor :
  nat → listΠ rcases_patt → listΠ name × listΠ rcases_patt
| 0     ids  := ([], [])
| 1     []   := ([`_], [default _])
| 1     [id] := ([id.name], [id])

-- The interesting case: we matched the last field against multiple
-- patterns, so split off the remaining patterns into a subsequent
-- match. This handles matching `α × β × γ` against `⟨a, b, c⟩`.
| 1     ids  := ([`_], [rcases_patt.many [ids]])

| (n+1) ids  :=
  let (ns, ps) := rcases.process_constructor n ids.tail,
      p := ids.head in
  (p.name :: ns, p :: ps)

meta def rcases.process_constructors (params : nat) :
  listΣ name → listΣ (listΠ rcases_patt) →
  tactic (dlist name × listΣ (name × listΠ rcases_patt))
| []      ids := pure (dlist.empty, [])
| (c::cs) ids := do
  n ← mk_const c >>= get_arity,
  let (h, t) := (match cs, ids.tail with
  -- We matched the last constructor against multiple patterns,
  -- so split off the remaining constructors. This handles matching
  -- `α ⊕ β ⊕ γ` against `a|b|c`.
  | [], _::_ := ([rcases_patt.many ids], [])
  | _, _ := (ids.head, ids.tail)
  end : _),
  let (ns, ps) := rcases.process_constructor (n - params) h,
  (l, r) ← rcases.process_constructors cs t,
  pure (dlist.of_list ns ++ l, (c, ps) :: r)

private def align {α β} (p : α → β → Prop) [∀ a b, decidable (p a b)] :
  list α → list β → list (α × β)
| (a::as) (b::bs) :=
  if p a b then (a, b) :: align as bs else align as (b::bs)
| _ _ := []

private meta def get_local_and_type (e : expr) : tactic (expr × expr) :=
(do t ← infer_type e, pure (t, e)) <|> (do
    e ← get_local e.local_pp_name,
    t ← infer_type e, pure (t, e))

meta mutual def rcases_core, rcases.continue
with rcases_core : listΣ (listΠ rcases_patt) → expr → tactic goals
| ids e := do
  (t, e) ← get_local_and_type e,
  t ← whnf t,
  env ← get_env,
  let I := t.get_app_fn.const_name,
  (ids, r, l) ← (if I ≠ `quot
  then do
    when (¬env.is_inductive I) $
      fail format!"rcases tactic failed: {e} : {I} is not an inductive datatype",
    let params := env.inductive_num_params I,
    let c := env.constructors_of I,
    (ids, r) ← rcases.process_constructors params c ids,
    l ← cases_core e ids.to_list,
    return (ids, r, l)
  else do
    (ids, r) ← rcases.process_constructors 2 [`quot.mk] ids,
    [(_, d)] ← induction e ids.to_list `quot.induction_on |
      fail format!"quotient induction on {e} failed. Maybe goal is not in Prop?",
    -- the result from `induction` is missing the information that the original constructor was
    -- `quot.mk` so we fix this up:
    return (ids, r, [(`quot.mk, d)])),
  gs ← get_goals,
  -- `cases_core` may not generate a new goal for every constructor,
  -- as some constructors may be impossible for type reasons. (See its
  -- documentation.) Match up the new goals with our remaining work
  -- by constructor name.
  list.join <$> (align (λ (a : name × _) (b : _ × name × _), a.1 = b.2.1) r (gs.zip l)).mmap
    (λ⟨⟨_, ps⟩, g, _, hs, _⟩,
      set_goals [g] >> rcases.continue (ps.zip hs))

with rcases.continue : listΠ (rcases_patt × expr) → tactic goals
| [] := get_goals
| ((rcases_patt.many ids, e) :: l) := do
  gs ← rcases_core ids e,
  list.join <$> gs.mmap (λ g, set_goals [g] >> rcases.continue l)
| ((rcases_patt.one `rfl, e) :: l) := do
  (t, e) ← get_local_and_type e,
  subst e,
  rcases.continue l
-- If the pattern is any other name, we already bound the name in the
-- top-level `cases` tactic, so there is no more work to do for it.
| (_ :: l) := rcases.continue l

meta def rcases (p : pexpr) (ids : listΣ (listΠ rcases_patt)) : tactic unit :=
do e ← i_to_expr p,
  if e.is_local_constant then
    focus1 (rcases_core ids e >>= set_goals)
  else do
    x ← mk_fresh_name,
    n ← revert_kdependencies e semireducible,
    (tactic.generalize e x)
    <|>
    (do t ← infer_type e,
        tactic.assertv x t e,
        get_local x >>= tactic.revert,
        return ()),
    h ← tactic.intro1,
    focus1 (rcases_core ids h >>= set_goals)

meta def rintro (ids : listΠ rcases_patt) : tactic unit :=
do l ← ids.mmap (λ id, do
    e ← intro id.name,
    return (id, e)),
  focus1 (rcases.continue l >>= set_goals)

def merge_list {α} (m : α → α → α) : list α → list α → list α
| [] l₂ := l₂
| l₁ [] := l₁
| (a :: l₁) (b :: l₂) := m a b :: merge_list l₁ l₂

meta def rcases_patt.merge : rcases_patt → rcases_patt → rcases_patt
| (rcases_patt.many ids₁) (rcases_patt.many ids₂) :=
  rcases_patt.many (merge_list (merge_list rcases_patt.merge) ids₁ ids₂)
| (rcases_patt.one `rfl) (rcases_patt.many ids₂) :=
  rcases_patt.many (merge_list (merge_list rcases_patt.merge) [[]] ids₂)
| (rcases_patt.many ids₁) (rcases_patt.one `rfl) :=
  rcases_patt.many (merge_list (merge_list rcases_patt.merge) ids₁ [[]])
| (rcases_patt.one `rfl) (rcases_patt.one `rfl) := rcases_patt.one `rfl
| (rcases_patt.one `_) p := p
| p (rcases_patt.one `_) := p
| (rcases_patt.one n) _ := rcases_patt.one n
| _ (rcases_patt.one n) := rcases_patt.one n

meta mutual def rcases_hint_core, rcases_hint.process_constructors, rcases_hint.continue
with rcases_hint_core : ℕ → expr → tactic (rcases_patt × goals)
| depth e := do
  (t, e) ← get_local_and_type e,
  t ← whnf t,
  env ← get_env,
  some l ← try_core (guard (depth ≠ 0) >> cases_core e) |
    prod.mk (rcases_patt.one e.local_pp_name) <$> get_goals,
  let I := t.get_app_fn.const_name,
  if I = ``eq then
    prod.mk (rcases_patt.one `rfl) <$> get_goals
  else do
    let c := env.constructors_of I,
    gs ← get_goals,
    (ps, gs') ← rcases_hint.process_constructors (depth - 1) c (gs.zip l),
    pure (rcases_patt.many ps, gs')

with rcases_hint.process_constructors : ℕ → listΣ name →
  list (expr × name × listΠ expr × list (name × expr)) →
  tactic (listΣ (listΠ rcases_patt) × goals)
| depth [] _  := pure ([], [])
| depth cs [] := pure (cs.map (λ _, []), [])
| depth (c::cs) ((g, c', hs, _) :: l) :=
  if c ≠ c' then do
    (ps, gs) ← rcases_hint.process_constructors depth cs l,
    pure ([] :: ps, gs)
  else do
    (p, gs) ← set_goals [g] >> rcases_hint.continue depth hs,
    (ps, gs') ← rcases_hint.process_constructors depth cs l,
    pure (p :: ps, gs ++ gs')

with rcases_hint.continue : ℕ → listΠ expr → tactic (listΠ rcases_patt × goals)
| depth [] := prod.mk [] <$> get_goals
| depth (e :: l) := do
  (p, gs) ← rcases_hint_core depth e,
  (ps, gs') ← gs.mfoldl (λ (r : listΠ rcases_patt × goals) g,
    do (ps, gs') ← set_goals [g] >> rcases_hint.continue depth l,
      pure (merge_list rcases_patt.merge r.1 ps, r.2 ++ gs')) ([], []),
  pure (p :: ps, gs')

meta def rcases_hint (p : pexpr) (depth : nat) : tactic rcases_patt :=
do e ← i_to_expr p,
  if e.is_local_constant then
    focus1 $ do (p, gs) ← rcases_hint_core depth e, set_goals gs, pure p
  else do
    x ← mk_fresh_name,
    n ← revert_kdependencies e semireducible,
    (tactic.generalize e x)
    <|>
    (do t ← infer_type e,
        tactic.assertv x t e,
        get_local x >>= tactic.revert,
        pure ()),
    h ← tactic.intro1,
    focus1 $ do (p, gs) ← rcases_hint_core depth h, set_goals gs, pure p

meta def rintro_hint (depth : nat) : tactic (listΠ rcases_patt) :=
do l ← intros,
  focus1 $ do
    (p, gs) ← rcases_hint.continue depth l,
    set_goals gs,
    pure p

section interactive
open interactive interactive.types expr

local notation `listΣ` := list_Sigma
local notation `listΠ` := list_Pi

local postfix `?`:9001 := optional
local postfix *:9001 := many

meta def rcases_patt_parse_core
  (rcases_patt_parse_list : parser (listΣ rcases_patt_inverted)) :
  parser rcases_patt_inverted | x :=
((rcases_patt_inverted.one <$> ident_) <|>
(rcases_patt_inverted.many <$> brackets "⟨" "⟩"
  (sep_by (tk ",") rcases_patt_parse_list))) x

meta def rcases_patt_parse_list : parser (listΣ rcases_patt_inverted) :=
with_desc "patt" $
list.cons <$> rcases_patt_parse_core rcases_patt_parse_list <*>
  (tk "|" *> rcases_patt_parse_core rcases_patt_parse_list)*

meta def rcases_patt_parse : parser rcases_patt_inverted :=
with_desc "patt_list" $ rcases_patt_parse_core rcases_patt_parse_list

meta def rcases_parse_depth : parser nat :=
do o ← (tk ":" *> small_nat)?, pure $ o.get_or_else 5

precedence `?`:max
meta def rcases_parse : parser (pexpr × (listΣ (listΠ rcases_patt) ⊕ nat)) :=
do hint ← (tk "?")?,
  p ← texpr,
  match hint with
  | none := do
    ids ← (tk "with" *> rcases_patt_parse_list)?,
    pure (p, sum.inl $ rcases_patt_inverted.invert_list (ids.get_or_else [default _]))
  | some _ := do depth ← rcases_parse_depth, pure (p, sum.inr depth)
  end

meta def rintro_parse : parser (listΠ rcases_patt ⊕ nat) :=
(tk "?" >> sum.inr <$> rcases_parse_depth) <|>
sum.inl <$> (rcases_patt_inverted.invert <$>
  (brackets "(" ")" rcases_patt_parse_list <|>
  (λ x, [x]) <$> rcases_patt_parse))*

meta def ext_patt := listΠ rcases_patt

meta def ext_parse : parser ext_patt :=
(rcases_patt_inverted.invert <$>
  (brackets "(" ")" rcases_patt_parse_list <|>
  (λ x, [x]) <$> rcases_patt_parse))*

end interactive
end tactic
