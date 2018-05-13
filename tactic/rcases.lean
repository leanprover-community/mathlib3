/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.dlist tactic.basic

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

inductive rcases_patt : Type
| one : name → rcases_patt
| many : listΣ (listΠ rcases_patt) → rcases_patt

instance rcases_patt.inhabited : inhabited rcases_patt :=
⟨rcases_patt.one `_⟩

def rcases_patt.name : rcases_patt → name
| (rcases_patt.one n) := n
| _ := `_

meta instance rcases_patt.has_reflect : has_reflect rcases_patt
| (rcases_patt.one n) := `(_)
| (rcases_patt.many l) := `(λ l, rcases_patt.many l).subst $
  begin
    have := rcases_patt.has_reflect,
    tactic.reset_instance_cache, -- this combo will be `haveI` later
    exact list.reflect l
  end

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
  fn ← mk_const c,
  n  ← get_arity fn,
  let (h, t) := by from match cs, ids.tail with
  -- We matched the last constructor against multiple patterns,
  -- so split off the remaining constructors. This handles matching
  -- `α ⊕ β ⊕ γ` against `a|b|c`.
  | [], _::_ := ([rcases_patt.many ids], [])
  | _, _ := (ids.head, ids.tail)
  end,
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

meta def rcases.continue
  (rcases_core : listΣ (listΠ rcases_patt) → expr → tactic goals)
  (n : nat) : listΠ (rcases_patt × expr) → tactic goals
| [] := intron n >> get_goals
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

meta def rcases_core (n : nat) : listΣ (listΠ rcases_patt) → expr → tactic goals
| ids e := do
  (t, e) ← get_local_and_type e,
  t ← whnf t,
  env ← get_env,
  let I := t.get_app_fn.const_name,
  when (¬env.is_inductive I) $
    fail format!"rcases tactic failed, {e} is not an inductive datatype",
  let params := env.inductive_num_params I,
  let c := env.constructors_of I,
  (ids, r) ← rcases.process_constructors params c ids,
  l ← cases_core e ids.to_list,
  gs ← get_goals,
  -- `cases_core` may not generate a new goal for every constructor,
  -- as some constructors may be impossible for type reasons. (See its
  -- documentation.) Match up the new goals with our remaining work
  -- by constructor name.
  list.join <$> (align (λ (a : name × _) (b : _ × name × _), a.1 = b.2.1) r (gs.zip l)).mmap
    (λ⟨⟨_, ps⟩, g, _, hs, _⟩,
      set_goals [g] >> rcases.continue rcases_core n (ps.zip hs))

meta def rcases (p : pexpr) (ids : list (list rcases_patt)) : tactic unit :=
do e ← i_to_expr p,
  if e.is_local_constant then
    focus1 (rcases_core 0 ids e >>= set_goals)
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
    focus1 (rcases_core 0 ids h >>= set_goals)

end tactic
