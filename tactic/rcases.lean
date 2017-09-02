/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.dlist data.list.basic

open lean lean.parser

namespace tactic

inductive rcases_patt : Type
| one : name → rcases_patt
| many : list (list rcases_patt) → rcases_patt

#print instances has_reflect

instance rcases_patt.inhabited : inhabited rcases_patt :=
⟨rcases_patt.one `_⟩

def rcases_patt.name : rcases_patt → name
| (rcases_patt.one n) := n
| _ := `_

meta instance rcases_patt.has_reflect : has_reflect rcases_patt
| (rcases_patt.one n) := `(_)
| (rcases_patt.many l) := `(λ l, rcases_patt.many l).subst $
  by have := rcases_patt.has_reflect; exact list.reflect l

meta def rcases.process_constructor :
  nat → list rcases_patt → list name × list rcases_patt
| 0     ids  := ([], [])
| 1     []   := ([`_], [default _])
| 1     [id] := ([id.name], [id])
| 1     ids  := ([`_], [rcases_patt.many [ids]])
| (n+1) ids  :=
  let (ns, ps) := rcases.process_constructor n ids.tail,
      p := ids.head in
  (p.name :: ns, p :: ps)

meta def rcases.process_constructors (params : nat) :
  list name → list (list rcases_patt) →
  tactic (dlist name × list (name × list rcases_patt))
| []      ids := pure (dlist.empty, [])
| (c::cs) ids := do
  fn ← mk_const c,
  n  ← get_arity fn,
  let (h, t) := by from match cs, ids.tail with
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

meta def rcases.continue
  (rcases_core : list (list rcases_patt) → expr → tactic (list expr))
  (n : nat) : list (rcases_patt × expr) → tactic (list expr)
| [] := intron n >> get_goals
| ((rcases_patt.many ids, e) :: l) := do
  gs ← rcases_core ids e,
  list.join <$> gs.mmap (λ g, set_goals [g] >> rcases.continue l)
| (_ :: l) := rcases.continue l

meta def rcases_core (n : nat) : list (list rcases_patt) → expr → tactic (list expr)
| ids e := do
  t   ← infer_type e,
  env ← get_env,
  let I := t.get_app_fn.const_name,
  when (¬env.is_inductive I) $
    fail format!"rcases tactic failed, {e} is not an inductive datatype",
  let params := env.inductive_num_params I,
  let c := env.constructors_of I,
  (ids, r) ← rcases.process_constructors params c ids,
  l ← cases_core e ids.to_list,
  gs ← get_goals,
  list.join <$> (align (λ (a : _ × _) (b : _ × _ × _), a.1 = b.2.1) r (gs.zip l)).mmap
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