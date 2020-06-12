import tactic.basic
import data.priority_queue
import order.lexicographic

open tactic

meta structure search_state (α : Type) :=
(data : α)
(state : tactic_state)

/--
A `search_tactic α β` takes two arguments,
a `b : β` representing the global state of the search,
and a `S : search_state α` representing a node in the search tree to be processed.
The value is a tactic returning a `β` representing the new global state,
and a list of `search_state α` to be added to the processing queue.

The tactic may assume that the `tactic_state` has already been set to `S.state`.
If the tactic fails, it is handled as if it had succeeded, returning `(b, [])`.
-/
meta def search_tactic (α β : Type) :=
β → search_state α → tactic (β × list (search_state α))

namespace search_tactic

variables {α β : Type}

/-- Takes a `search_tactic` which may fail, and replaces any failures with an empty list. -/
meta def catch (t : search_tactic α β) : search_tactic α β :=
λ b S, t b S <|> pure (b, [])

meta instance : has_add (search_tactic α β) :=
⟨λ t₁ t₂ b S, do
  (b', hd :: tl) ← t₁.catch b S | t₂ b S,
  return (b', hd :: tl)⟩

meta def search_tactic.of_tactic
  (update_local : α → tactic α) (update_global : β → β) (t : tactic unit) :
  search_tactic α β :=
λ b S, do
  t,
  s' ← get_state,
  a' ← update_local S.data,
  return (update_global b, [{ data := a', state := s' }])


variables [decidable_linear_order α] [has_to_format α] [has_to_format β]

-- Even though the function `search_state.data` is not injective, the priority queue should still work.
meta instance decidable_linear_order_search_state : decidable_linear_order (search_state α) :=
decidable_linear_order.lift search_state.data undefined infer_instance.

meta def step (t : search_tactic α β) (b : β) (Q : priority_queue (search_state α)) :
  tactic (β × priority_queue (search_state α)):=
do
  (some S, T) ← pure (priority_queue.pull Q),
  set_state S.state,
  trace_state,
  (b', SS) ← t.catch b S,
  pure (b', T.insert_all SS)

meta def run_queue_until (t : search_tactic α β) (P : α → β → bool) :
  β → priority_queue (search_state α) → tactic (β × search_state α)
| b Q := do
  trace format!"global: {b}",
  trace format!"queue: {(Q.1.map (search_state.data))}",
  some S ← pure (priority_queue.peek Q) | fail "Exhausted all search states.",
  if P S.data b then return (b, S) else
    do
      (b', Q') ← step t b Q,
      run_queue_until b' Q'

variables [inhabited α] [inhabited β]

meta def run_until (t : search_tactic α β) (P : α → β → bool) :
  tactic (search_state α) :=
do
  s ← get_state,
  let Q : priority_queue (search_state α) :=
    priority_queue.singleton { data := default α, state := s, },
  (b, S) ← t.run_queue_until P (default β) Q,
  set_state S.state,
  return S

end search_tactic

namespace tactic

/--
`some_goal t` runs the tactic `t` on the first goal it succeeds on.
-/
meta def some_goal {α : Type} (t : tactic α) : tactic α :=
do
  gs ← get_goals,
  (i, r) ← first (gs.enum.map (λ g, do set_goals [g.2], r ← t, return (g.1, r))),
  gs' ← get_goals,
  set_goals $ (gs.take i) ++ gs' ++ (gs.drop (i + 1)),
  return r

namespace interactive
meta def some_goal (t : itactic) : itactic :=
tactic.some_goal t
end interactive

end tactic

namespace tactic

/-!
We now implement a particular backtracking search tactic called `ariadne`,
using the `search_tactic` framework.
-/

namespace ariadne

meta structure thread :=
(num_goals : ℕ)
(local_solutions : ℕ) -- the total number of subgoals we have solved using `solve_by_elim`
(tried_solve_by_elim : bool)
(library_steps : ℕ)
(library_allowed : bool)
(queued_tactics : list (tactic ℕ))

meta instance : inhabited thread := ⟨
{ num_goals := 1,
  local_solutions := 0,
  tried_solve_by_elim := ff,
  library_steps := 0,
  library_allowed := tt,
  queued_tactics := [], }⟩

meta instance : has_to_format thread :=
{ to_format := λ D, format!"⟨{D.num_goals}, {D.local_solutions}, {D.library_steps}, {D.queued_tactics.length}⟩" ++ if D.tried_solve_by_elim then "" else "*" }

meta def thread.score (D : thread) :=
( -- Anything with 0 goals remaining comes first!
  min D.num_goals 1,
  -- Eagerly attempt terminal goals using `solve_by_elim`.
  if D.tried_solve_by_elim then 1 else 0,
  -- Prefer working on branches in which we've managed
  -- to discharge some subgoals using local hypotheses.
  -(D.local_solutions : ℤ),
  D.num_goals,
  -- if D.library_allowed then 0 else 1,
  D.library_steps,
  D.queued_tactics.length
)

section
local attribute [reducible] lex -- Make all the `lex` instances work on `prod`, too.

meta instance decidable_linear_order_search_state : decidable_linear_order thread :=
decidable_linear_order.lift thread.score undefined infer_instance.
end

/--
Attempt to solve any "terminal" goals using `solve_by_elim`.
There is no need to allow for backtracking, as any solution suffices.

This tactic always succeeds, returning a single new `search_state`, for which `tried_terminal = tt`.
-/
meta def solve_terminal_goals : search_tactic thread ℕ :=
λ b S, do
  let D := S.data,
  guardb $ ¬ D.tried_solve_by_elim,
  id ← mk_const `id,
  n ← suggest.apply_and_solve ff {} id,
  ng ← num_goals,
  let D' : thread :=
  { num_goals := ng,
    local_solutions := D.local_solutions + n,
    tried_solve_by_elim := tt,
    .. D },
  s' ← get_state,
  return (b+1, [{ state:= s', data := D' }])

/--
If there tactics queued in the `queued_tactics` field of the `thread`,
run them one at a time.
-/
meta def run_queued_tactic : search_tactic thread ℕ :=
λ b S, do
  let D := S.data,
  guardb $ D.tried_solve_by_elim,
  t :: ts ← pure D.queued_tactics,
  r ← try_core t,
  match r with
  | some n := do
      ng ← num_goals,
      let D₁ : thread :=
      { num_goals := ng,
        tried_solve_by_elim := tt,
        local_solutions := D.local_solutions + n,
        library_steps := D.library_steps + 1,
        library_allowed := tt,
        queued_tactics := [], },
      let D₂ : thread :=
      { queued_tactics := ts,
        .. D },
      s' ← get_state,
      return (b, [{ state := s', data := D₁ }, { data := D₂, .. S }])
  | none := do
      let D' : thread :=
      { queued_tactics := ts, -- remove code duplication?
        ..D },
      return (b, [{ data := D', .. S }])
  end

section
open tactic.suggest

/--
The preparatory work for applying a lemma from the library.
In this `search_tactic`, we just assemble the list of relevant lemmas,
and store them in the `thread`.

Later `apply_library_lemma` works through this list, one lemma at a time.
-/
meta def collect_library_lemmas : search_tactic thread ℕ :=
λ b S, do
  let D := S.data,
  guardb $ D.tried_solve_by_elim && D.library_allowed,
  g :: _ ← get_goals,
  t ← infer_type g,
  defs ← suggest.library_defs (head_symbol t),
  let D' : thread :=
  { queued_tactics := defs.map (λ d, suggest.apply_declaration ff { } d),
    library_allowed := ff,
    .. S.data },
  return (b+1, [{ data := D', .. S }])

end

meta def search_tactics : search_tactic thread ℕ :=
solve_terminal_goals + run_queued_tactic + collect_library_lemmas

end ariadne

meta def ariadne : tactic unit :=
tactic.ariadne.search_tactics.run_until (λ D n, n ≥ 10 ∨ D.num_goals = 0) >> skip

namespace interactive
meta def ariadne : itactic :=
tactic.ariadne
end interactive

end tactic

example {P Q : Prop} (h : P) (f : P → Q) : Q :=
begin
  ariadne,
end

constant P : Prop
constant Q : Prop
constant R : Prop
constant S : Prop
constant f : P → Q
constant g : Q → R → S

set_option trace.suggest true

example (p : P) (r : R) : S :=
begin
-- (do id ← mk_const `id, apply id), --suggest.apply_and_solve ff {} id),
  ariadne,
end

example {α : Type} (s t : set α) (a : α) (m : a ∈ s) (h : s ⊆ t) : a ∈ t :=
by ariadne
