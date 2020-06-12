import order.lexicographic
import data.list.sort

/--
A `search_state α` represents an intermediate state in a proof search.
The type `α` represents data describing
the local state of the search.

A term `S : search_state α` has three fields:
* `S.data : α`, containing a description of the current state of the search.
* `S.tactic_state : tactic_state`, the internal Lean description of the current proof goals.
* `S.run : tactic (list (search_state α))`.
-/
meta inductive search_state (α β : Type)
| mk : α → tactic_state → (β → tactic (β × list search_state)) → search_state

namespace search_state

variables {α β : Type}

meta def data (S : search_state α β) : α :=
by { cases S with a s t, exact a }

meta def tactic_state (S : search_state α β) : tactic_state :=
by { cases S with a s t, exact s }

meta def run (S : search_state α β) (b : β) : tactic (β × list (search_state α β)) :=
by { cases S with a s t, exact t b }

end search_state

variables {α β : Type} [has_to_format α] [has_to_format β] [decidable_linear_order α]

-- Even though the function `search_state.data` is not injective, the priority queue should still work.
meta instance : decidable_linear_order (search_state α β) :=
decidable_linear_order.lift search_state.data undefined infer_instance

open tactic

meta def step (b : β) (Q : priority_queue (search_state α β)) :
  tactic (β × priority_queue (search_state α β)) :=
do
  (some S, T) ← pure (priority_queue.pull Q),
  set_state S.tactic_state,
  trace_state,
  (b', SS) ← S.run b,
  pure (b', T.insert_all SS)

meta def run_until (P : α → bool) :
  β → priority_queue (search_state α β) → tactic (β × search_state α β)
| b Q := do
  trace format!"global: {b}",
  trace format!"queue: {(Q.1.map (search_state.data))}",
  some S ← pure (priority_queue.peek Q) | fail "Exhausted all search states.",
  if P S.data then return (b, S) else
    do
      (b', Q') ← step b Q,
      run_until b' Q'

meta def search_state.search (P : α → bool) (b : β) (S : search_state α β) :
  tactic (search_state α β) :=
do
  (b, S) ← run_until P b (priority_queue.singleton S),
  set_state S.tactic_state,
  return S

meta def search_state.tactic_list
  (update_local : α → tactic α) (update_global : β → ℕ → β)
  (tacs : list (tactic unit)) : α → tactic (search_state α β)
| a := do
  s ← get_state,
  return $ search_state.mk a s
    (λ b, do
      r ← tacs.mmap_filter (λ t : tactic unit,
        try_core (do set_state s, t, a' ← update_local a, search_state.tactic_list a')),
      let b' := update_global b r.length,
      pure (b', r))

meta def ex : tactic (search_state ℕ ℕ) :=
search_state.tactic_list (λ n, num_goals) (+) [`[any_goals {exact 0}], `[exact []], `[split]] 1

example : (ℕ × list ℕ) × ℕ :=
begin
  (do S ← ex, S.search (λ n, n = 0) 0),
end

structure search_data :=
(num_goals : ℕ)
(steps : ℕ)

meta instance : has_to_format search_data :=
{ to_format := λ S, do format!"{(S.num_goals, S.steps)}" }

def search_data.zero : search_data :=
{ num_goals := 1,
  steps := 0, }

meta def search_data.update (x : search_data) : tactic search_data :=
do
  n ← num_goals,
  pure { num_goals := n, steps := x.steps + 1 }

def search_data.done (x : search_data) : bool :=
x.num_goals = 0

meta def search_data.breadth_first : decidable_linear_order search_data :=
decidable_linear_order.lift
  (λ x : search_data, (min x.num_goals 1, x.steps))
  undefined
  (by apply_instance : decidable_linear_order (lex ℕ ℕ))

meta def search_data.depth_first : decidable_linear_order search_data :=
decidable_linear_order.lift
  (λ x : search_data, (min x.num_goals 1, -(x.steps : ℤ)))
  undefined
  (by apply_instance : decidable_linear_order (lex ℕ ℤ))

meta def ex2 : tactic (search_state search_data ℕ) :=
search_state.tactic_list
  search_data.update (+)
  [`[refine ⟨0,_⟩], `[refine ⟨1,_⟩], `[refl]]
  search_data.zero


section
local attribute [instance] search_data.breadth_first

example : ∃ n m : ℕ, n = m :=
begin
  (do S ← ex2, S.search search_data.done 0),
end
end

section
local attribute [instance] search_data.depth_first

example : ∃ n m : ℕ, n = m :=
begin
  (do S ← ex2, S.search search_data.done 0),
end
end
