import data.list.sort
import meta.uchange

universes u

def priority_queue (α : Type u) [preorder α] := Σ' L : list α, L.sorted (≤)

namespace priority_queue
variables {α : Type u} [decidable_linear_order α]

def singleton (a : α) : priority_queue α :=
⟨[a], list.sorted_singleton _⟩

def insert (a : α) (q : priority_queue α) : priority_queue α :=
⟨q.1.ordered_insert (≤) a, q.1.sorted_ordered_insert (≤) a q.2⟩

def insert_all (L : list α) (q : priority_queue α) : priority_queue α :=
L.foldl (λ q a, insert a q) q

def peek (q : priority_queue α) : with_bot α :=
q.1.nth 0

def pull (q : priority_queue α) : with_bot α × priority_queue α :=
(q.1.nth 0, ⟨q.1.tail, q.2.tail⟩)

def size (q : priority_queue α) : ℕ := q.1.length

lemma insert_size {a : α} {q : priority_queue α} : (q.insert a).size = q.size + 1 :=
q.1.ordered_insert_length (≤) a

  -- peek_some    := λ q, begin cases q, cases q_fst, simp, simp, apply option.no_confusion, end,
  -- pull_size    := λ L, by simp,
  -- count        := λ a q, q.1.count a,
  -- pull_min     := λ q a c,
  -- begin
  --   rcases q with ⟨_,_|⟨_,_,s⟩⟩,
  --   { exact bot_le, },
  --   { erw with_bot.coe_le_coe,
  --     exact s a (list.count_pos.mp c), },
  -- end,
  -- count_insert := λ a b q, by simp [list.ordered_insert_count],
  -- count_pull   := λ a q,
  -- begin
  --   rcases q with ⟨⟨⟩|⟨b,q⟩, s⟩,
  --   { simp, },
  --   { simp only [list.count_cons, with_bot.coe_eq_coe, list.ordered_insert, list.length,
  --       with_bot.some_eq_coe, list.nth, list.tail, list.tail_cons],
  --     split_ifs; simp, },

end priority_queue

meta inductive search_state (α : Type)
| mk : α → tactic_state → tactic (list search_state) → search_state

namespace search_state

meta def data {α : Type} (S : search_state α) : α :=
by { cases S with a s t, exact a }

meta def tactic_state {α : Type} (S : search_state α) : tactic_state :=
by { cases S with a s t, exact s }

meta def run {α : Type} (S : search_state α) : tactic (list (search_state α)) :=
by { cases S with a s t, exact t }

end search_state

variables {α : Type} [decidable_linear_order α]

-- Even though the function `search_state.data` is not injective, the priority queue should still work.
meta instance : decidable_linear_order (search_state α) :=
decidable_linear_order.lift (@search_state.data _) (unchecked_cast' false) infer_instance

open tactic

meta def step (Q : priority_queue (search_state α)) :
  tactic (priority_queue (search_state α)) :=
do
  (some S, T) ← pure (priority_queue.pull Q),
  SS ← S.run,
  pure (T.insert_all SS)

meta def run_until (P : α → bool) :
  priority_queue (search_state α) → tactic (search_state α)
| Q := do
  some S ← pure (priority_queue.peek Q) | fail "Exhausted all search states.",
  if P S.data then return S else
    do
      Q' ← step Q,
      run_until Q'

meta def search_state.search (S : search_state α) (P : α → bool) :
  tactic (search_state α) :=
run_until P (priority_queue.singleton S)

meta def search_state.tactic_list {α : Type*} (update : α → tactic α) (tacs : list (tactic unit)) : α → tactic (search_state α)
| a := do
  s ← get_state,
  return $ search_state.mk a s
    (tacs.mmap_filter (λ t, try_core (do t, a' ← update a, search_state.tactic_list a')))

meta def ex : tactic (search_state ℕ) :=
search_state.tactic_list (λ n, num_goals) [`[exact 0], `[exact []], `[split]] 1

example : ℕ × list ℕ :=
begin
  (do S ← ex, S.search (λ n, n = 0)),
end
