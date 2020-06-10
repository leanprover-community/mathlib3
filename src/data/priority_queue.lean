import data.list.sort

universes u

def priority_queue (α : Type u) [preorder α] := Σ' L : list α, L.sorted (≤)

namespace priority_queue
variables {α : Type u} [decidable_linear_order α]

def insert (a : α) (q : priority_queue α) : priority_queue α :=
⟨q.1.ordered_insert (≤) a, q.1.sorted_ordered_insert (≤) a q.2⟩

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
begin
  cases S with a s t,
  exact a
end

meta def tactic_state {α : Type} (S : search_state α) : tactic_state :=
begin
  cases S with a s t,
  exact s
end

meta def run {α : Type} (S : search_state α) : tactic (list (search_state α)) :=
begin
  cases S with a s t,
  exact t
end

end search_state

meta instance {α : Type} [decidable_linear_order α] : decidable_linear_order (search_state α) :=
begin
exact decidable_linear_order.lift (@search_state.data α) sorry infer_instance,
end

def step {α : Type} [decidable_linear_order α] (Q : priority_queue (search_state α))
