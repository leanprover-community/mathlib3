import data.list.sort

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
