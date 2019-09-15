import data.list.sort

universes u

class priority_queue_ops (α Q : Type u) [decidable_linear_order α] :=
(size : Q → ℕ)
(insert : α → Q → Q)
(peek : Π (q : Q), 0 < size q → α)
(pull : Π (q : Q), 0 < size q → (α × Q))

class priority_queue (α Q : Type u) [decidable_linear_order α] extends priority_queue_ops α Q :=
(peek_eq_pull : ∀ (q : Q) (h : 0 < size q), peek q h = (pull q h).1)
(insert_size : ∀ (q : Q) (a : α), size (insert a q) = size q + 1)
(pull_size : ∀ (q : Q) (h : 0 < size q), size (pull q h).2 = size q - 1)
(count : α → Q → ℕ)
(pull_min : ∀ (q : Q) (h : 0 < size q) (a : α) (w : 0 < count a (pull q h).2), (pull q h).1 ≤ a)
(count_insert : ∀ (a b : α) (q : Q), count a (insert b q) = count a q + (if a = b then 1 else 0))
(count_pull : ∀ (a : α) (q : Q) (h : 0 < size q), count a (pull q h).2 = count a q - (if a = (pull q h).1 then 1 else 0))

instance (α : Type u) [decidable_linear_order α] : priority_queue α (Σ' L : list α, L.sorted (≤)) :=
{ size   := λ q, q.1.length,
  insert := λ a q, ⟨q.1.ordered_insert (≤) a, q.1.sorted_ordered_insert (≤) a q.2⟩,
  peek   := λ q h, q.1.nth_le 0 h,
  pull   := λ q h, (q.1.nth_le 0 h, ⟨q.1.tail, q.2.tail⟩),
  peek_eq_pull := λ q h, rfl,
  insert_size  := λ q a, q.1.ordered_insert_length (≤) a,
  pull_size    := λ L h, by simp,
  count        := λ a q, q.1.count a,
  pull_min     := λ q h a c, by { rcases q with ⟨_,_|⟨_,_,s⟩⟩, cases h, exact s a (list.count_pos.mp c), },
  count_insert := λ a b q, by simp [list.ordered_insert_count],
  count_pull   := λ a q h, by simp [h, list.count_tail] }
