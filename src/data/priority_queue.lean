import data.list.sort

universes u

class priority_queue_ops (α Q : Type u) [decidable_linear_order α] :=
(empty : Q)
(size : Q → ℕ)
(insert : α → Q → Q)
(peek : Π (q : Q), with_bot α)
(pull : Π (q : Q), with_bot α × Q)

class priority_queue (α Q : Type u) [decidable_linear_order α] extends priority_queue_ops α Q :=
(empty_size : size empty = 0)
(peek_eq_pull : ∀ (q : Q), peek q = (pull q).1)
(insert_size : ∀ (q : Q) (a : α), size (insert a q) = size q + 1)
(peek_some : ∀ (q : Q), peek q = ⊥ ↔ size q = 0)
(pull_size : ∀ (q : Q), size (pull q).2 = size q - 1)
(count : α → Q → ℕ)
(pull_min : ∀ (q : Q) (a : α) (w : 0 < count a (pull q).2), peek q ≤ a)
(count_insert : ∀ (a b : α) (q : Q), count a (insert b q) = count a q + (if a = b then 1 else 0))
(count_pull : ∀ (a : α) (q : Q), count a (pull q).2 = count a q - (if (a : with_bot α) = (pull q).1 then 1 else 0))

attribute [simp] with_bot.coe_eq_coe with_bot.some_eq_coe with_bot.none_eq_bot

instance (α : Type u) [decidable_linear_order α] : priority_queue α (Σ' L : list α, L.sorted (≤)) :=
{ empty := ⟨[], list.sorted_nil⟩,
  empty_size := by simp,
  size   := λ q, q.1.length,
  insert := λ a q, ⟨q.1.ordered_insert (≤) a, q.1.sorted_ordered_insert (≤) a q.2⟩,
  peek   := λ q, q.1.nth 0,
  pull   := λ q, (q.1.nth 0, ⟨q.1.tail, q.2.tail⟩),
  peek_eq_pull := λ q, rfl,
  insert_size  := λ q a, q.1.ordered_insert_length (≤) a,
  peek_some    := λ q, begin cases q, cases q_fst, simp, simp, apply option.no_confusion, end,
  pull_size    := λ L, by simp,
  count        := λ a q, q.1.count a,
  pull_min     := λ q a c,
  begin
    rcases q with ⟨_,_|⟨_,_,s⟩⟩,
    { exact bot_le, },
    { erw with_bot.coe_le_coe,
      exact s a (list.count_pos.mp c), },
  end,
  count_insert := λ a b q, by simp [list.ordered_insert_count],
  count_pull   := λ a q,
  begin
    rcases q with ⟨⟨⟩|⟨b,q⟩, s⟩,
    { simp, },
    { simp only [list.count_cons, with_bot.coe_eq_coe, list.ordered_insert, list.length,
        with_bot.some_eq_coe, list.nth, list.tail, list.tail_cons],
      split_ifs; simp, },
  end }

namespace priority_queue_ops

def head {α Q : Type u} [decidable_linear_order α] [priority_queue α Q] (q : Q) (h : 0 < size α q) : α :=
sorry

end priority_queue_ops

open priority_queue_ops

def to_list_aux (α Q : Type u) [decidable_linear_order α] [priority_queue α Q] :
  Π (n : ℕ) (q : Q), n = size α q → list α → list α
| 0 q h L := L.reverse
| (n+1) q h L := to_list_aux n (pull q).2 sorry (head q sorry :: L)
