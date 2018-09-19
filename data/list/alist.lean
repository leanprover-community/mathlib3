import data.list.sigma

universes u v w

structure alist {α : Type u} (β : α → Type v) : Type (max u v) :=
(val : list (sigma β))
(nd : val.knodup)

namespace alist
variables {α : Type u} {β : α → Type v}

instance : has_mem α (alist β) := ⟨λ a s, ∃ b : β a, sigma.mk a b ∈ s.val⟩

variables [decidable_eq α]

def lookup (a : α) (s : alist β) : option (β a) :=
s.val.lookup a

theorem lookup_is_some {a : α} {s : alist β} :
  (s.lookup a).is_some ↔ a ∈ s := list.lookup_is_some

instance (a : α) (s : alist β) : decidable (a ∈ s) :=
decidable_of_iff _ lookup_is_some

def replace (a : α) (b : β a) (s : alist β) : alist β :=
⟨list.kreplace a b s.val, (list.kreplace_knodup a b).2 s.nd⟩

/-- Fold a function over the key-value pairs in the map -/
def foldl {δ : Type w} (f : δ → Π a, β a → δ) (d : δ) (m : alist β) : δ :=
m.val.foldl (λ r a, f r a.1 a.2) d

end alist
