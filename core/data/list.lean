
namespace list

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

instance [decidable_eq α] : has_sdiff (list α) :=
⟨ list.diff ⟩

/- partition -/

def partition_map (f : α → β ⊕ γ) : list α → list β × list γ
| [] := ([],[])
| (x::xs) :=
match f x with
| (sum.inr r) := prod.map id (cons r) $ partition_map xs
| (sum.inl l) := prod.map (cons l) id $ partition_map xs
end

end list
