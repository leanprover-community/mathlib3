import data.list

namespace list
variables {α : Type*}

lemma append_tail {l₁ l₂ : list α} (h : l₁ ≠ []) : (l₁ ++ l₂).tail = l₁.tail ++ l₂ :=
begin
  cases l₁,
  exact (h rfl).elim,
  simp [tail],
end

end list
