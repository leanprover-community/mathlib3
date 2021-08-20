/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import data.list

/-!
# Move these somewhere
-/

namespace list
variables {α : Type*}

lemma append_tail {l₁ l₂ : list α} (h : l₁ ≠ []) : (l₁ ++ l₂).tail = l₁.tail ++ l₂ :=
begin
  cases l₁,
  exact (h rfl).elim,
  simp [tail],
end

lemma is_rotated_append {l₁ l₂ : list α} : (l₁ ++ l₂) ~r (l₂ ++ l₁) :=
begin
  use l₁.length,
  rw rotate_eq_rotate',
  induction l₁ generalizing l₂,
  { simp, },
  { simp [rotate', l₁_ih], },
end

end list
