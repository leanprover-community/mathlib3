/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import logic.basic data.fin

variables {α : Type*}

namespace array

@[simp] lemma not_mem_nil (a : α) (x : array 0 α) : a ∉ x :=
λ ⟨i, _⟩, fin.elim0 i

lemma mem_of_mem_pop_back {n : ℕ} {a : α} {x : array (n+1) α} :
  a ∈ pop_back x → a ∈ x :=
λ ⟨⟨i, hin⟩, hi⟩, ⟨⟨i, nat.lt_succ_of_lt hin⟩, hi⟩

lemma mem_iff_mem_pop_back_or_read_last_eq {n : ℕ} (a : α) (x : array (n+1) α) :
  a ∈ x ↔ a ∈ pop_back x ∨ x.read (fin.last n) = a :=
⟨λ ⟨⟨i, hin⟩, hi⟩, (lt_or_eq_of_le (nat.le_of_lt_succ hin)).elim
    (λ hin : i < n, or.inl ⟨⟨i, hin⟩, hi⟩)
    (λ hin : i = n, or.inr $ by clear_aux_decl; subst hin; exact hi),
  λ h, h.elim mem_of_mem_pop_back (λ h, h ▸ read_mem _ _)⟩

instance mem_decidable [decidable_eq α] : Π {n : ℕ}
  (x : array n α), decidable_pred (∈ x)
| 0     x a := is_false (by simp)
| (n+1) x a := by letI := mem_decidable x.pop_back a;
  exact decidable_of_iff
    (x.read (fin.last n) = a ∨ (by resetI; exact a ∈ x.pop_back))
    (by rw [or.comm, ← mem_iff_mem_pop_back_or_read_last_eq])

end array
