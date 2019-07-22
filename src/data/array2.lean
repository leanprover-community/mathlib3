/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import logic.basic data.fin

universes u v

namespace d_array

variables {n : ℕ} {α : fin n → Type u} {β : Type v}

def foreach_aux (a : d_array n α) (f : Π i : fin n, α i → α i)
  (i : ℕ) (hi : i ≤ n) : d_array n α :=
a.iterate_aux (λ i v (a' : d_array n α), a'.write i (f i v)) i hi a

lemma foreach_aux_succ (a : d_array n α) (f : Π i : fin n, α i → α i)
  (i : ℕ) (hi : (i + 1) ≤ n) :
a.foreach_aux f (i + 1) hi = (a.foreach_aux f i (nat.le_of_succ_le hi)).write
  ⟨i, hi⟩ (f _ (a.read _)) := rfl

lemma read_foreach_aux (a : d_array n α) (f : Π i : fin n, α i → α i) :
 Π (i : ℕ) (hi : i ≤ n) (j : ℕ) (hj : j < i),
  (a.foreach_aux f i hi).read ⟨j, lt_of_lt_of_le hj hi⟩ =
    f ⟨j, lt_of_lt_of_le hj hi⟩ (a.read _)
| 0 hi j hj := (nat.not_lt_zero _ hj).elim
| (i+1) hi j hj :=
  if hij : i = j
    then begin
        subst hij,
        erw [foreach_aux_succ, read_write],
        refl
      end
    else
    have j < i, from lt_of_le_of_ne (nat.le_of_lt_succ hj) (ne.symm hij),
    by rw [foreach_aux_succ, read_write_of_ne _ _
      (show fin.mk i hi ≠ ⟨j, _⟩, from fin.ne_of_vne hij), read_foreach_aux _ _ _ this]

@[simp] lemma read_foreach (a : d_array n α) (f : Π i : fin n, α i → α i) (i : fin n) :
  read (a.foreach f) i = f i (a.read i) :=
by cases i with i hi; exact read_foreach_aux a f n (le_refl n) i hi

end d_array

namespace array

variables {n : ℕ} {α : Type*}

@[simp] lemma read_foreach  (x : array n α)
  (f : Π i : fin n, α → α) (i : fin n) :
  (x.foreach f).read i = f i (x.read i) :=
d_array.read_foreach x _ _

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
