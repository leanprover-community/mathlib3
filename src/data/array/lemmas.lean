/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import control.traversable.equiv
import data.vector.basic

universes u v w

namespace d_array
variables {n : ℕ} {α : fin n → Type u}

instance [∀ i, inhabited (α i)] : inhabited (d_array n α) :=
⟨⟨λ _, default _⟩⟩

end d_array

namespace array

instance {n α} [inhabited α] : inhabited (array n α) :=
d_array.inhabited

theorem to_list_of_heq {n₁ n₂ α} {a₁ : array n₁ α} {a₂ : array n₂ α}
  (hn : n₁ = n₂) (ha : a₁ == a₂) : a₁.to_list = a₂.to_list :=
by congr; assumption

/- rev_list -/

section rev_list
variables {n : ℕ} {α : Type u} {a : array n α}

theorem rev_list_reverse_aux : ∀ i (h : i ≤ n) (t : list α),
  (a.iterate_aux (λ _, (::)) i h []).reverse_core t = a.rev_iterate_aux (λ _, (::)) i h t
| 0     h t := rfl
| (i+1) h t := rev_list_reverse_aux i _ _

@[simp] theorem rev_list_reverse : a.rev_list.reverse = a.to_list :=
rev_list_reverse_aux _ _ _

@[simp] theorem to_list_reverse : a.to_list.reverse = a.rev_list :=
by rw [←rev_list_reverse, list.reverse_reverse]

end rev_list

/- mem -/

section mem
variables {n : ℕ} {α : Type u} {v : α} {a : array n α}

theorem mem.def : v ∈ a ↔ ∃ i, a.read i = v :=
iff.rfl

theorem mem_rev_list_aux : ∀ {i} (h : i ≤ n),
  (∃ (j : fin n), (j : ℕ) < i ∧ read a j = v) ↔ v ∈ a.iterate_aux (λ _, (::)) i h []
| 0     _ := ⟨λ ⟨i, n, _⟩, absurd n i.val.not_lt_zero, false.elim⟩
| (i+1) h := let IH := mem_rev_list_aux (le_of_lt h) in
  ⟨λ ⟨j, ji1, e⟩, or.elim (lt_or_eq_of_le $ nat.le_of_succ_le_succ ji1)
    (λ ji, list.mem_cons_of_mem _ $ IH.1 ⟨j, ji, e⟩)
    (λ je, by simp [d_array.iterate_aux]; apply or.inl; unfold read at e;
          have H : j = ⟨i, h⟩ := fin.eq_of_veq je; rwa [←H, e]),
  λ m, begin
    simp [d_array.iterate_aux, list.mem] at m,
    cases m with e m',
    exact ⟨⟨i, h⟩, nat.lt_succ_self _, eq.symm e⟩,
    exact let ⟨j, ji, e⟩ := IH.2 m' in
    ⟨j, nat.le_succ_of_le ji, e⟩
  end⟩

@[simp] theorem mem_rev_list : v ∈ a.rev_list ↔ v ∈ a :=
iff.symm $ iff.trans
  (exists_congr $ λ j, iff.symm $
    show j.1 < n ∧ read a j = v ↔ read a j = v,
    from and_iff_right j.2)
  (mem_rev_list_aux _)

@[simp] theorem mem_to_list : v ∈ a.to_list ↔ v ∈ a :=
by rw ←rev_list_reverse; exact list.mem_reverse.trans mem_rev_list

end mem

/- foldr -/

section foldr
variables {n : ℕ} {α : Type u} {β : Type w} {b : β} {f : α → β → β} {a : array n α}

theorem rev_list_foldr_aux : ∀ {i} (h : i ≤ n),
  (d_array.iterate_aux a (λ _, (::)) i h []).foldr f b = d_array.iterate_aux a (λ _, f) i h b
| 0     h := rfl
| (j+1) h := congr_arg (f (read a ⟨j, h⟩)) (rev_list_foldr_aux _)

theorem rev_list_foldr : a.rev_list.foldr f b = a.foldl b f :=
rev_list_foldr_aux _

end foldr

/- foldl -/

section foldl
variables {n : ℕ} {α : Type u} {β : Type w} {b : β} {f : β → α → β} {a : array n α}

theorem to_list_foldl : a.to_list.foldl f b = a.foldl b (function.swap f) :=
by rw [←rev_list_reverse, list.foldl_reverse, rev_list_foldr]

end foldl

/- length -/

section length
variables {n : ℕ} {α : Type u}

theorem rev_list_length_aux (a : array n α) (i h) :
  (a.iterate_aux (λ _, (::)) i h []).length = i :=
by induction i; simp [*, d_array.iterate_aux]

@[simp] theorem rev_list_length (a : array n α) : a.rev_list.length = n :=
rev_list_length_aux a _ _

@[simp] theorem to_list_length (a : array n α) : a.to_list.length = n :=
by rw[←rev_list_reverse, list.length_reverse, rev_list_length]

end length

/- nth -/

section nth
variables {n : ℕ} {α : Type u} {a : array n α}

theorem to_list_nth_le_aux (i : ℕ) (ih : i < n) : ∀ j {jh t h'},
  (∀ k tl, j + k = i → list.nth_le t k tl = a.read ⟨i, ih⟩) →
  (a.rev_iterate_aux (λ _, (::)) j jh t).nth_le i h' = a.read ⟨i, ih⟩
| 0     _  _ _  al := al i _ $ zero_add _
| (j+1) jh t h' al := to_list_nth_le_aux j $ λ k tl hjk,
  show list.nth_le (a.read ⟨j, jh⟩ :: t) k tl = a.read ⟨i, ih⟩, from
  match k, hjk, tl with
  | 0,    e, tl := match i, e, ih with ._, rfl, _ := rfl end
  | k'+1, _, tl := by simp[list.nth_le]; exact al _ _ (by simp [add_comm, add_assoc, *]; cc)
  end

theorem to_list_nth_le (i : ℕ) (h h') : list.nth_le a.to_list i h' = a.read ⟨i, h⟩ :=
to_list_nth_le_aux _ _ _ (λ k tl, absurd tl k.not_lt_zero)

@[simp] theorem to_list_nth_le' (a : array n α) (i : fin n) (h') :
  list.nth_le a.to_list i h' = a.read i :=
by cases i; apply to_list_nth_le

theorem to_list_nth {i v} : list.nth a.to_list i = some v ↔ ∃ h, a.read ⟨i, h⟩ = v :=
begin
  rw list.nth_eq_some,
  have ll := to_list_length a,
  split; intro h; cases h with h e; subst v,
  { exact ⟨ll ▸ h, (to_list_nth_le _ _ _).symm⟩ },
  { exact ⟨ll.symm ▸ h, to_list_nth_le _ _ _⟩ }
end

theorem write_to_list {i v} : (a.write i v).to_list = a.to_list.update_nth i v :=
list.ext_le (by simp) $ λ j h₁ h₂, begin
  have h₃ : j < n, {simpa using h₁},
  rw [to_list_nth_le _ h₃],
  refine let ⟨_, e⟩ := list.nth_eq_some.1 _ in e.symm,
  by_cases ij : (i : ℕ) = j,
  { subst j, rw [show (⟨(i : ℕ), h₃⟩ : fin _) = i, from fin.eq_of_veq rfl,
      array.read_write, list.nth_update_nth_of_lt],
    simp [h₃] },
  { rw [list.nth_update_nth_ne _ _ ij, a.read_write_of_ne,
        to_list_nth.2 ⟨h₃, rfl⟩],
    exact fin.ne_of_vne ij }
end

end nth

/- enum -/

section enum
variables {n : ℕ} {α : Type u} {a : array n α}

theorem mem_to_list_enum {i v} : (i, v) ∈ a.to_list.enum ↔ ∃ h, a.read ⟨i, h⟩ = v :=
by simp [list.mem_iff_nth, to_list_nth, and.comm, and.assoc, and.left_comm]

end enum

/- to_array -/

section to_array
variables {n : ℕ} {α : Type u}

@[simp] theorem to_list_to_array (a : array n α) : a.to_list.to_array == a :=
heq_of_heq_of_eq
  (@@eq.drec_on (λ m (e : a.to_list.length = m), (d_array.mk (λ v, a.to_list.nth_le v.1 v.2)) ==
    (@d_array.mk m (λ _, α) $ λ v, a.to_list.nth_le v.1 $ e.symm ▸ v.2)) a.to_list_length heq.rfl) $
  d_array.ext $ λ ⟨i, h⟩, to_list_nth_le i h _

@[simp] theorem to_array_to_list (l : list α) : l.to_array.to_list = l :=
list.ext_le (to_list_length _) $ λ n h1 h2, to_list_nth_le _ h2 _

end to_array

/- push_back -/

section push_back
variables {n : ℕ} {α : Type u} {v : α} {a : array n α}

lemma push_back_rev_list_aux : ∀ i h h',
  d_array.iterate_aux (a.push_back v) (λ _, (::)) i h [] = d_array.iterate_aux a (λ _, (::)) i h' []
| 0 h h' := rfl
| (i+1) h h' := begin
  simp [d_array.iterate_aux],
  refine ⟨_, push_back_rev_list_aux _ _ _⟩,
  dsimp [read, d_array.read, push_back],
  rw [dif_neg], refl,
  exact ne_of_lt h',
end

@[simp] theorem push_back_rev_list : (a.push_back v).rev_list = v :: a.rev_list :=
begin
  unfold push_back rev_list foldl iterate d_array.iterate,
  dsimp [d_array.iterate_aux, read, d_array.read, push_back],
  rw [dif_pos (eq.refl n)],
  apply congr_arg,
  apply push_back_rev_list_aux
end

@[simp] theorem push_back_to_list : (a.push_back v).to_list = a.to_list ++ [v] :=
by rw [←rev_list_reverse, ←rev_list_reverse, push_back_rev_list, list.reverse_cons]

@[simp] lemma read_push_back_left (i : fin n) : (a.push_back v).read i.cast_succ = a.read i :=
begin
  cases i with i hi,
  have : ¬ i = n := ne_of_lt hi,
  simp [push_back, this, fin.cast_succ, fin.cast_add, fin.cast_le, fin.cast_lt, read, d_array.read]
end

@[simp] lemma read_push_back_right : (a.push_back v).read (fin.last _) = v :=
begin
  cases hn : fin.last n with k hk,
  have : k = n := by simpa [fin.eq_iff_veq ] using hn.symm,
  simp [push_back, this, fin.cast_succ, fin.cast_add, fin.cast_le, fin.cast_lt, read, d_array.read]
end

end push_back

/- foreach -/

section foreach
variables {n : ℕ} {α : Type u} {β : Type v} {i : fin n} {f : fin n → α → β} {a : array n α}

@[simp] theorem read_foreach : (foreach a f).read i = f i (a.read i) :=
rfl

end foreach

/- map -/

section map
variables {n : ℕ} {α : Type u} {β : Type v} {i : fin n} {f : α → β} {a : array n α}

theorem read_map : (a.map f).read i = f (a.read i) :=
read_foreach

end map

/- map₂ -/

section map₂
variables {n : ℕ} {α : Type u} {i : fin n} {f : α → α → α} {a₁ a₂ : array n α}

@[simp] theorem read_map₂ : (map₂ f a₁ a₂).read i = f (a₁.read i) (a₂.read i) :=
read_foreach

end map₂

end array

namespace equiv

/-- The natural equivalence between length-`n` heterogeneous arrays
and dependent functions from `fin n`. -/
def d_array_equiv_fin {n : ℕ} (α : fin n → Type*) : d_array n α ≃ (Π i, α i) :=
⟨d_array.read, d_array.mk, λ ⟨f⟩, rfl, λ f, rfl⟩

/-- The natural equivalence between length-`n` arrays and functions from `fin n`. -/
def array_equiv_fin (n : ℕ) (α : Type*) : array n α ≃ (fin n → α) :=
d_array_equiv_fin _

/-- The natural equivalence between length-`n` vectors and length-`n` arrays. -/
def vector_equiv_array (α : Type*) (n : ℕ) : vector α n ≃ array n α :=
(vector_equiv_fin _ _).trans (array_equiv_fin _ _).symm

end equiv

namespace array
open function
variable {n : ℕ}

instance : traversable (array n) :=
@equiv.traversable (flip vector n) _ (λ α, equiv.vector_equiv_array α n) _

instance : is_lawful_traversable (array n) :=
@equiv.is_lawful_traversable (flip vector n) _ (λ α, equiv.vector_equiv_array α n) _ _

end array
