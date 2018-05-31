/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import data.list.basic data.buffer

universes u w

namespace d_array
variables {n : nat} {α : fin n → Type u} {β : Type w}

instance [∀ i, inhabited (α i)] : inhabited (d_array n α) :=
⟨⟨λ _, default _⟩⟩

end d_array

namespace array
variables {n : nat} {α : Type u} {β : Type w}

instance [inhabited α] : inhabited (array n α) := d_array.inhabited

theorem rev_list_foldr_aux (a : array n α) (b : β) (f : α → β → β) :
  Π (i : nat) (h : i ≤ n), (d_array.iterate_aux a (λ _ v l, v :: l) i h []).foldr f b = d_array.iterate_aux a (λ _, f) i h b
| 0     h := rfl
| (j+1) h := congr_arg (f (read a ⟨j, h⟩)) (rev_list_foldr_aux j _)

theorem rev_list_foldr (a : array n α) (b : β) (f : α → β → β) : a.rev_list.foldr f b = a.foldl b f :=
rev_list_foldr_aux a b f _ _

theorem mem.def (v : α) (a : array n α) :
  v ∈ a ↔ ∃ i : fin n, read a i = v := iff.rfl

theorem rev_list_reverse_core (a : array n α) : Π i (h : i ≤ n) (t : list α),
  (a.iterate_aux (λ _ v l, v :: l) i h []).reverse_core t = a.rev_iterate_aux (λ _ v l, v :: l) i h t
| 0     h t := rfl
| (i+1) h t := rev_list_reverse_core i _ _

@[simp] theorem rev_list_reverse (a : array n α) : a.rev_list.reverse = a.to_list :=
rev_list_reverse_core a _ _ _

@[simp] theorem to_list_reverse (a : array n α) : a.to_list.reverse = a.rev_list :=
by rw [← rev_list_reverse, list.reverse_reverse]

theorem rev_list_length_aux (a : array n α) (i h) : (a.iterate_aux (λ _ v l, v :: l) i h []).length = i :=
by induction i; simp [*, d_array.iterate_aux]

@[simp] theorem rev_list_length (a : array n α) : a.rev_list.length = n :=
rev_list_length_aux a _ _

@[simp] theorem to_list_length (a : array n α) : a.to_list.length = n :=
by rw[← rev_list_reverse, list.length_reverse, rev_list_length]

theorem to_list_nth_le_core (a : array n α) (i : ℕ) (ih : i < n) : Π (j) {jh t h'},
  (∀k tl, j + k = i → list.nth_le t k tl = a.read ⟨i, ih⟩) → (a.rev_iterate_aux (λ _ v l, v :: l) j jh t).nth_le i h' = a.read ⟨i, ih⟩
| 0     _  _ _  al := al i _ $ zero_add _
| (j+1) jh t h' al := to_list_nth_le_core j $ λk tl hjk,
  show list.nth_le (a.read ⟨j, jh⟩ :: t) k tl = a.read ⟨i, ih⟩, from
  match k, hjk, tl with
  | 0,    e, tl := match i, e, ih with ._, rfl, _ := rfl end
  | k'+1, _, tl := by simp[list.nth_le]; exact al _ _ (by simp [*])
  end

theorem to_list_nth_le (a : array n α) (i : ℕ) (h h') : list.nth_le a.to_list i h' = a.read ⟨i, h⟩ :=
to_list_nth_le_core _ _ _ _ (λk tl, absurd tl $ nat.not_lt_zero _)

@[simp] theorem to_list_nth_le' (a : array n α) (i : fin n) (h') : list.nth_le a.to_list i.1 h' = a.read i :=
by cases i; apply to_list_nth_le

theorem to_list_nth {a : array n α} {i : ℕ} {v} : list.nth a.to_list i = some v ↔ ∃ h, a.read ⟨i, h⟩ = v :=
begin
  rw list.nth_eq_some,
  have ll := to_list_length a,
  split; intro h; cases h with h e; subst v,
  { exact ⟨ll ▸ h, (to_list_nth_le _ _ _ _).symm⟩ },
  { exact ⟨ll.symm ▸ h, to_list_nth_le _ _ _ _⟩ }
end

theorem to_list_foldl (a : array n α) (b : β) (f : β → α → β) : a.to_list.foldl f b = a.foldl b (function.swap f) :=
by rw [← rev_list_reverse, list.foldl_reverse, rev_list_foldr]

theorem write_to_list {a : array n α} {i v} : (a.write i v).to_list = a.to_list.update_nth i.1 v :=
list.ext_le (by simp) $ λ j h₁ h₂, begin
  have h₃ : j < n, {simpa using h₁},
  rw [to_list_nth_le _ _ h₃],
  refine let ⟨_, e⟩ := list.nth_eq_some.1 _ in e.symm,
  by_cases ij : i.1 = j,
  { subst j, rw [show fin.mk i.val h₃ = i, from fin.eq_of_veq rfl,
      array.read_write, list.nth_update_nth_of_lt],
    simp [h₃] },
  { rw [list.nth_update_nth_ne _ _ ij, a.read_write_of_ne,
        to_list_nth.2 ⟨h₃, rfl⟩],
    exact fin.ne_of_vne ij }
end

theorem mem_rev_list_core (a : array n α) (v : α) : Π i (h : i ≤ n),
  (∃ (j : fin n), j.1 < i ∧ read a j = v) ↔ v ∈ a.iterate_aux (λ _ v l, v :: l) i h []
| 0     _ := ⟨λ⟨_, n, _⟩, absurd n $ nat.not_lt_zero _, false.elim⟩
| (i+1) h := let IH := mem_rev_list_core i (le_of_lt h) in
  ⟨λ⟨j, ji1, e⟩, or.elim (lt_or_eq_of_le $ nat.le_of_succ_le_succ ji1)
    (λji, list.mem_cons_of_mem _ $ IH.1 ⟨j, ji, e⟩)
    (λje, by simp [d_array.iterate_aux]; apply or.inl; unfold read at e;
          have H : j = ⟨i, h⟩ := fin.eq_of_veq je; rwa [← H, e]),
  λm, begin
    simp [d_array.iterate_aux, list.mem] at m,
    cases m with e m',
    exact ⟨⟨i, h⟩, nat.lt_succ_self _, eq.symm e⟩,
    exact let ⟨j, ji, e⟩ := IH.2 m' in
    ⟨j, nat.le_succ_of_le ji, e⟩
  end⟩

@[simp] theorem mem_rev_list (a : array n α) (v : α) : v ∈ a.rev_list ↔ v ∈ a :=
iff.symm $ iff.trans
  (exists_congr $ λj, iff.symm $ show j.1 < n ∧ read a j = v ↔ read a j = v, from and_iff_right j.2)
  (mem_rev_list_core a v _ _)

@[simp] theorem mem_to_list (a : array n α) (v : α) : v ∈ a.to_list ↔ v ∈ a :=
by rw ← rev_list_reverse; simp [-rev_list_reverse]

theorem mem_to_list_enum (a : array n α) {i v} :
  (i, v) ∈ a.to_list.enum ↔ ∃ h, a.read ⟨i, h⟩ = v :=
by simp [list.mem_iff_nth, to_list_nth, and.comm, and.assoc, and.left_comm]

@[simp] theorem to_list_to_array (a : array n α) : a.to_list.to_array == a :=
heq_of_heq_of_eq
  (@@eq.drec_on (λ m (e : a.to_list.length = m), (d_array.mk (λv, a.to_list.nth_le v.1 v.2)) ==
    (@d_array.mk m (λ_, α) $ λv, a.to_list.nth_le v.1 $ e.symm ▸ v.2)) a.to_list_length heq.rfl) $
  d_array.ext $ λ⟨i, h⟩, to_list_nth_le _ i h _

@[simp] theorem to_array_to_list (l : list α) : l.to_array.to_list = l :=
list.ext_le (to_list_length _) $ λn h1 h2, to_list_nth_le _ _ _ _

lemma push_back_rev_list_core (a : array n α) (v : α) :
  ∀ i h h',
    d_array.iterate_aux (a.push_back v) (λ_, list.cons) i h [] =
    d_array.iterate_aux a (λ_, list.cons) i h' []
| 0 h h' := rfl
| (i+1) h h' := begin
  simp [d_array.iterate_aux],
  refine ⟨_, push_back_rev_list_core _ _ _⟩,
  dsimp [read, d_array.read, push_back],
  rw [dif_neg], refl,
  exact ne_of_lt h',
end

@[simp] theorem push_back_rev_list (a : array n α) (v : α) :
  (a.push_back v).rev_list = v :: a.rev_list :=
begin
  unfold push_back rev_list foldl iterate d_array.iterate,
  dsimp [d_array.iterate_aux, read, d_array.read, push_back],
  rw [dif_pos (eq.refl n)], apply congr_arg,
  apply push_back_rev_list_core
end

@[simp] theorem push_back_to_list (a : array n α) (v : α) :
  (a.push_back v).to_list = a.to_list ++ [v] :=
by rw [← rev_list_reverse, ← rev_list_reverse, push_back_rev_list,
       list.reverse_cons, list.concat_eq_append]

theorem read_foreach_aux (f : fin n → α → α) (ai : array n α) :
  ∀ i h (a : array n α) (j : fin n), j.1 < i →
    (d_array.iterate_aux ai (λ i v a', write a' i (f i v)) i h a).read j = f j (ai.read j)
| 0     hi a ⟨j, hj⟩ ji := absurd ji (nat.not_lt_zero _)
| (i+1) hi a ⟨j, hj⟩ ji := begin
  dsimp [d_array.iterate_aux], dsimp at ji,
  by_cases e : (⟨i, hi⟩ : fin _) = ⟨j, hj⟩,
  { rw [e], simp, refl },
  { rw [read_write_of_ne _ _ e, read_foreach_aux _ _ _ ⟨j, hj⟩],
    exact (lt_or_eq_of_le (nat.le_of_lt_succ ji)).resolve_right
      (ne.symm $ mt (@fin.eq_of_veq _ ⟨i, hi⟩ ⟨j, hj⟩) e) }
end

theorem read_foreach (a : array n α) (f : fin n → α → α) (i : fin n) :
  (foreach a f).read i = f i (a.read i) :=
read_foreach_aux _ _ _ _ _ _ i.2

theorem read_map (f : α → α) (a : array n α) (i : fin n) :
  (map f a).read i = f (a.read i) :=
read_foreach _ _ _

theorem read_map₂ (f : α → α → α) (a b : array n α) (i : fin n) :
  (map₂ f a b).read i = f (a.read i) (b.read i) :=
read_foreach _ _ _

end array

instance (α) [decidable_eq α] : decidable_eq (buffer α) :=
by tactic.mk_dec_eq_instance
