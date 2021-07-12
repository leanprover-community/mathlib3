/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.list.basic
import data.nat.choose.basic

/-! # sublists

`list.sublists` gives a list of all (not necessarily contiguous) sublists of a list.

This file contains basic results on this function.
-/

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}
open nat

namespace list

/-! ### sublists -/

@[simp] theorem sublists'_nil : sublists' (@nil α) = [[]] := rfl

@[simp, priority 1100] theorem sublists'_singleton (a : α) : sublists' [a] = [[], [a]] := rfl

theorem map_sublists'_aux (g : list β → list γ) (l : list α) (f r) :
  map g (sublists'_aux l f r) = sublists'_aux l (g ∘ f) (map g r) :=
by induction l generalizing f r; [refl, simp only [*, sublists'_aux]]

theorem sublists'_aux_append (r' : list (list β)) (l : list α) (f r) :
  sublists'_aux l f (r ++ r') = sublists'_aux l f r ++ r' :=
by induction l generalizing f r; [refl, simp only [*, sublists'_aux]]

theorem sublists'_aux_eq_sublists' (l f r) :
  @sublists'_aux α β l f r = map f (sublists' l) ++ r :=
by rw [sublists', map_sublists'_aux, ← sublists'_aux_append]; refl

@[simp] theorem sublists'_cons (a : α) (l : list α) :
  sublists' (a :: l) = sublists' l ++ map (cons a) (sublists' l) :=
by rw [sublists', sublists'_aux]; simp only [sublists'_aux_eq_sublists', map_id, append_nil]; refl

@[simp] theorem mem_sublists' {s t : list α} : s ∈ sublists' t ↔ s <+ t :=
begin
  induction t with a t IH generalizing s,
  { simp only [sublists'_nil, mem_singleton],
    exact ⟨λ h, by rw h, eq_nil_of_sublist_nil⟩ },
  simp only [sublists'_cons, mem_append, IH, mem_map],
  split; intro h, rcases h with h | ⟨s, h, rfl⟩,
  { exact sublist_cons_of_sublist _ h },
  { exact cons_sublist_cons _ h },
  { cases h with _ _ _ h s _ _ h,
    { exact or.inl h },
    { exact or.inr ⟨s, h, rfl⟩ } }
end

@[simp] theorem length_sublists' : ∀ l : list α, length (sublists' l) = 2 ^ length l
| []     := rfl
| (a::l) := by simp only [sublists'_cons, length_append, length_sublists' l, length_map,
    length, pow_succ', mul_succ, mul_zero, zero_add]

@[simp] theorem sublists_nil : sublists (@nil α) = [[]] := rfl

@[simp] theorem sublists_singleton (a : α) : sublists [a] = [[], [a]] := rfl

theorem sublists_aux₁_eq_sublists_aux : ∀ l (f : list α → list β),
  sublists_aux₁ l f = sublists_aux l (λ ys r, f ys ++ r)
| []     f := rfl
| (a::l) f := by rw [sublists_aux₁, sublists_aux]; simp only [*, append_assoc]

theorem sublists_aux_cons_eq_sublists_aux₁ (l : list α) :
  sublists_aux l cons = sublists_aux₁ l (λ x, [x]) :=
by rw [sublists_aux₁_eq_sublists_aux]; refl

theorem sublists_aux_eq_foldr.aux {a : α} {l : list α}
  (IH₁ : ∀ (f : list α → list β → list β), sublists_aux l f = foldr f [] (sublists_aux l cons))
  (IH₂ : ∀ (f : list α → list (list α) → list (list α)),
      sublists_aux l f = foldr f [] (sublists_aux l cons))
  (f : list α → list β → list β) : sublists_aux (a::l) f = foldr f [] (sublists_aux (a::l) cons) :=
begin
  simp only [sublists_aux, foldr_cons], rw [IH₂, IH₁], congr' 1,
  induction sublists_aux l cons with _ _ ih, {refl},
  simp only [ih, foldr_cons]
end

theorem sublists_aux_eq_foldr (l : list α) : ∀ (f : list α → list β → list β),
  sublists_aux l f = foldr f [] (sublists_aux l cons) :=
suffices _ ∧ ∀ f : list α → list (list α) → list (list α),
    sublists_aux l f = foldr f [] (sublists_aux l cons),
  from this.1,
begin
  induction l with a l IH, {split; intro; refl},
  exact ⟨sublists_aux_eq_foldr.aux IH.1 IH.2,
         sublists_aux_eq_foldr.aux IH.2 IH.2⟩
end

theorem sublists_aux_cons_cons (l : list α) (a : α) :
  sublists_aux (a::l) cons = [a] :: foldr (λys r, ys :: (a :: ys) :: r) [] (sublists_aux l cons) :=
by rw [← sublists_aux_eq_foldr]; refl

theorem sublists_aux₁_append : ∀ (l₁ l₂ : list α) (f : list α → list β),
  sublists_aux₁ (l₁ ++ l₂) f = sublists_aux₁ l₁ f ++
    sublists_aux₁ l₂ (λ x, f x ++ sublists_aux₁ l₁ (f ∘ (++ x)))
| []      l₂ f := by simp only [sublists_aux₁, nil_append, append_nil]
| (a::l₁) l₂ f := by simp only [sublists_aux₁, cons_append, sublists_aux₁_append l₁, append_assoc];
  refl

theorem sublists_aux₁_concat (l : list α) (a : α) (f : list α → list β) :
  sublists_aux₁ (l ++ [a]) f = sublists_aux₁ l f ++
    f [a] ++ sublists_aux₁ l (λ x, f (x ++ [a])) :=
by simp only [sublists_aux₁_append, sublists_aux₁, append_assoc, append_nil]

theorem sublists_aux₁_bind : ∀ (l : list α)
  (f : list α → list β) (g : β → list γ),
  (sublists_aux₁ l f).bind g = sublists_aux₁ l (λ x, (f x).bind g)
| []     f g := rfl
| (a::l) f g := by simp only [sublists_aux₁, bind_append, sublists_aux₁_bind l]

theorem sublists_aux_cons_append (l₁ l₂ : list α) :
  sublists_aux (l₁ ++ l₂) cons = sublists_aux l₁ cons ++
    (do x ← sublists_aux l₂ cons, (++ x) <$> sublists l₁) :=
begin
  simp only [sublists, sublists_aux_cons_eq_sublists_aux₁, sublists_aux₁_append, bind_eq_bind,
    sublists_aux₁_bind],
  congr, funext x, apply congr_arg _,
  rw [← bind_ret_eq_map, sublists_aux₁_bind], exact (append_nil _).symm
end

theorem sublists_append (l₁ l₂ : list α) :
  sublists (l₁ ++ l₂) = (do x ← sublists l₂, (++ x) <$> sublists l₁) :=
by simp only [map, sublists, sublists_aux_cons_append, map_eq_map, bind_eq_bind,
  cons_bind, map_id', append_nil, cons_append, map_id' (λ _, rfl)]; split; refl

@[simp] theorem sublists_concat (l : list α) (a : α) :
  sublists (l ++ [a]) = sublists l ++ map (λ x, x ++ [a]) (sublists l) :=
by rw [sublists_append, sublists_singleton, bind_eq_bind, cons_bind, cons_bind, nil_bind,
  map_eq_map, map_eq_map, map_id' (append_nil), append_nil]

theorem sublists_reverse (l : list α) : sublists (reverse l) = map reverse (sublists' l) :=
by induction l with hd tl ih; [refl,
simp only [reverse_cons, sublists_append, sublists'_cons, map_append, ih, sublists_singleton,
  map_eq_map, bind_eq_bind, map_map, cons_bind, append_nil, nil_bind, (∘)]]

theorem sublists_eq_sublists' (l : list α) : sublists l = map reverse (sublists' (reverse l)) :=
by rw [← sublists_reverse, reverse_reverse]

theorem sublists'_reverse (l : list α) : sublists' (reverse l) = map reverse (sublists l) :=
by simp only [sublists_eq_sublists', map_map, map_id' (reverse_reverse)]

theorem sublists'_eq_sublists (l : list α) : sublists' l = map reverse (sublists (reverse l)) :=
by rw [← sublists'_reverse, reverse_reverse]

theorem sublists_aux_ne_nil : ∀ (l : list α), [] ∉ sublists_aux l cons
| [] := id
| (a::l) := begin
  rw [sublists_aux_cons_cons],
  refine not_mem_cons_of_ne_of_not_mem (cons_ne_nil _ _).symm _,
  have := sublists_aux_ne_nil l, revert this,
  induction sublists_aux l cons; intro, {rwa foldr},
  simp only [foldr, mem_cons_iff, false_or, not_or_distrib],
  exact ⟨ne_of_not_mem_cons this, ih (not_mem_of_not_mem_cons this)⟩
end

@[simp] theorem mem_sublists {s t : list α} : s ∈ sublists t ↔ s <+ t :=
by rw [← reverse_sublist_iff, ← mem_sublists',
       sublists'_reverse, mem_map_of_injective reverse_injective]

@[simp] theorem length_sublists (l : list α) : length (sublists l) = 2 ^ length l :=
by simp only [sublists_eq_sublists', length_map, length_sublists', length_reverse]

theorem map_ret_sublist_sublists (l : list α) : map list.ret l <+ sublists l :=
reverse_rec_on l (nil_sublist _) $
λ l a IH, by simp only [map, map_append, sublists_concat]; exact
((append_sublist_append_left _).2 $ singleton_sublist.2 $
  mem_map.2 ⟨[], mem_sublists.2 (nil_sublist _), by refl⟩).trans
((append_sublist_append_right _).2 IH)

/-! ### sublists_len -/

/-- Auxiliary function to construct the list of all sublists of a given length. Given an
integer `n`, a list `l`, a function `f` and an auxiliary list `L`, it returns the list made of
of `f` applied to all sublists of `l` of length `n`, concatenated with `L`. -/
def sublists_len_aux {α β : Type*} : ℕ → list α → (list α → β) → list β → list β
| 0     l      f r := f [] :: r
| (n+1) []     f r := r
| (n+1) (a::l) f r := sublists_len_aux (n + 1) l f
  (sublists_len_aux n l (f ∘ list.cons a) r)

/-- The list of all sublists of a list `l` that are of length `n`. For instance, for
`l = [0, 1, 2, 3]` and `n = 2`, one gets
`[[2, 3], [1, 3], [1, 2], [0, 3], [0, 2], [0, 1]]`. -/
def sublists_len {α : Type*} (n : ℕ) (l : list α) : list (list α) :=
sublists_len_aux n l id []

lemma sublists_len_aux_append {α β γ : Type*} :
  ∀ (n : ℕ) (l : list α) (f : list α → β) (g : β → γ) (r : list β) (s : list γ),
  sublists_len_aux n l (g ∘ f) (r.map g ++ s) =
  (sublists_len_aux n l f r).map g ++ s
| 0     l      f g r s := rfl
| (n+1) []     f g r s := rfl
| (n+1) (a::l) f g r s := begin
  unfold sublists_len_aux,
  rw [show ((g ∘ f) ∘ list.cons a) = (g ∘ f ∘ list.cons a), by refl,
    sublists_len_aux_append, sublists_len_aux_append]
end

lemma sublists_len_aux_eq {α β : Type*} (l : list α) (n) (f : list α → β) (r) :
  sublists_len_aux n l f r = (sublists_len n l).map f ++ r :=
by rw [sublists_len, ← sublists_len_aux_append]; refl

lemma sublists_len_aux_zero {α : Type*} (l : list α) (f : list α → β) (r) :
  sublists_len_aux 0 l f r = f [] :: r := by cases l; refl

@[simp] lemma sublists_len_zero {α : Type*} (l : list α) :
  sublists_len 0 l = [[]] := sublists_len_aux_zero _ _ _

@[simp] lemma sublists_len_succ_nil {α : Type*} (n) :
  sublists_len (n+1) (@nil α) = [] := rfl

@[simp] lemma sublists_len_succ_cons {α : Type*} (n) (a : α) (l) :
  sublists_len (n + 1) (a::l) =
  sublists_len (n + 1) l ++ (sublists_len n l).map (cons a) :=
by rw [sublists_len, sublists_len_aux, sublists_len_aux_eq,
  sublists_len_aux_eq, map_id, append_nil]; refl

@[simp] lemma length_sublists_len {α : Type*} : ∀ n (l : list α),
  length (sublists_len n l) = nat.choose (length l) n
| 0     l      := by simp
| (n+1) []     := by simp
| (n+1) (a::l) := by simp [-add_comm, nat.choose, *]; apply add_comm

lemma sublists_len_sublist_sublists' {α : Type*} : ∀ n (l : list α),
  sublists_len n l <+ sublists' l
| 0     l      := singleton_sublist.2 (mem_sublists'.2 (nil_sublist _))
| (n+1) []     := nil_sublist _
| (n+1) (a::l) := begin
  rw [sublists_len_succ_cons, sublists'_cons],
  exact (sublists_len_sublist_sublists' _ _).append
    ((sublists_len_sublist_sublists' _ _).map _)
end

lemma sublists_len_sublist_of_sublist
  {α : Type*} (n) {l₁ l₂ : list α} (h : l₁ <+ l₂) : sublists_len n l₁ <+ sublists_len n l₂ :=
begin
  induction n with n IHn generalizing l₁ l₂, {simp},
  induction h with l₁ l₂ a s IH l₁ l₂ a s IH, {refl},
  { refine IH.trans _,
    rw sublists_len_succ_cons,
    apply sublist_append_left },
  { simp [sublists_len_succ_cons],
    exact IH.append ((IHn s).map _) }
end

lemma length_of_sublists_len {α : Type*} : ∀ {n} {l l' : list α},
  l' ∈ sublists_len n l → length l' = n
| 0     l      l' (or.inl rfl) := rfl
| (n+1) (a::l) l' h := begin
  rw [sublists_len_succ_cons, mem_append, mem_map] at h,
  rcases h with h | ⟨l', h, rfl⟩,
  { exact length_of_sublists_len h },
  { exact congr_arg (+1) (length_of_sublists_len h) },
end

lemma mem_sublists_len_self {α : Type*} {l l' : list α}
  (h : l' <+ l) : l' ∈ sublists_len (length l') l :=
begin
  induction h with l₁ l₂ a s IH l₁ l₂ a s IH,
  { exact or.inl rfl },
  { cases l₁ with b l₁,
    { exact or.inl rfl },
    { rw [length, sublists_len_succ_cons],
      exact mem_append_left _ IH } },
  { rw [length, sublists_len_succ_cons],
    exact mem_append_right _ (mem_map.2 ⟨_, IH, rfl⟩) }
end

@[simp] lemma mem_sublists_len {α : Type*} {n} {l l' : list α} :
  l' ∈ sublists_len n l ↔ l' <+ l ∧ length l' = n :=
⟨λ h, ⟨mem_sublists'.1
    ((sublists_len_sublist_sublists' _ _).subset h),
  length_of_sublists_len h⟩,
λ ⟨h₁, h₂⟩, h₂ ▸ mem_sublists_len_self h₁⟩

end list
