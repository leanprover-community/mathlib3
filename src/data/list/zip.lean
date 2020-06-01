/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
import data.list.basic

universes u v w z

variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type z}

open nat

namespace list

/- zip & unzip -/

@[simp] theorem zip_cons_cons (a : α) (b : β) (l₁ : list α) (l₂ : list β) :
  zip (a :: l₁) (b :: l₂) = (a, b) :: zip l₁ l₂ := rfl

@[simp] theorem zip_nil_left (l : list α) : zip ([] : list β) l = [] := rfl

@[simp] theorem zip_nil_right (l : list α) : zip l ([] : list β) = [] :=
by cases l; refl

@[simp] theorem zip_swap : ∀ (l₁ : list α) (l₂ : list β),
  (zip l₁ l₂).map prod.swap = zip l₂ l₁
| []      l₂      := (zip_nil_right _).symm
| l₁      []      := by rw zip_nil_right; refl
| (a::l₁) (b::l₂) := by simp only [zip_cons_cons, map_cons, zip_swap l₁ l₂, prod.swap_prod_mk];
    split; refl

@[simp] theorem length_zip : ∀ (l₁ : list α) (l₂ : list β),
   length (zip l₁ l₂) = min (length l₁) (length l₂)
| []      l₂      := rfl
| l₁      []      := by simp only [length, zip_nil_right, min_zero]
| (a::l₁) (b::l₂) := by by simp only [length, zip_cons_cons, length_zip l₁ l₂, min_add_add_right]

theorem zip_append : ∀ {l₁ l₂ r₁ r₂ : list α} (h : length l₁ = length l₂),
   zip (l₁ ++ r₁) (l₂ ++ r₂) = zip l₁ l₂ ++ zip r₁ r₂
| []      l₂      r₁ r₂ h := by simp only [eq_nil_of_length_eq_zero h.symm]; refl
| l₁      []      r₁ r₂ h := by simp only [eq_nil_of_length_eq_zero h]; refl
| (a::l₁) (b::l₂) r₁ r₂ h := by simp only [cons_append, zip_cons_cons, zip_append (succ_inj h)];
    split; refl

theorem zip_map (f : α → γ) (g : β → δ) : ∀ (l₁ : list α) (l₂ : list β),
   zip (l₁.map f) (l₂.map g) = (zip l₁ l₂).map (prod.map f g)
| []      l₂      := rfl
| l₁      []      := by simp only [map, zip_nil_right]
| (a::l₁) (b::l₂) := by simp only [map, zip_cons_cons, zip_map l₁ l₂, prod.map]; split; refl

theorem zip_map_left (f : α → γ) (l₁ : list α) (l₂ : list β) :
   zip (l₁.map f) l₂ = (zip l₁ l₂).map (prod.map f id) :=
by rw [← zip_map, map_id]

theorem zip_map_right (f : β → γ) (l₁ : list α) (l₂ : list β) :
   zip l₁ (l₂.map f) = (zip l₁ l₂).map (prod.map id f) :=
by rw [← zip_map, map_id]

theorem zip_map' (f : α → β) (g : α → γ) : ∀ (l : list α),
   zip (l.map f) (l.map g) = l.map (λ a, (f a, g a))
| []     := rfl
| (a::l) := by simp only [map, zip_cons_cons, zip_map' l]; split; refl

theorem mem_zip {a b} : ∀ {l₁ : list α} {l₂ : list β},
   (a, b) ∈ zip l₁ l₂ → a ∈ l₁ ∧ b ∈ l₂
| (_::l₁) (_::l₂) (or.inl rfl) := ⟨or.inl rfl, or.inl rfl⟩
| (a'::l₁) (b'::l₂) (or.inr h) := by split; simp only [mem_cons_iff, or_true, mem_zip h]

@[simp] theorem unzip_nil : unzip (@nil (α × β)) = ([], []) := rfl

@[simp] theorem unzip_cons (a : α) (b : β) (l : list (α × β)) :
   unzip ((a, b) :: l) = (a :: (unzip l).1, b :: (unzip l).2) :=
by rw unzip; cases unzip l; refl

theorem unzip_eq_map : ∀ (l : list (α × β)), unzip l = (l.map prod.fst, l.map prod.snd)
| []            := rfl
| ((a, b) :: l) := by simp only [unzip_cons, map_cons, unzip_eq_map l]

theorem unzip_left (l : list (α × β)) : (unzip l).1 = l.map prod.fst :=
by simp only [unzip_eq_map]

theorem unzip_right (l : list (α × β)) : (unzip l).2 = l.map prod.snd :=
by simp only [unzip_eq_map]

theorem unzip_swap (l : list (α × β)) : unzip (l.map prod.swap) = (unzip l).swap :=
by simp only [unzip_eq_map, map_map]; split; refl

theorem zip_unzip : ∀ (l : list (α × β)), zip (unzip l).1 (unzip l).2 = l
| []            := rfl
| ((a, b) :: l) := by simp only [unzip_cons, zip_cons_cons, zip_unzip l]; split; refl

theorem unzip_zip_left : ∀ {l₁ : list α} {l₂ : list β}, length l₁ ≤ length l₂ →
  (unzip (zip l₁ l₂)).1 = l₁
| []      l₂      h := rfl
| l₁      []      h := by rw eq_nil_of_length_eq_zero (eq_zero_of_le_zero h); refl
| (a::l₁) (b::l₂) h := by simp only [zip_cons_cons, unzip_cons,
    unzip_zip_left (le_of_succ_le_succ h)]; split; refl

theorem unzip_zip_right {l₁ : list α} {l₂ : list β} (h : length l₂ ≤ length l₁) :
  (unzip (zip l₁ l₂)).2 = l₂ :=
by rw [← zip_swap, unzip_swap]; exact unzip_zip_left h

theorem unzip_zip {l₁ : list α} {l₂ : list β} (h : length l₁ = length l₂) :
  unzip (zip l₁ l₂) = (l₁, l₂) :=
by rw [← @prod.mk.eta _ _ (unzip (zip l₁ l₂)),
  unzip_zip_left (le_of_eq h), unzip_zip_right (ge_of_eq h)]

@[simp] theorem length_revzip (l : list α) : length (revzip l) = length l :=
by simp only [revzip, length_zip, length_reverse, min_self]

@[simp] theorem unzip_revzip (l : list α) : (revzip l).unzip = (l, l.reverse) :=
unzip_zip (length_reverse l).symm

@[simp] theorem revzip_map_fst (l : list α) : (revzip l).map prod.fst = l :=
by rw [← unzip_left, unzip_revzip]

@[simp] theorem revzip_map_snd (l : list α) : (revzip l).map prod.snd = l.reverse :=
by rw [← unzip_right, unzip_revzip]

theorem reverse_revzip (l : list α) : reverse l.revzip = revzip l.reverse :=
by rw [← zip_unzip.{u u} (revzip l).reverse, unzip_eq_map]; simp; simp [revzip]

theorem revzip_swap (l : list α) : (revzip l).map prod.swap = revzip l.reverse :=
by simp [revzip]

end list
