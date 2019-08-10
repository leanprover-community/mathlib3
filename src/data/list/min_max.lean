/-
Copyright (c) 2019 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minchao Wu, Chris Hughes
-/
import data.list.basic 

namespace list
variables {α : Type*} {β : Type*} [decidable_linear_order β] [inhabited α]

def argmax_two (f : α → β) (a b : α) :=
if f b ≤ f a then a else b

def argmin_two (f : α → β) (a b : α) :=
@argmax_two _ (order_dual β) _ _ f a b

def argmax (f : α → β) (l : list α) : α :=
l.foldl (argmax_two f) l.head

def argmin (f : α → β) (l : list α) :=
@argmax _ (order_dual β) _ _ f l

lemma le_argmax_two_right_of_le {f : α → β} {a b c : α} : 
  f a ≤ f c → f a ≤ f (argmax_two f b c) :=
if hab : f c ≤ f b 
then by rw [argmax_two, if_pos hab]; exact λ h, le_trans h hab
else by rw [argmax_two, if_neg hab]; exact id

lemma le_argmax_two_left_of_le {f : α → β} {a b c : α} : 
  f a ≤ f b → f a ≤ f (argmax_two f b c) :=
if hab : f c ≤ f b 
then by rw [argmax_two, if_pos hab]; exact id
else by rw [argmax_two, if_neg hab]; exact λ h, le_trans h (le_of_not_ge hab)

@[simp] lemma le_argmax_two_iff (f : α → β) {a b c : α} :
  f a ≤ f (argmax_two f b c) ↔ f a ≤ f b ∨ f a ≤ f c :=
⟨by rw [argmax_two]; split_ifs; cc, 
  λ h, h.elim le_argmax_two_left_of_le le_argmax_two_right_of_le⟩

lemma argmax_two_assoc (f : α → β) (a b c : α) :
  argmax_two f (argmax_two f a b) c = argmax_two f a (argmax_two f b c) :=
begin 
  dunfold argmax_two,
  have := @le_trans _ _ (f c) (f b) (f a),
  have := λ h₁ h₂, not_le_of_gt (@lt_trans _ _ (f a) (f b) (f c) h₁ h₂),
  split_ifs; simp * at *,
end

lemma argmax_two_choice (f : α → β) (a b : α) : 
  argmax_two f a b = a ∨ argmax_two f a b = b :=
by dunfold argmax_two; split_ifs; simp

@[simp] lemma argmax_two_self (f : α → β) (a : α) : argmax_two f a a = a :=
if_pos (le_refl _) 

@[simp] lemma argmax_nil (f : α → β) : argmax f [] = default α := rfl

@[simp] lemma argmin_nil (f : α → β) : argmin f [] = default α := rfl

@[simp] lemma argmax_singleton {f : α → β} {a : α} : argmax f [a] = a := 
by simp [argmax, argmax_two]

@[simp] lemma argmin_singleton {f : α → β} {a : α} : argmin f [a] = a := 
@argmax_singleton _ (order_dual β) _ _ _ _

private theorem le_of_foldl_argmax_two {f : α → β} {l} : Π {a b : α}, a ∈ l → 
  f a ≤ f (foldl (argmax_two f) b l) :=
list.reverse_rec_on l 
  (λ _ _ h, absurd h $ not_mem_nil _)
  begin 
    intros _ _ ih _ _ h,
    cases mem_append.1 h with h h, 
    { simp [ih h] },
    { simp [mem_singleton.1 h, le_refl] }, 
  end

private theorem foldl_argmax_two_mem (f : α → β) (l) : Π (a : α), foldl (argmax_two f) a l ∈ a :: l :=
list.reverse_rec_on l (by simp) 
  begin
    assume tl hd ih a,
    simp only [foldl_append, foldl_cons, foldl_nil],
    cases argmax_two_choice f (foldl (argmax_two f) a tl) hd with h h,
    { rw h, 
      have hmem := @ih a, 
      cases (mem_cons_iff _ _ _).1 hmem; simp * },
    { simp [h] }
  end

theorem argmax_mem (f : α → β) : Π {l : list α}, l ≠ [] → argmax f l ∈ l 
| [] h       := (h rfl).elim
| (hd::tl) h := by simpa [argmax] using foldl_argmax_two_mem f tl hd

theorem argmin_mem (f : α → β) : Π {l : list α}, l ≠ [] → argmin f l ∈ l :=
@argmax_mem _ (order_dual β) _ _ _

theorem le_argmax_of_mem (f : α → β) {a : α} {l : list α} : a ∈ l → f a ≤ f (argmax f l) :=
le_of_foldl_argmax_two

theorem argmin_le_of_mem (f : α → β) {a : α} {l : list α} : a ∈ l → f (argmin f l) ≤ f a:=
@le_argmax_of_mem _ (order_dual β) _ _ _ _ _

theorem argmax_concat (f : α → β) (a : α) : Π {l : list α}, l ≠ [] → argmax f (l ++ [a]) = 
  argmax_two f (argmax f l) a 
| [] h       := (h rfl).elim
| (hd :: tl) _ := by simp [argmax]

theorem argmin_concat (f : α → β) (a : α) : Π {l : list α}, l ≠ [] → argmin f (l ++ [a]) = 
  argmin_two f (argmin f l) a :=
@argmax_concat _ (order_dual β) _ _ _ _ 

theorem argmax_cons (f : α → β) (a : α) : Π {l : list α}, l ≠ [] → argmax f (a :: l) = 
  argmax_two f a (argmax f l)
| [] h := (h rfl).elim
| (hd::tl) _ := list.reverse_rec_on tl (by simp [argmax, argmax_two]; congr) $
  assume tl hd' ih,
  by rw [← cons_append, ← cons_append,  argmax_concat _ _ (cons_ne_nil _ _),
    ih, argmax_concat _ _ (cons_ne_nil _ _), argmax_two_assoc]

theorem argmin_cons (f : α → β) (a : α) : Π {l : list α}, l ≠ [] → argmin f (a :: l) = 
  argmin_two f a (argmin f l) :=
@argmax_cons _ (order_dual β) _ _ _ _

variable [decidable_linear_order α]

def maximum (l : list α) := argmax id l

def minimum (l : list α) := argmin id l

@[simp] lemma maximum_nil : maximum ([] : list α) = default α := rfl

@[simp] lemma minimum_nil : minimum ([] : list α) = default α := rfl

theorem maximum_mem {l : list α} : l ≠ [] → maximum l ∈ l := 
argmax_mem _ 

theorem minimum_mem {l : list α} : l ≠ [] → minimum l ∈ l := 
argmin_mem _ 

theorem le_maximum_of_mem {a : α} {l : list α} : a ∈ l → a ≤ maximum l :=
le_argmax_of_mem id

theorem minimum_le_of_mem {a : α} {l : list α} : a ∈ l → minimum l ≤ a :=
argmin_le_of_mem id

theorem maximum_concat (a : α) {l : list α} : l ≠ [] → maximum (l ++ [a]) = max (maximum l) a :=
max_comm a (maximum l) ▸ argmax_concat id a

theorem minimum_concat (a : α) {l : list α} : l ≠ [] → minimum (l ++ [a]) =  min (minimum l) a :=
argmin_concat id a

theorem maximum_cons (a : α) {l : list α} : l ≠ [] → maximum (a :: l) = max a (maximum l) :=
max_comm (maximum l) a ▸ argmax_cons id a

theorem minimum_cons (a : α) {l : list α} : l ≠ [] → minimum (a :: l) = min a (minimum l) :=
argmin_cons id a

end list
