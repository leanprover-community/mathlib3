/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

A tactic for discharging Presburger arithmetic goals using the Omega test.
-/

import data.list.basic 
import tactic.omega.misc 
import tactic.omega.simp_omega 

variables {α β : Type}

namespace list

@[omega] def set [has_zero α] (i) : list α → ℕ → list α
| (j::is) 0     := i::is
| []      0     := [i] 
| (j::is) (k+1) := j::(set is k) 
| []      (k+1) := 0::(set ([] : list α) k)
notation as `{` m `↦` a `}` := set a as m 

lemma length_set [has_zero α] {a : α} :
  ∀ {m as}, (as{m ↦ a}).length = _root_.max as.length (m+1) 
| 0 [] := rfl
| 0 (a::as) := 
  begin
    rw max_eq_left, refl, 
    simp [nat.le_add_right],
  end
| (m+1) [] := 
  begin
    rw max_eq_right, simp_omega [list.length],
    rw @length_set m, rw max_eq_right, 
    repeat {apply zero_le}
  end
| (m+1) (a::as) := 
  begin
    simp_omega 
    [list.length, nat.max_succ_succ], 
    rw @length_set m, 
  end
  
@[omega] def get [has_zero α] : nat → list α → α  
| _ [] := (0 : α)
| 0 (i::is) := i 
| (n+1) (i::is) := get n is 

@[omega] lemma get_nil [has_zero α] {k} : get k [] = (0 : α) := 
begin cases k; refl end

lemma get_eq_zero_of_le [has_zero α] : 
  ∀ k {as : list α}, as.length ≤ k → get k as = (0 : α) 
| 0 [] h1 := rfl
| 0 (a::as) h1 := by cases h1
| (k+1) [] h1 := rfl
| (k+1) (a::as) h1 := 
  begin
    simp_omega, apply get_eq_zero_of_le k,
    rw ← nat.succ_le_succ_iff, apply h1,
  end

lemma get_set [has_zero α] {a : α} : 
  ∀ {k} {as}, as{k ↦ a}.get k = a
| 0 as := begin cases as; refl end
| (k+1) as :=
  begin cases as; {simp_omega, apply get_set} end

lemma eq_get_of_mem [has_zero α] {a} : 
  ∀ {as : list α}, a ∈ as → ∃ n, a = (as.get n)
| [] h := by cases h
| (b::as) h :=
  begin
    rw mem_cons_iff at h, cases h,
    { existsi 0, apply h },
    { cases eq_get_of_mem h with n h2,
      existsi (n+1), apply h2 }
  end

lemma mem_get_of_le [has_zero α] : 
  ∀ {n} {as : list α}, 
  n < as.length → as.get n ∈ as 
| _ [] h1 := by cases h1
| 0 (a::as) _ := or.inl rfl
| (n+1) (a::as) h1 := 
  begin
    simp_omega, apply or.inr,
    apply mem_get_of_le,
    apply nat.lt_of_succ_lt_succ h1,
  end

lemma mem_get_of_ne_zero [has_zero α] : 
  ∀ {n} {as : list α}, 
  as.get n ≠ 0 → as.get n ∈ as 
| _ [] h1 := begin exfalso, apply h1, rw get_nil end
| 0 (a::as) h1 := or.inl rfl 
| (n+1) (a::as) h1 :=
  begin
    simp_omega, 
    apply (or.inr (mem_get_of_ne_zero _)),
    apply h1
  end

lemma get_set_eq_of_ne [has_zero α] {a : α} : 
  ∀ {as : list α} {k} m, m ≠ k → as{k ↦ a}.get m = as.get m 
| as 0 m h1 := 
  begin
    cases m, contradiction, cases as, simp_omega, refl
  end
| as (k+1) m h1 := 
  begin
    cases as; cases m; simp_omega, 
    { rw get_set_eq_of_ne, simp_omega,
      intro hc, apply h1, simp [hc] },
    { apply get_set_eq_of_ne, intro hc,
      apply h1, simp [hc], }
  end

lemma get_map [has_zero α] [has_zero β] {f : α → β} : 
  ∀ {n} {as : list α}, n < as.length → (as.map f).get n = f (as.get n) 
| _ [] h := by cases h
| 0 (a::as) h := rfl
| (n+1) (a::as) h := 
  begin
    simp only [map, get], apply get_map,
    simp only [length, nat.lt_succ_iff] at h, 
    apply h,
  end

lemma get_map' [has_zero α] [has_zero β] {f : α → β} {n} {as : list α} :
  f 0 = 0 → (as.map f).get n = f (as.get n) :=
begin
  intro h1, by_cases h2 : n < as.length,
  { apply get_map h2 },
  { rw not_lt at h2,
    rw [get_eq_zero_of_le _ h2, get_eq_zero_of_le, h1], 
    rw [length_map], apply h2 }
end

lemma forall_val_of_forall_mem [has_zero α] {p : α → Prop} {as : list α} :
  p 0 → (∀ x ∈ as, p x) → (∀ n, p (as.get n)) | h1 h2 n := 
begin
  by_cases h3 : n < as.length,
  { apply h2 _ (mem_get_of_le h3) },
  { rw not_lt at h3,
    rw get_eq_zero_of_le _ h3, apply h1 }
end 

@[omega] def neg [has_neg α] : list α → list α 
| []      := [] 
| (a::as) := -a::(neg as)

@[omega] lemma get_neg [add_group α] : 
  ∀ {k} {as : list α}, as.neg.get k = -(as.get k) 
| _ []          := by simp_omega
| 0 (a::as)     := by simp_omega
| (k+1) (a::as) := begin simp_omega [get_neg] end

@[omega] lemma length_neg [has_neg α] : 
  ∀ as : list α, (as).neg.length = as.length 
| []      := rfl 
| (a::as) := by simp_omega [list.length, length_neg] 

@[omega] def add [has_add α] : list α → list α → list α 
| as1 [] := as1
| [] as2 := as2
| (a1::as1) (a2::as2) := ((a1+a2)::(add as1 as2))

@[omega] lemma nil_add [has_add α] (as : list α) :
add [] as = as := by cases as; refl

@[omega] lemma add_nil [has_add α] (as : list α) :
add as [] = as := by cases as; refl

@[omega] lemma get_add [add_monoid α] : 
  ∀ {k} {is js : list α}, 
  (add is js).get k = (is.get k + js.get k) 
| 0     is      []      := by simp_omega
| 0     []      js      := by simp_omega
| 0     (i::is) (j::js) := by simp_omega
| (k+1) []      js      := by simp_omega
| (k+1) is      []      := by simp_omega
| (k+1) (i::is) (j::js) := by simp_omega [get_add]

lemma length_add [has_add α] : 
  ∀ {is js : list α}, (add is js).length = max is.length js.length 
| [] js := begin simp_omega, rw max_eq_right, apply zero_le end
| is [] := begin simp_omega, rw max_eq_left, apply zero_le end
| (i::is) (j::js) :=
  by simp_omega [list.length,
     nat.max_succ_succ, length_add]

lemma map_add_map [has_add α] (f g : α → α) :
  ∀ {as : list α}, as.map (λ x, f x + g x) = add (as.map f) (as.map g) 
| []      := rfl
| (a::as) := begin simp_omega [@map_add_map as], constructor; refl end

@[omega] def sub [has_neg α] [has_sub α] : list α → list α → list α 
| [] []        := []
| [] (a2::as2) := neg (a2::as2)
| (a1::as1) [] := a1::as1
| (a1::as1) (a2::as2) := (a1-a2)::(sub as1 as2) 

@[omega] lemma nil_sub [has_neg α] [has_sub α] (as : list α) :
sub [] as = as.neg := by cases as; refl

@[omega] lemma sub_nil [has_neg α] [has_sub α] (as : list α) :
sub as [] = as := by cases as; refl

@[omega] lemma get_sub [add_group α] : 
  ∀ {k} {is js : list α}, 
  (sub is js).get k = (is.get k - js.get k) 
| 0     is      []      := by simp_omega
| 0     []      js      := by simp_omega
| 0     (i::is) (j::js) := by simp_omega
| (k+1) []      js      := by simp_omega 
| (k+1) is      []      := by simp_omega 
| (k+1) (i::is) (j::js) := by simp_omega [get_sub]

lemma length_sub [has_neg α] [has_sub α] : 
  ∀ {is js : list α}, (sub is js).length = max is.length js.length 
| [] js := begin simp_omega, rw max_eq_right, apply zero_le end
| is [] := begin simp_omega, rw max_eq_left, apply zero_le end
| (i::is) (j::js) :=
  by simp_omega [list.length,
     nat.max_succ_succ, length_sub]

def max [inhabited α] [decidable_linear_order α] : list α → α 
| []           := @inhabited.default α _
| [a]          := a
| (a1::a2::as) := _root_.max a1 (max (a2::as))

def map_with_index_core (f : nat → α → β) : nat → list α → list β  
| k []      := []
| k (a::as) := f k a::(map_with_index_core (k+1) as)

def map_with_index (f : nat → α → β) (as : list α) : list β :=
map_with_index_core f 0 as

lemma forall_mem_cons_of {p : α → Prop} {a : α} {as : list α} :
  p a → (∀ x ∈ as, p x) → (∀ x ∈ (a::as), p x) :=
begin
  intros h1 h2, rw forall_mem_cons,
  constructor; assumption
end

end list