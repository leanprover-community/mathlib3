/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

Use lists as finite representations of functions with domain ℕ.
-/

import data.list.basic

variables {α β γ : Type} 
variables {a a' : α} {b' : β} {c' : γ}
variables {as as1 as2 as3 : list α} {bs : list β} 
variables {f : α → β → γ}

namespace list

namespace func


/- set -/

@[simp] def set (a' a : α) : list α → ℕ → list α
| (_::as) 0     := a::as
| []      0     := [a]
| (h::as) (k+1) := h::(set as k)
| []      (k+1) := a'::(set ([] : list α) k)

local notation as `{` m `↦` a `;` a' `}` := set a' a as m

lemma length_set {d a : α} :
  ∀ {m : ℕ} {as : list α},
  (as{m ↦ a ; d}).length = _root_.max as.length (m+1)
| 0 [] := rfl
| 0 (a::as) :=
  begin
    rw max_eq_left, refl,
    simp [nat.le_add_right],
  end
| (m+1) [] :=
  begin
    rw max_eq_right,
    simp only [length, set], 
    rw @length_set m,
    rw max_eq_right,
    repeat {apply zero_le},
  end
| (m+1) (a::as) :=
  begin
    simp only [set, length],
    rw [@length_set m, nat.max_succ_succ],
  end


/- get -/

@[simp] def get (d : α): ℕ → list α → α
| _ []          := d
| 0 (a::as)     := a
| (n+1) (a::as) := get n as

@[simp] lemma get_nil {d : α} {k : ℕ} : get d k [] = d :=
by cases k; refl

lemma get_eq_default_of_le {d : α} :
  ∀ (k : ℕ) {as : list α}, as.length ≤ k → get d k as = d
| 0 [] h1 := rfl
| 0 (a::as) h1 := by cases h1
| (k+1) [] h1 := rfl
| (k+1) (a::as) h1 :=
  begin
    simp, apply get_eq_default_of_le k,
    rw ← nat.succ_le_succ_iff, apply h1,
  end

@[simp] lemma get_set {d1 d2 a : α} :
  ∀ {k : ℕ} {as : list α}, get d2 k (as{k ↦ a ; d1}) = a
| 0 as     := begin cases as; refl end
| (k+1) as := by {cases as; {simp, apply get_set}} 

lemma eq_get_of_mem {a : α} :
  ∀ {as : list α}, a ∈ as → ∃ n : nat, ∀ d : α, a = (get d n as)
| [] h := by cases h
| (b::as) h :=
  begin
    rw mem_cons_iff at h, cases h,
    { existsi 0, intro d, apply h },
    { cases eq_get_of_mem h with n h2,
      existsi (n+1), apply h2 }
  end

lemma mem_get_of_le {d : α} :
  ∀ {n : ℕ} {as : list α}, n < as.length → get d n as ∈ as
| _ [] h1 := by cases h1
| 0 (a::as) _ := or.inl rfl
| (n+1) (a::as) h1 :=
  begin
    simp, apply or.inr,
    apply mem_get_of_le,
    apply nat.lt_of_succ_lt_succ h1,
  end

lemma mem_get_of_ne_zero {d : α} :
  ∀ {n : ℕ} {as : list α},
  get d n as ≠ d → get d n as ∈ as
| _ [] h1 := begin exfalso, apply h1, rw get_nil end
| 0 (a::as) h1 := or.inl rfl
| (n+1) (a::as) h1 :=
  begin
    simp,
    apply (or.inr (mem_get_of_ne_zero _)),
    apply h1
  end

lemma get_set_eq_of_ne {d a : α} :
  ∀ {as : list α} {k : ℕ} (m : ℕ),
  m ≠ k → get d m (as{k ↦ a ; d}) = get d m as
| as 0 m h1 :=
  begin
    cases m, contradiction, cases as, simp, refl
  end
| as (k+1) m h1 :=
  begin
    cases as; cases m; simp,
    { rw get_set_eq_of_ne, simp,
      intro hc, apply h1, simp [hc] },
    { apply get_set_eq_of_ne, intro hc,
      apply h1, simp [hc], }
  end

lemma get_map (a' : α) {f : α → β} : ∀ {n : ℕ} {as : list α},
  n < as.length → get b' n (as.map f) = f (get a' n as)
| _ [] h := by cases h
| 0 (a::as) h := rfl
| (n+1) (a::as) h :=
  begin
    simp only [map, get], apply get_map,
    simp only [length, nat.lt_succ_iff] at h,
    apply h,
  end

lemma get_map' {f : α → β} {n : ℕ} {as : list α} :
  f a' = b' → get b' n (as.map f) = f (get a' n as) :=
begin
  intro h1, by_cases h2 : n < as.length,
  { apply get_map a' h2, },
  { rw not_lt at h2,
    rw [get_eq_default_of_le _ h2, get_eq_default_of_le, h1],
    rw [length_map], apply h2 }
end

lemma forall_val_of_forall_mem {p : α → Prop} :
  p a' → (∀ x ∈ as, p x) → (∀ n, p (get a' n as)) :=
begin
  intros h1 h2 n,
  by_cases h3 : n < as.length,
  { apply h2 _ (mem_get_of_le h3) },
  { rw not_lt at h3,
    rw get_eq_default_of_le _ h3, apply h1 }
end


/- equiv -/

def equiv (a : α) (as1 as2 : list α) : Prop :=
∀ (m : nat), get a m as1 = get a m as2

lemma equiv_refl : equiv a as as := λ k, rfl

lemma equiv_symm : equiv a as1 as2 → equiv a as2 as1 := 
λ h1 k, (h1 k).symm

lemma equiv_trans :
  equiv a as1 as2 → equiv a as2 as3 → equiv a as1 as3 :=
λ h1 h2 k, eq.trans (h1 k) (h2 k)

lemma equiv_of_eq : as1 = as2 → equiv a as1 as2 := 
begin intro h1, rw h1, apply equiv_refl end

lemma eq_of_equiv :
  ∀ {as1 as2 : list α}, as1.length = as2.length → 
  equiv a as1 as2 → as1 = as2 
| []     [] h1 h2 := rfl
| (_::_) [] h1 h2 := by cases h1
| [] (_::_) h1 h2 := by cases h1
| (a1::as1) (a2::as2) h1 h2 := 
  begin
    congr,
    { apply h2 0 },
    { apply eq_of_equiv, 
      simp only [add_left_inj, add_comm, length] at h1,
      exact h1, intro m, apply h2 (m+1) }
  end


/- neg -/

def neg [has_neg α] (as : list α) := as.map (λ a, -a) 

@[simp] lemma get_neg {α : Type} [add_group α] 
  {k : ℕ} {as : list α} : get 0 k (neg as) = -(get 0 k as) :=
by {simp only [neg], rw get_map', apply neg_zero}

@[simp] lemma length_neg [has_neg α] (as : list α) : 
  (neg as).length = as.length := 
by {simp only [neg, length_map]}


/- pointwise -/

@[simp] def pointwise (a' : α) (b' : β) (f : α → β → γ) : list α → list β → list γ 
| []      []      := []
| []      (b::bs) := map (f a') (b::bs)
| (a::as) []      := map (λ x, f x b') (a::as)
| (a::as) (b::bs) := (f a b)::(pointwise as bs)

lemma nil_pointwise : 
  ∀ bs : list β, pointwise a' b' f [] bs = bs.map (f a') 
| []      := rfl
| (b::bs) := 
  by { simp only [nil_pointwise bs, pointwise, 
    eq_self_iff_true, and_self, map] }

lemma pointwise_nil : 
  ∀ as : list α, pointwise a' b' f as [] = as.map (λ a, f a b') 
| []      := rfl
| (a::as) := 
  by { simp only [pointwise_nil as, pointwise, 
    eq_self_iff_true, and_self, list.map] }

def get_pointwise (h1 : f a' b' = c') : 
  ∀ (k : nat) (as : list α) (bs : list β), 
  get c' k (pointwise a' b' f as bs) = f (get a' k as) (get b' k bs) 
| k [] [] := by {simp only [h1, get_nil, pointwise, get]}
| 0 [] (b::bs) := 
  by { simp only [get_pointwise, get_nil, 
       pointwise, get, nat.nat_zero_eq_zero, map] }
| (k+1) [] (b::bs) := 
  by { simp only [get, get_nil, pointwise, map], 
       have h := get_pointwise k [] bs, 
       simp only [nil_pointwise, get_nil] at h, 
       exact h }
| 0 (a::as) [] := 
  by { simp only [get_pointwise, get_nil, 
      pointwise, get, nat.nat_zero_eq_zero, map] }
| (k+1) (a::as) [] := 
  by { simp only [get, get_nil, pointwise, map], 
       have h := get_pointwise k as [], 
       simp only [pointwise_nil, get_nil] at h, 
       exact h }
| 0 (a::as) (b::bs) := by { simp only [pointwise, get] }
| (k+1) (a::as) (b::bs) := 
  by { simp only [pointwise, get, get_pointwise k] }

lemma length_pointwise : ∀ {as : list α} {bs : list β}, 
  (pointwise a' b' f as bs).length = _root_.max as.length bs.length 
| []      []      := rfl
| []      (b::bs) := 
  begin
    simp only [pointwise, length, length_map],
    rw [max_eq_right], repeat {apply zero_le},
  end
| (a::as) []      := 
  begin
    simp only [pointwise, length, length_map],
    rw [max_eq_left], repeat {apply zero_le},
  end
| (a::as) (b::bs) :=
  begin
    simp only [pointwise, length, 
      nat.max_succ_succ, @length_pointwise as bs],
  end


/- add -/

def add [has_zero α] [has_add α] : list α → list α → list α := pointwise 0 0 (+)

@[simp] lemma get_add {α : Type} [add_monoid α] {k : ℕ} {xs ys : list α} :
  get 0 k (add xs ys) = (get 0 k xs + get 0 k ys) :=
by {apply get_pointwise, apply zero_add}

@[simp] lemma length_add [has_zero α] [has_add α] {xs ys : list α} : 
  (add xs ys).length = _root_.max xs.length ys.length := 
length_pointwise

@[simp] lemma nil_add {α : Type} [add_monoid α] 
  (as : list α) : add [] as = as := 
begin
  rw [add, nil_pointwise], 
  apply eq.trans _ (map_id as), congr,
  ext, rw zero_add, refl,
end

@[simp] lemma add_nil {α : Type} [add_monoid α] 
  (as : list α) : add as [] = as := 
begin
  rw [add, pointwise_nil], 
  apply eq.trans _ (map_id as), congr,
  ext, rw add_zero, refl,
end

lemma map_add_map {α : Type} [add_monoid α] (f g : α → α) {as : list α} :
  add (as.map f) (as.map g) = as.map (λ x, f x + g x) :=
begin
  apply @eq_of_equiv _ (0 : α),
  { rw [length_map, length_add, max_eq_left, length_map],
    apply le_of_eq, rw [length_map, length_map] },
  { intros m, rw [get_add], 
    by_cases h : m < length as,
    { repeat {rw [@get_map α α _ 0 _ _ _ h]} },
    { rw not_lt at h,
      repeat {rw [get_eq_default_of_le m]};
      try {rw length_map, apply h},
      apply zero_add } }
end


/- sub -/

def sub [has_zero α] [has_sub α] : list α → list α → list α := pointwise 0 0 (λ x y, x - y)

@[simp] lemma get_sub {α : Type} [add_group α] {k : ℕ} {xs ys : list α} :
  get 0 k (sub xs ys) = (get 0 k xs - get 0 k ys) :=
by {apply get_pointwise, apply sub_zero}

@[simp] lemma length_sub [has_zero α] [has_sub α] {xs ys : list α} : 
  (sub xs ys).length = _root_.max xs.length ys.length := 
length_pointwise

@[simp] lemma nil_sub {α : Type} [add_group α] 
  (as : list α) : sub [] as = neg as := 
begin
  rw [sub, nil_pointwise], 
  congr, ext, rw zero_sub,
end

@[simp] lemma sub_nil {α : Type} [add_group α] 
  (as : list α) : sub as [] = as := 
begin
  rw [sub, pointwise_nil], 
  apply eq.trans _ (map_id as), 
  congr, ext, 
  rw sub_zero, refl
end

end func

end list
