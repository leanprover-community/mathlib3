/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek
-/
import data.nat.basic

/-!
# Lists as Functions

Definitions for using lists as finite representations of finitely-supported functions with domain
ℕ.

These include pointwise operations on lists, as well as get and set operations.

## Notations

An index notation is introduced in this file for setting a particular element of a list. With `as`
as a list `m` as an index, and `a` as a new element, the notation is `as {m ↦ a}`.

So, for example
`[1, 3, 5] {1 ↦ 9}` would result in `[1, 9, 5]`

This notation is in the locale `list.func`.
-/

open list

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

namespace list
namespace func

variables {a : α}
variables {as as1 as2 as3 : list α}

/-- Elementwise negation of a list -/
def neg [has_neg α] (as : list α) := as.map (λ a, -a)

variables [inhabited α] [inhabited β]

/--
Update element of a list by index. If the index is out of range, extend the list with default
elements
-/
@[simp] def set (a : α) : list α → ℕ → list α
| (_::as) 0     := a::as
| []      0     := [a]
| (h::as) (k+1) := h::(set as k)
| []      (k+1) := (default α)::(set ([] : list α) k)

localized "notation as ` {` m ` ↦ ` a `}` := list.func.set a as m" in list.func

/-- Get element of a list by index. If the index is out of range, return the default element -/
@[simp] def get : ℕ → list α → α
| _ []          := default α
| 0 (a::as)     := a
| (n+1) (a::as) := get n as

/--
Pointwise equality of lists. If lists are different lengths, compare with the default
element.
-/
def equiv (as1 as2 : list α) : Prop :=
∀ (m : nat), get m as1 = get m as2

/-- Pointwise operations on lists. If lists are different lengths, use the default element. -/
@[simp] def pointwise (f : α → β → γ) : list α → list β → list γ
| []      []      := []
| []      (b::bs) := map (f $ default α) (b::bs)
| (a::as) []      := map (λ x, f x $ default β) (a::as)
| (a::as) (b::bs) := (f a b)::(pointwise as bs)

/-- Pointwise addition on lists. If lists are different lengths, use zero. -/
def add {α : Type u} [has_zero α] [has_add α] : list α → list α → list α :=
@pointwise α α α ⟨0⟩ ⟨0⟩ (+)

/-- Pointwise subtraction on lists. If lists are different lengths, use zero. -/
def sub {α : Type u} [has_zero α] [has_sub α] : list α → list α → list α :=
@pointwise α α α ⟨0⟩ ⟨0⟩ (@has_sub.sub α _)

/- set -/

lemma length_set : ∀ {m : ℕ} {as : list α},
  (as {m ↦ a}).length = _root_.max as.length (m+1)
| 0 []          := rfl
| 0 (a::as)     := by {rw max_eq_left, refl, simp [nat.le_add_right]}
| (m+1) []      := by simp only [set, nat.zero_max, length, @length_set m]
| (m+1) (a::as) := by simp only [set, nat.max_succ_succ, length, @length_set m]

@[simp] lemma get_nil {k : ℕ} : get k [] = default α :=
by {cases k; refl}

lemma get_eq_default_of_le :
  ∀ (k : ℕ) {as : list α}, as.length ≤ k → get k as = default α
| 0     []      h1 := rfl
| 0     (a::as) h1 := by cases h1
| (k+1) []      h1 := rfl
| (k+1) (a::as) h1 :=
  begin
    apply get_eq_default_of_le k,
    rw ← nat.succ_le_succ_iff, apply h1,
  end

@[simp] lemma get_set {a : α} :
  ∀ {k : ℕ} {as : list α}, get k (as {k ↦ a}) = a
| 0 as     := by {cases as; refl, }
| (k+1) as := by {cases as; simp [get_set]}

lemma eq_get_of_mem {a : α} :
  ∀ {as : list α}, a ∈ as → ∃ n : nat, ∀ d : α, a = (get n as)
| [] h := by cases h
| (b::as) h :=
  begin
    rw mem_cons_iff at h, cases h,
    { existsi 0, intro d, apply h },
    { cases eq_get_of_mem h with n h2,
      existsi (n+1), apply h2 }
  end

lemma mem_get_of_le :
  ∀ {n : ℕ} {as : list α}, n < as.length → get n as ∈ as
| _ [] h1 := by cases h1
| 0 (a::as) _ := or.inl rfl
| (n+1) (a::as) h1 :=
  begin
    apply or.inr, unfold get,
    apply mem_get_of_le,
    apply nat.lt_of_succ_lt_succ h1,
  end

lemma mem_get_of_ne_zero :
  ∀ {n : ℕ} {as : list α},
  get n as ≠ default α → get n as ∈ as
| _ [] h1 := begin exfalso, apply h1, rw get_nil end
| 0 (a::as) h1 := or.inl rfl
| (n+1) (a::as) h1 :=
  begin
    unfold get,
    apply (or.inr (mem_get_of_ne_zero _)),
    apply h1
  end

lemma get_set_eq_of_ne {a : α} :
  ∀ {as : list α} (k : ℕ) (m : ℕ),
  m ≠ k → get m (as {k ↦ a}) = get m as
| as 0 m h1 :=
  by { cases m, contradiction, cases as;
       simp only [set, get, get_nil] }
| as (k+1) m h1 :=
  begin
    cases as; cases m,
    simp only [set, get],
    { have h3 : get m (nil {k ↦ a}) = default α,
      { rw [get_set_eq_of_ne k m, get_nil],
        intro hc, apply h1, simp [hc] },
      apply h3 },
    simp only [set, get],
    { apply get_set_eq_of_ne k m,
      intro hc, apply h1, simp [hc], }
  end

lemma get_map {f : α → β} : ∀ {n : ℕ} {as : list α}, n < as.length →
  get n (as.map f) = f (get n as)
| _ [] h := by cases h
| 0 (a::as) h := rfl
| (n+1) (a::as) h1 :=
  begin
    have h2 : n < length as,
    { rw [← nat.succ_le_iff, ← nat.lt_succ_iff],
      apply h1 },
    apply get_map h2,
  end

lemma get_map' {f : α → β} {n : ℕ} {as : list α} :
  f (default α) = (default β) →
  get n (as.map f) = f (get n as) :=
begin
  intro h1, by_cases h2 : n < as.length,
  { apply get_map h2, },
  { rw not_lt at h2,
    rw [get_eq_default_of_le _ h2, get_eq_default_of_le, h1],
    rw [length_map], apply h2 }
end

lemma forall_val_of_forall_mem {as : list α} {p : α → Prop} :
  p (default α) → (∀ x ∈ as, p x) → (∀ n, p (get n as)) :=
begin
  intros h1 h2 n,
  by_cases h3 : n < as.length,
  { apply h2 _ (mem_get_of_le h3) },
  { rw not_lt at h3,
    rw get_eq_default_of_le _ h3, apply h1 }
end

/- equiv -/

lemma equiv_refl : equiv as as := λ k, rfl

lemma equiv_symm : equiv as1 as2 → equiv as2 as1 :=
λ h1 k, (h1 k).symm

lemma equiv_trans :
  equiv as1 as2 → equiv as2 as3 → equiv as1 as3 :=
λ h1 h2 k, eq.trans (h1 k) (h2 k)

lemma equiv_of_eq : as1 = as2 → equiv as1 as2 :=
begin intro h1, rw h1, apply equiv_refl end

lemma eq_of_equiv : ∀ {as1 as2 : list α}, as1.length = as2.length →
  equiv as1 as2 → as1 = as2
| []     [] h1 h2 := rfl
| (_::_) [] h1 h2 := by cases h1
| [] (_::_) h1 h2 := by cases h1
| (a1::as1) (a2::as2) h1 h2 :=
  begin
    congr,
    { apply h2 0 },
    have h3 : as1.length = as2.length,
    { simpa [add_left_inj, add_comm, length] using h1 },
    apply eq_of_equiv h3,
    intro m, apply h2 (m+1)
  end

end func
-- We want to drop the `inhabited` instances for a moment,
-- so we close and open the namespace

namespace func

/- neg -/

@[simp] lemma get_neg [add_group α] {k : ℕ} {as : list α} :
  @get α ⟨0⟩ k (neg as) = -(@get α ⟨0⟩ k as) :=
by {unfold neg, rw (@get_map' α α ⟨0⟩), apply neg_zero}

@[simp] lemma length_neg [has_neg α] (as : list α) : (neg as).length = as.length :=
by simp only [neg, length_map]

variables [inhabited α] [inhabited β]

/- pointwise -/

lemma nil_pointwise {f : α → β → γ} : ∀ bs : list β, pointwise f [] bs = bs.map (f $ default α)
| []      := rfl
| (b::bs) :=
  by simp only [nil_pointwise bs, pointwise,
     eq_self_iff_true, and_self, map]

lemma pointwise_nil {f : α → β → γ} :
  ∀ as : list α, pointwise f as [] = as.map (λ a, f a $ default β)
| []      := rfl
| (a::as) :=
  by simp only [pointwise_nil as, pointwise,
     eq_self_iff_true, and_self, list.map]

lemma get_pointwise [inhabited γ] {f : α → β → γ} (h1 : f (default α) (default β) = default γ) :
  ∀ (k : nat) (as : list α) (bs : list β),
  get k (pointwise f as bs) = f (get k as) (get k bs)
| k [] [] := by simp only [h1, get_nil, pointwise, get]
| 0 [] (b::bs) :=
  by simp only [get_pointwise, get_nil,
      pointwise, get, nat.nat_zero_eq_zero, map]
| (k+1) [] (b::bs) :=
  by { have : get k (map (f $ default α) bs) = f (default α) (get k bs),
       { simpa [nil_pointwise, get_nil] using (get_pointwise k [] bs) },
       simpa [get, get_nil, pointwise, map] }
| 0 (a::as) [] :=
  by simp only [get_pointwise, get_nil,
     pointwise, get, nat.nat_zero_eq_zero, map]
| (k+1) (a::as) [] :=
  by simpa [get, get_nil, pointwise, map, pointwise_nil, get_nil]
     using get_pointwise k as []
| 0 (a::as) (b::bs) := by simp only [pointwise, get]
| (k+1) (a::as) (b::bs) :=
  by simp only [pointwise, get, get_pointwise k]

lemma length_pointwise {f : α → β → γ} :
  ∀ {as : list α} {bs : list β},
  (pointwise f as bs).length = _root_.max as.length bs.length
| []      []      := rfl
| []      (b::bs) :=
  by simp only [pointwise, length, length_map,
     max_eq_right (nat.zero_le (length bs + 1))]
| (a::as) []      :=
  by simp only [pointwise, length, length_map,
     max_eq_left (nat.zero_le (length as + 1))]
| (a::as) (b::bs) :=
  by simp only [pointwise, length,
     nat.max_succ_succ, @length_pointwise as bs]

end func

namespace func
/- add -/

@[simp] lemma get_add {α : Type u} [add_monoid α] {k : ℕ} {xs ys : list α} :
  @get α ⟨0⟩ k (add xs ys) = ( @get α ⟨0⟩ k xs + @get α ⟨0⟩ k ys) :=
by {apply get_pointwise, apply zero_add}

@[simp] lemma length_add {α : Type u}
  [has_zero α] [has_add α] {xs ys : list α} :
  (add xs ys).length = _root_.max xs.length ys.length :=
@length_pointwise α α α ⟨0⟩ ⟨0⟩ _ _ _

@[simp] lemma nil_add {α : Type u} [add_monoid α]
  (as : list α) : add [] as = as :=
begin
  rw [add, @nil_pointwise α α α ⟨0⟩ ⟨0⟩],
  apply eq.trans _ (map_id as),
  congr' with x,
  have : @default α ⟨0⟩ = 0 := rfl,
  rw [this, zero_add], refl
end

@[simp] lemma add_nil {α : Type u} [add_monoid α]
  (as : list α) : add as [] = as :=
begin
  rw [add, @pointwise_nil α α α ⟨0⟩ ⟨0⟩],
  apply eq.trans _ (map_id as),
  congr' with x,
  have : @default α ⟨0⟩ = 0 := rfl,
  rw [this, add_zero], refl
end

lemma map_add_map {α : Type u} [add_monoid α] (f g : α → α) {as : list α} :
  add (as.map f) (as.map g) = as.map (λ x, f x + g x) :=
begin
  apply @eq_of_equiv _ (⟨0⟩ : inhabited α),
  { rw [length_map, length_add, max_eq_left, length_map],
    apply le_of_eq,
    rw [length_map, length_map] },
  intros m,
  rw [get_add],
  by_cases h : m < length as,
  { repeat {rw [@get_map α α ⟨0⟩ ⟨0⟩ _ _ _ h]} },
  rw not_lt at h,
  repeat {rw [get_eq_default_of_le m]};
  try {rw length_map, apply h},
  apply zero_add
end

/- sub -/

@[simp] lemma get_sub {α : Type u}
  [add_group α] {k : ℕ} {xs ys : list α} :
  @get α ⟨0⟩ k (sub xs ys) = (@get α ⟨0⟩ k xs - @get α ⟨0⟩ k ys) :=
by {apply get_pointwise, apply sub_zero}

@[simp] lemma length_sub [has_zero α] [has_sub α] {xs ys : list α} :
  (sub xs ys).length = _root_.max xs.length ys.length :=
@length_pointwise α α α ⟨0⟩ ⟨0⟩ _ _ _

@[simp] lemma nil_sub {α : Type} [add_group α]
  (as : list α) : sub [] as = neg as :=
begin
  rw [sub, nil_pointwise],
  congr' with x,
  have : @default α ⟨0⟩ = 0 := rfl,
  rw [this, zero_sub]
end

@[simp] lemma sub_nil {α : Type} [add_group α]
  (as : list α) : sub as [] = as :=
begin
  rw [sub, pointwise_nil],
  apply eq.trans _ (map_id as),
  congr' with x,
  have : @default α ⟨0⟩ = 0 := rfl,
  rw [this, sub_zero], refl
end

end func
end list
