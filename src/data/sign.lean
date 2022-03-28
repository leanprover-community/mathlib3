/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import order.basic
import algebra.algebra.basic

/-!
# Sign function

This file defines the sign function for types with zero and a decidable less-than relation, and
proves some basic theorems about it.
-/

@[derive decidable_eq]
inductive sign_type
| zero | neg | pos

namespace sign_type

instance : has_zero sign_type := ⟨zero⟩
instance :  has_one sign_type := ⟨pos⟩

instance : has_neg sign_type :=
⟨λ s, match s with
| neg  := pos
| zero := zero
| pos  := neg
end⟩

@[simp] lemma zero_eq_zero   : zero = 0 := rfl
@[simp] lemma neg_eq_neg_one : neg = -1 := rfl
@[simp] lemma pos_eq_one     : pos = 1  := rfl

def mul : sign_type → sign_type → sign_type
| neg neg  := pos
| neg zero := zero
| neg pos  := neg
| zero _   := zero
| pos h    := h

instance : has_mul sign_type := ⟨mul⟩

inductive le : sign_type → sign_type → Prop
| of_neg (a) : le neg a
| zero       : le zero zero
| of_pos (a) : le a pos

instance : has_le sign_type := ⟨le⟩

instance : decidable_rel le :=
λ a b, by cases a; cases b; exact is_false (by rintro ⟨⟩) <|> exact is_true (by constructor)

/- We can define a `field` instance on `sign_type`, but it's not mathematically sensible -/
instance : comm_group_with_zero sign_type :=
{ zero            := 0,
  one             := 1,
  mul             := (*),
  inv             := id,
  mul_zero        := λ a, by cases a; refl,
  zero_mul        := λ a, by cases a; refl,
  mul_one         := λ a, by cases a; refl,
  one_mul         := λ a, by cases a; refl,
  mul_inv_cancel  := λ a ha,  by cases a; trivial,
  mul_comm        := λ a b,   by casesm* _; refl,
  mul_assoc       := λ a b c, by casesm* _; refl,
  exists_pair_ne  := ⟨0, 1,   by rintro ⟨⟩⟩,
  inv_zero        := rfl }

instance : linear_order sign_type :=
{ le           := (≤),
  le_refl      := λ a, by cases a; constructor,
  le_total     := λ a b, by casesm* _; dec_trivial,
  le_antisymm  := λ a b ha hb, by casesm* _; refl,
  le_trans     := λ a b c hab hbc, by casesm* _; constructor,
  decidable_le := le.decidable_rel }

def fin3_equiv : sign_type ≃* fin 3 :=
{ to_fun :=  λ a, a.rec_on 0 (-1) 1,
  inv_fun := λ a, match a with
    | ⟨0, h⟩   := 0
    | ⟨1, h⟩   := 1
    | ⟨2, h⟩   := -1
    | ⟨n+3, h⟩ := (h.not_le le_add_self).elim
  end,
  left_inv :=  λ a, by cases a; refl,
  right_inv := λ a, match a with
    | ⟨0, h⟩   := rfl
    | ⟨1, h⟩   := rfl
    | ⟨2, h⟩   := rfl
    | ⟨n+3, h⟩ := (h.not_le le_add_self).elim
  end,
  map_mul' := λ x y, by casesm* _; refl }

end sign_type

variables {α : Type*} [has_zero α]

open sign_type

/-- The sign of an element - 1 if it's positive, -1 if negative, 0 otherwise. -/
@[simps] def sign [preorder α] [decidable_rel ((<) : α → α → Prop)] : α →o sign_type :=
⟨λ a, if 0 < a then 1 else if a < 0 then -1 else 0, λ a b h, begin
  dsimp,
  split_ifs; try {constructor},
  { cases lt_irrefl 0 (h_1.trans $ h.trans_lt h_3) },
  { cases h_2 (h_1.trans_le h) },
  { cases h_2 (h.trans_lt h_4) }
  end⟩

section preorder

variables [preorder α] [decidable_rel ((<) : α → α → Prop)] {a b : α}

@[simp] lemma sign_zero : sign (0 : α) = 0 := by simp [sign]

end preorder

section linear_order

variables [linear_order α] {a b : α}

lemma sign_ne_zero (h : a ≠ 0) : sign a ≠ 0 :=
begin
  contrapose! h,
  rw sign_coe at h,
  split_ifs at h,
  { cases h },
  { cases h },
  exact ((lt_trichotomy a 0).resolve_left h_2).resolve_right h_1
end

end linear_order
