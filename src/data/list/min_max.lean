/-
Copyright (c) 2019 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Minchao Wu
-/
import data.list algebra.order_functions

namespace list
universes u
variables {α : Type u} [inhabited α] [decidable_linear_order α]

@[simp] def maximum (l : list α) : α := l.foldl max l.head

def maximum_aux (l : list α) : α := l.foldr max l.head

@[simp] def maximum_singleton {a : α} : maximum [a] = a := by simp

theorem le_of_foldr_max : Π {a b : α} {l}, a ∈ l → a ≤ foldr max b l
| a b [] h := absurd h $ not_mem_nil _
| a b (hd::tl) h := 
begin 
  cases h, 
  { simp [h, le_max_left] }, 
  { simp [le_max_right_of_le, le_of_foldr_max h] } 
end

theorem le_of_foldl_max {a b : α} {l} (h : a ∈ l) : a ≤ foldl max b l := 
by { rw foldl_eq_foldr max_comm max_assoc, apply le_of_foldr_max h }

theorem mem_foldr_max : Π {a : α} {l}, foldr max a l ∈ a :: l
| a [] := by simp
| a (hd::tl) := 
begin
  simp only [foldr_cons],
  cases (@max_choice _ _ hd (foldr max a tl)), 
  { simp [h] }, 
  { rw h, 
    have hmem := @mem_foldr_max a tl, 
    cases hmem, { simp [hmem] }, { right, right, exact hmem } }
end

theorem mem_foldl_max {a : α} {l} : foldl max a l ∈ a :: l :=
by { rw foldl_eq_foldr max_comm max_assoc, apply mem_foldr_max }

theorem mem_maximum_aux : Π {l : list α}, l ≠ [] →  maximum_aux l ∈ l
| [] h := by contradiction
| (hd::tl) h := 
begin
  dsimp [maximum_aux],
  have hc := @max_choice _ _ hd (foldr max hd tl),
  cases hc, { simp [hc] }, { simp [hc, mem_foldr_max] }
end

theorem mem_maximum {l : list α} (h : l ≠ []) : maximum l ∈ l :=
by { dsimp, rw foldl_eq_foldr max_comm max_assoc, apply mem_maximum_aux h }

theorem le_maximum_aux_of_mem : Π {a : α} {l}, a ∈ l → a ≤ maximum_aux l
| a [] h := absurd h $ not_mem_nil _
| a (hd::tl) h := 
begin
  cases h,
  { rw h, apply le_of_foldr_max, simp },
  { dsimp [maximum_aux], apply le_max_right_of_le, apply le_of_foldr_max h }
end

theorem le_maximum_of_mem {a : α} {l} (h : a ∈ l) : a ≤ maximum l :=
by { dsimp, rw foldl_eq_foldr max_comm max_assoc, apply le_maximum_aux_of_mem h }

def maximum_aux_cons : Π {a : α} {l}, l ≠ [] → maximum_aux (a :: l) = max a (maximum_aux l)
| a [] h := by contradiction
| a (hd::tl) h := 
begin
  apply le_antisymm,
  { have : a :: hd :: tl ≠ [], { simp [h] },
    have hle := mem_maximum_aux this, 
    cases hle, 
    { simp [hle, le_max_left] }, 
    { apply le_max_right_of_le, apply le_maximum_aux_of_mem, exact hle } },
  { have hc := @max_choice _ _ a (maximum_aux $ hd :: tl),
    cases hc, 
    { simp [hc, le_maximum_aux_of_mem] }, 
    { simp [hc, le_maximum_aux_of_mem, mem_maximum_aux h] } }
end

def maximum_cons {a : α} {l} (h : l ≠ []) : maximum (a :: l) = max a (maximum l) :=
begin 
  dsimp only [maximum], 
  repeat {rw foldl_eq_foldr max_comm max_assoc}, 
  have := maximum_aux_cons h, 
  dsimp only [maximum_aux] at this, 
  exact this
end

end list
