/-
Copyright (c) 2018 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek
-/

import data.list
import data.array.defs

/-!
# Tables

A `table` is a self-resizing array-backed list,
which uses opaque references called `table_ref`s for access.
-/

universe variables u v w z

attribute [inline] bool.decidable_eq option.is_some option.is_none list.head
attribute [inline] array.read array.write

def null : ℕ := 0xFFFFFFFF
def first : ℕ := 0

class indexed (α : Type u) :=
(index : α → ℕ)
class keyed (α : Type u) (κ : Type v) [decidable_eq κ] :=
(key : α → κ)

structure table (α : Type u) :=
(next_id : ℕ)
(buff_len : ℕ)
(entries : array buff_len (option α))

namespace table

def null : ℕ := 0xFFFFFFFF
def first : ℕ := 0

variables {α : Type u} {β : Type v} {κ : Type w} [decidable_eq κ] (t : table α)

-- TODO use push_back and pop_back builtins to avoid array preallocation
-- TODO several recusion-induced-meta can be removed from the file (given proofs)

def DEFAULT_BUFF_LEN := 10

def create (buff_len : ℕ := DEFAULT_BUFF_LEN) : table α :=
⟨table.first, buff_len, mk_array buff_len none⟩

def from_list (l : list α) : table α :=
let n := l.length in
let buff : array n (option α) := mk_array n none in
⟨n, n, buff.map_copy_from_list (λ a, some a) l⟩

meta def from_map_array {dim : ℕ} (x : array dim α) (f : α → β) : table β :=
let buff : array dim (option β) := mk_array dim none in
⟨dim, dim, x.map_copy buff (λ a, some $ f a)⟩

meta def from_array {dim : ℕ} (x : array dim α) : table α := from_map_array x id

@[inline] def is_full : bool := t.next_id = t.buff_len

@[inline] private def try_fin (r : ℕ) : option (fin t.buff_len) :=
begin
  by_cases h : r < t.buff_len,
  exact fin.mk r h,
  exact none
end

@[inline] meta def grow : table α :=
let new_len := t.buff_len * 2 in
let new_buff : array new_len (option α) := mk_array new_len none in
{t with buff_len := new_len, entries := array.copy t.entries new_buff}

@[inline] def at_ref (r : ℕ) : option α :=
match try_fin t r with
| none := none
| some r := t.entries.read r
end

@[inline] def present (r : ℕ) : bool := (t.at_ref r).is_some

@[inline] meta def get (r : ℕ) : option α := t.at_ref r

@[inline] def iget [inhabited α] (r : ℕ) : α :=
match t.at_ref r with
| none := default α
| some a := a
end

@[inline] def set (r : ℕ) (a : α) : table α :=
match try_fin t r with
| none := t
| some r := {t with entries := t.entries.write r a}
end

@[inline] meta def alloc (a : α) : table α :=
let t : table α := if t.is_full then t.grow else t in
let t := t.set t.next_id a in
{ t with next_id := t.next_id + 1 }

@[inline] meta def alloc_list : table α → list α → table α
| t [] := t
| t (a :: rest) := alloc_list (t.alloc a) rest

@[inline] def update [indexed α] (a : α) : table α := t.set (indexed.index a) a

@[inline] def length : ℕ := t.next_id

meta def find_from (p : α → Prop) [decidable_pred p] : ℕ → option α
| ref := match t.at_ref ref with
         | none := none
         | some a := if p a then some a else find_from (ref + 1)
         end

@[inline] meta def find (p : α → Prop) [decidable_pred p] : option α :=
t.find_from p table.first

@[inline] meta def find_key [decidable_eq κ] [keyed α κ] (key : κ) : option α :=
t.find (λ a, key = @keyed.key _ _ _ _ a)

meta def foldl (f : β → α → β) (b : β) (t : table α) : β :=
t.entries.foldl b (λ a : option α, λ b : β,
  match a with
  | none := b
  | some a := f b a
  end)

private meta def empty_buff (t : table α) : array t.buff_len (option β) :=
mk_array t.buff_len none

meta def map (f : α → β) : table β :=
⟨t.next_id, t.buff_len, t.entries.map_copy (empty_buff t) (option.map f)⟩

meta def mmap {m : Type v → Type z} [monad m] (f : α → m β) : m (table β) :=
do new_buff ← t.entries.mmap_copy (empty_buff t) (λ a : option α,
   match a with
   | none := pure none
   | some a := do v ← f a, pure $ some v
   end),
   return ⟨t.next_id, t.buff_len, new_buff⟩

meta def to_list : list α := t.foldl list.concat []

end table
