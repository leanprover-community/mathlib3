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
which uses opaque references called `ℕ`s for access.
-/

universe variables u v w z

attribute [inline] bool.decidable_eq option.is_some option.is_none list.head
attribute [inline] array.read array.write

-- @[irreducible] def ℕ : Type := ℕ

-- namespace ℕ

-- section internal

-- local attribute [reducible] ℕ

-- def MAXIMUM := 0xFFFFFFFF

-- def of_nat (r : ℕ) : ℕ := r
-- def to_nat (r : ℕ) : ℕ := r
-- def next (r : ℕ) : ℕ := of_nat (r + 1)

-- instance : decidable_eq ℕ := by apply_instance

-- instance : has_to_string ℕ := by apply_instance
-- meta instance : has_to_format ℕ := by apply_instance

-- end internal

-- def to_string (r : ℕ) : string := to_string r.to_nat
-- def null  : ℕ := of_nat MAXIMUM
-- def first : ℕ := of_nat 0

-- end ℕ

def d_array.map' {n : ℕ} {α : fin n → Type u} {β : fin n → Type v} (f : Π (i : fin n), α i → β i) (x : d_array n α) :
  d_array n β :=
d_array.mk $ λ i, f i $ x.read i

def array.map' {n : ℕ} {α : Type u} {β : Type v} (f : α → β) (x : array n α) :
  array n β :=
x.map' $ λ _, f

def buffer.map' {α : Type u} {β : Type v} (f : α → β) (x : buffer α) :
  buffer β :=
(x.to_array.map' f).to_buffer

class indexed (α : Type u) :=
(index : α → ℕ)
class keyed (α : Type u) (κ : Type v) [decidable_eq κ] :=
(key : α → κ)

abbreviation table (α : Type u) := buffer (option α)

namespace table

variables {α : Type u} {β : Type v} {κ : Type w} [decidable_eq κ] (t : table α)

-- TODO use push_back and pop_back builtins to avoid array preallocation
-- TODO several recusion-induced-meta can be removed from the file (given proofs)

def DEFAULT_TABLE_LEN := 10

def create (len : ℕ := DEFAULT_TABLE_LEN) : table α :=
⟨len, mk_array len none⟩

-- TODO(jmc): Is this fast? Otherwise optimise.
def from_list (l : list α) : table α :=
(l.map (option.some)).to_buffer

def map (f : α → β) : table β := buffer.map' (option.map f) t

def from_map_array {dim : ℕ} (x : array dim α) (f : α → β) : table β :=
(x.map' (option.some ∘ f)).to_buffer

def from_array {dim : ℕ} (x : array dim α) : table α := from_map_array x id

-- @[inline] def is_full : bool := t.next_id.to_nat = t.buff_len

@[inline] private def try_fin (r : ℕ) : option (fin t.size) :=
if h : r < t.size then some ⟨r, h⟩ else none

-- @[inline] meta def grow : table α :=
-- let new_len := t.buff_len * 2 in
-- let new_buff : array new_len (option α) := mk_array new_len none in
-- {t with buff_len := new_len, entries := array.copy t.entries new_buff}

@[inline] def at_ref (r : ℕ) : option α :=
match try_fin t r with
| none := none
| some r := t.read r
end

@[inline] def present (r : ℕ) : bool := (t.at_ref r).is_some

@[inline] def get (r : ℕ) : option α := t.at_ref r

@[inline] def iget [inhabited α] (r : ℕ) : α :=
match t.at_ref r with
| none := default α
| some a := a
end

@[inline] def set (r : ℕ) (a : α) : table α :=
match try_fin t r with
| none := t
| some r := t.write r a
end

@[inline] def alloc (a : α) : table α :=
t.push_back a

@[inline] def alloc_list : table α → list α → table α
| t [] := t
| t (a :: rest) := alloc_list (t.alloc a) rest

@[inline] def update [indexed α] (a : α) : table α := t.set (indexed.index a) a

@[inline] def length : ℕ := t.size

meta def find_from (p : α → Prop) [decidable_pred p] : ℕ → option α
| ref := match t.at_ref ref with
         | none := none
         | some a := if p a then some a else find_from (ref + 1)
         end

@[inline] meta def find (p : α → Prop) [decidable_pred p] : option α :=
t.find_from p 0

@[inline] meta def find_key [decidable_eq κ] [keyed α κ] (key : κ) : option α :=
t.find (λ a, key = @keyed.key _ _ _ _ a)

meta def foldl (f : β → α → β) (b : β) (t : table α) : β :=
t.to_array.foldl b (λ a : option α, λ b : β,
  match a with
  | none := b
  | some a := f b a
  end)

private meta def empty_buff (t : table α) : array t.length (option β) :=
mk_array t.length none

-- meta def map (f : α → β) : table β :=
-- ⟨t.next_id, t.buff_len, t.entries.map_copy (empty_buff t) (option.map f)⟩

meta def mmap {m : Type v → Type z} [monad m] (f : α → m β) : m (table β) :=
do x ← t.to_array.mmap_copy (empty_buff t) (λ a : option α,
   match a with
   | none := pure none
   | some a := do v ← f a, pure $ some v
   end),
   return x.to_buffer

def is_after_last (r : ℕ) : bool := t.length ≤ r

meta def to_list : list α := t.foldl list.concat []

meta instance [has_to_string α] : has_to_string (table α) := ⟨λ t, to_string t.to_list⟩

end table
