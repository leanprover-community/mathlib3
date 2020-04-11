/-
Copyright (c) 2018 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek
-/

import data.list
import data.array.defs

/-!
# Tables

TODO(jmc): fix the documentation
-/

universe variables u v w z

def d_array.map' {n : ℕ} {α : fin n → Type u} {β : fin n → Type v} (f : Π (i : fin n), α i → β i) (x : d_array n α) :
  d_array n β :=
d_array.mk $ λ i, f i $ x.read i

def array.map' {n : ℕ} {α : Type u} {β : Type v} (f : α → β) (x : array n α) :
  array n β :=
x.map' $ λ _, f

def buffer.map' {α : Type u} {β : Type v} (f : α → β) (x : buffer α) :
  buffer β :=
(x.to_array.map' f).to_buffer

-- TODO: inline these classes, they are almost never used.
class indexed (α : Type u) :=
(index : α → ℕ)
class keyed (α : Type u) (κ : Type v) [decidable_eq κ] :=
(key : α → κ)

abbreviation table (α : Type u) := buffer (option α)

namespace table

variables {α : Type u} {β : Type v} {κ : Type w} [decidable_eq κ] (t : table α)

-- TODO use push_back and pop_back builtins to avoid array preallocation
-- TODO several recusion-induced-meta can be removed from the file (given proofs)

def create (len : ℕ := 0) : table α :=
⟨len, mk_array len none⟩

-- TODO(jmc): Is this fast? Otherwise optimise.
def from_list (l : list α) : table α :=
(l.map (option.some)).to_buffer

def map (f : α → β) : table β := buffer.map' (option.map f) t

def from_map_array {dim : ℕ} (x : array dim α) (f : α → β) : table β :=
(x.map' (option.some ∘ f)).to_buffer

def from_array {dim : ℕ} (x : array dim α) : table α := from_map_array x id

@[inline] private def try_fin (r : ℕ) : option (fin t.size) :=
if h : r < t.size then some ⟨r, h⟩ else none

@[inline] def get (r : ℕ) : option α :=
t.read' r

@[inline] def contains (r : ℕ) : bool := (t.get r).is_some

@[inline] def iget [inhabited α] (r : ℕ) : α :=
match t.get r with
| none := default α
| some a := a
end

@[inline] def set (r : ℕ) (a : α) : table α :=
match try_fin t r with
| none := t
| some r := t.write r a
end

@[inline] def push_back (a : α) : table α :=
t.push_back a

@[inline] def append_list : table α → list α → table α
| t [] := t
| t (a :: rest) := append_list (t.push_back a) rest

@[inline] def update [indexed α] (a : α) : table α := t.set (indexed.index a) a

@[inline] def length : ℕ := t.size

meta def find_from (p : α → Prop) [decidable_pred p] : ℕ → option α
| ref := match t.get ref with
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
