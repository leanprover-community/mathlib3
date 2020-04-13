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

/-- A `table` is an array-like datastructure where entries may be empty.
It is implemented as `buffer (option _)`. -/
@[reducible] def table (α : Type u) := buffer (option α)

/-- Create an empty table.
This method accepts an optional length parameter (default: `0`)
to specify the size of the table.
Alias: `table.create` -/
def mk_table {α : Type u} (len : ℕ := 0) : table α :=
⟨len, mk_array len none⟩

namespace table

variables {α : Type u} {β : Type v} (t : table α)

/-- Create an empty table.
This method accepts an optional length parameter (default: `0`)
to specify the size of the table.
Alias: `mk_table` -/
def create (len : ℕ := 0) : table α :=
mk_table len

/-- Convert a list into a table. -/
def from_list (l : list α) : table α :=
(l.map option.some).to_buffer

/-- The length of a table.
Note: this is not the number of values that the table contains.
Some entries may be empty (i.e., `option.none`)
but they count towards the length nonetheless. -/
@[inline] def length : ℕ := t.size

-- def mmap {m} [monad m] (t : table α) (f : α → m β) : m (table β) :=
-- buffer.mmap (option.mmap f) t

def mmap {m : Type v → Type z} [monad m] (f : α → m β) : m (table β) :=
do x ← t.to_array.mmap_copy (mk_array t.length none) (λ a : option α,
   match a with
   | none := pure none
   | some a := do v ← f a, pure $ some v
   end),
   return x.to_buffer

/-- Map a function over a table. -/
def map (f : α → β) : table β := buffer.map' (option.map f) t

/-- Convert an array into a table. -/
def from_array {n : ℕ} (a : array n α) : table α :=
(array.map' option.some a).to_buffer

/-- Read an entry from a table, or return `none` when the index is out of bounds.
Alias: `table.get` -/
@[inline] def read' (r : ℕ) : option α := t.read' r

/-- Read an entry from a table, or return `none` when the index is out of bounds.
Alias: `table.read'` -/
@[inline] def get (r : ℕ) : option α := t.read' r

/-- Returns true if there is a value present in the table at the given index. -/
@[inline] def contains (r : ℕ) : bool := (t.get r).is_some

/-- Returns a value from a table,
or the default term if there is no value present at the given index. -/
@[inline] def iget [inhabited α] (r : ℕ) : α :=
match t.get r with
| none := default α
| some a := a
end

/-- Write a value to a table, or do nothing if the index is out of bounds.
Alias: `table.set` -/
@[inline] def write' (r : ℕ) (a : α) : table α := t.write' r a

/-- Write a value to a table, or do nothing if the index is out of bounds.
Alias: `table.write'` -/
@[inline] def set (r : ℕ) (a : α) : table α := t.write' r a

/-- Push a value onto the back of a table. -/
@[inline] def push_back (a : α) : table α := t.push_back a

/-- Pop a value from the back of a table. -/
@[inline] def pop_back (t : table α) : table α := t.pop_back

/-- Append a list to the end of a table. -/
@[inline] def append_list (l : list α) : table α :=
buffer.append_list t $ l.map option.some

/-- Find a value in a table that satisfies a given predicate, starting from a given index. -/
def find_from (p : α → Prop) [decidable_pred p] : ℕ → option α
| i := if h : i < t.length then
        have wf : t.length - (i + 1) < t.length - i,
          from nat.lt_of_succ_le $ by rw [← nat.succ_sub h, nat.succ_sub_succ],
        match t.get i with
        | none   := find_from (i + 1)
        | some a := if p a then some a else find_from (i + 1)
         end else none
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ i, t.length - i)⟩]}

/-- Find a value in a table that satisfies a given predicate -/
@[inline] def find (p : α → Prop) [decidable_pred p] : option α :=
t.find_from p 0

/-- Fold a table by a binary function and a default value. -/
def foldl (f : β → α → β) (b : β) (t : table α) : β :=
t.foldl b (λ a : option α, λ b : β,
  match a with
  | none := b
  | some a := f b a
  end)

/-- Convert a table to a list, omitting empty entries (i.e., entries with value `option.none`). -/
def to_list : list α := t.foldl list.concat []

meta instance [has_to_string α] : has_to_string (table α) := ⟨λ t, to_string t.to_list⟩

end table
