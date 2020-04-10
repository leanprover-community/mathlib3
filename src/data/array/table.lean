/-
Copyright (c) 2018 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek
-/

import data.list
import data.array.defs

import tactic.lint

/-!
# Tables

A `table` is a self-resizing array-backed list,
which uses opaque references called `table_ref`s for access.
-/

universe variables u v w z

attribute [inline] bool.decidable_eq option.is_some option.is_none list.head
attribute [inline] array.read array.write

/-- `table_ref` is a type alias for `ℕ`. -/
@[irreducible] def table_ref : Type := ℕ

namespace table_ref

section internal

local attribute [reducible] table_ref

/-- A natural number, viewed as `table_ref`. -/
def of_nat (r : ℕ) : table_ref := r

/-- A `table_ref`, viewed as natural number. -/
def to_nat (r : table_ref) : ℕ := r

/-- The succesor function on `table_ref`s. -/
def next (r : table_ref) : table_ref := of_nat (r + 1)

lemma to_nat_next (r : table_ref) : r.next.to_nat = r.to_nat + 1 := rfl

instance : decidable_eq table_ref := by apply_instance

instance : inhabited table_ref := by apply_instance

instance : has_well_founded table_ref := by apply_instance

instance : has_to_string table_ref := by apply_instance

meta instance : has_to_format table_ref := by apply_instance

end internal

/-- A function to convert a `table_ref` to a `string`. -/
def to_string (r : table_ref) : string := to_string r.to_nat

/-- The `table_ref` `null` is implemented as the natural number `0xFFFFFFFF`. -/
def null  : table_ref := of_nat 0xFFFFFFFF

/-- The first `table_ref`; implemented as the natural number `0`. -/
def first : table_ref := of_nat 0

end table_ref

/-- An `indexed` type is a type endowed with a indexing function to `table_ref`. -/
class indexed (α : Type u) :=
(index : α → table_ref)

/-- A type `α` is `keyed` on a type `κ` with dedicable equality,
if `α` endowed with a keying function to `κ`. -/
class keyed (α : Type u) (κ : Type v) [decidable_eq κ] :=
(key : α → κ)

/-- A `table` is a self-resizing array-backed list. -/
structure table (α : Type u) :=
(next_id : table_ref)
(buff_len : ℕ)
(entries : array buff_len (option α))

namespace table

variables {α : Type u} {β : Type v} {κ : Type w} [decidable_eq κ] (t : table α)

-- TODO use push_back and pop_back builtins to avoid array preallocation
-- TODO several recusion-induced-meta can be removed from the file (given proofs)

/-- The default buffer length for tables. -/
def DEFAULT_BUFF_LEN := 10

/-- Initialize a new table, with all entries set to `none`. -/
def create (buff_len : ℕ := DEFAULT_BUFF_LEN) : table α :=
⟨table_ref.first, buff_len, mk_array buff_len none⟩

instance : inhabited (table α) := ⟨create⟩

/-- Turn a `list α` into a `table α`. -/
def from_list (l : list α) : table α :=
let n := l.length in
let buff : array n (option α) := mk_array n none in
⟨table_ref.of_nat n, n, buff.map_copy_from_list some l⟩

/-- Turn an array into a table, while mapping the entries through a function. -/
def from_map_array {dim : ℕ} (x : array dim α) (f : α → β) : table β :=
let buff : array dim (option β) := mk_array dim none in
⟨table_ref.of_nat dim, dim, x.map_copy buff (some ∘ f)⟩

/-- Turn an array into a table. -/
def from_array {dim : ℕ} (x : array dim α) : table α :=
from_map_array x id

/-- Predicate that decides whether a table is full. -/
@[inline] def is_full : bool := t.next_id.to_nat = t.buff_len

/-- Turn a `table_ref` into `option (fin t.buff_len)`, where `t` is a table. -/
@[inline] def try_fin (r : table_ref) : option (fin t.buff_len) :=
let r := r.to_nat in
if h : r < t.buff_len then fin.mk r h else none

/-- Double the size of a `table`
by appending `buff_len` entries to the end that are initialized to `none`. -/
@[inline] def grow : table α :=
let new_len := t.buff_len * 2 in
let new_buff : array new_len (option α) := mk_array new_len none in
{t with buff_len := new_len, entries := array.copy t.entries new_buff}

/-- Fetch the `r`-th entry of a table, or return `none`. -/
@[inline] def at_ref (r : table_ref) : option α :=
match try_fin t r with
| none := none
| some r := t.entries.read r
end

/-- Predicate that determines whether a value is present at the `r`-th entry of a table `t`. -/
@[inline] def present (r : table_ref) : bool := (t.at_ref r).is_some

/-- Fetch the `r`-th entry of a table, or return `none`. -/
@[inline] def get (r : table_ref) : option α := t.at_ref r

/-- Fetch the `r`-th entry of a table, or return  the default element. -/
@[inline] def iget [inhabited α] (r : table_ref) : α :=
match t.at_ref r with
| none := default α
| some a := a
end

/-- Set the `r`-th entry of table `t` to the value `a`, provided `r` is in bounds.
Otherwise, do nothing. -/
@[inline] def set (r : table_ref) (a : α) : table α :=
match try_fin t r with
| none := t
| some r := {t with entries := t.entries.write r a}
end

/-- Push a value to the end of a table. -/
@[inline] def alloc (a : α) : table α :=
let t : table α := if t.is_full then t.grow else t in
let t := t.set t.next_id a in
{ t with next_id := t.next_id.next }

/-- Push a list of values to the end of a table. -/
@[inline] def alloc_list : table α → list α → table α
| t [] := t
| t (a :: rest) := alloc_list (t.alloc a) rest

/-- Given a term `a` of an indexed type, `t.update a` will write `a` to the `i`-th entry of `t`,
where `i` is the index of `a`. -/
@[inline] def update [indexed α] (a : α) : table α := t.set (indexed.index a) a

/-- The length of a table. -/
@[inline] def length : ℕ := t.next_id.to_nat

lemma to_nat_lt_buff_len_of_present {r : table_ref} (h : t.present r) :
  r.to_nat < t.buff_len :=
begin
  rw [present, option.is_some_iff_exists] at h,
  cases h with a ha,
  by_contra H,
  have aux : t.try_fin r = none,
  { delta try_fin, rw dif_neg H },
  rw [at_ref, aux] at ha,
  exact option.no_confusion ha,
end

/-- Find an entry in a table satisfying a given predicate, starting from a given `table_ref` -/
def find_from (p : α → Prop) [decidable_pred p] : table_ref → option α
| ref := if h : t.present ref then
          match t.at_ref ref with
         | none := none
         | some a := if p a then some a
            else have wf : (t.buff_len - ref.next.to_nat) < t.buff_len - ref.to_nat,
              from nat.lt_of_succ_le $
                begin
                  rw [table_ref.to_nat_next, ← nat.succ_sub, nat.succ_sub_succ],
                  apply t.to_nat_lt_buff_len_of_present h,
                end,
            find_from ref.next
         end else none
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ a, t.buff_len - a.to_nat)⟩]}

/-- Find an entry in a table satisfying a given predicate. -/
@[inline] def find (p : α → Prop) [decidable_pred p] : option α :=
t.find_from p table_ref.first

/-- Find an entry in a table that has a given key. -/
@[inline] def find_key [keyed α κ] (key : κ) : option α :=
t.find (λ a, key = @keyed.key _ _ _ _ a)

/-- Fold an operation over a table. -/
def foldl (f : β → α → β) (b : β) (t : table α) : β :=
t.entries.foldl b (λ a : option α, λ b : β,
  match a with
  | none := b
  | some a := f b a
  end)

/-- An empty array of the same size as the table `t`.
Here “empty” means that all entries are initialized to `none`. -/
private def empty_buff (t : table α) : array t.buff_len (option β) :=
mk_array t.buff_len none

/-- Map a function over all entries of a table. -/
def map (f : α → β) : table β :=
{t with entries := t.entries.map_copy (empty_buff t) (option.map f)}

/-- Monadically map a function over all entries in a table. -/
def mmap {m : Type v → Type z} [monad m] (f : α → m β) : m (table β) :=
do new_buff ← t.entries.mmap_copy (empty_buff t) (λ a : option α,
   match a with
   | none := pure none
   | some a := do v ← f a, pure $ some v
   end),
   return ⟨t.next_id, t.buff_len, new_buff⟩

/-- Predicate that expresses that a `table_ref` is out of bounds. -/
def is_after_last (r : table_ref) : bool := t.next_id.to_nat ≤ r.to_nat

/-- Convert a table to a list. -/
def to_list : list α := t.foldl list.concat []

instance [has_to_string α] : has_to_string (table α) := ⟨λ t, to_string t.to_list⟩

end table
