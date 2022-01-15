/-
Copyright (c) 2018 Sean Leather. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Leather, Mario Carneiro
-/
import data.list.sigma

/-!
# Association Lists

This file defines association lists. An association list is a list where every element consists of
a key and a value, and no two entries have the same key. The type of the value is allowed to be
dependent on the type of the key.

This type dependence is implemented using `sigma`: The elements of the list are of type `sigma β`,
for some type index `β`.

## Main definitions

Association lists are represented by the `alist` structure. This file defines this structure and
provides ways to access, modify, and combine `alist`s.

* `alist.keys` returns a list of keys of the alist.
* `alist.mem` returns membership in the set of keys.
* `alist.erase` removes a certain key.
* `alist.insert` adds a key-value mapping to the list.
* `alist.union` combines two association lists.

## References

* <https://en.wikipedia.org/wiki/Association_list>

-/

universes u v w
open list
variables {α : Type u} {β : α → Type v}

/-- `alist β` is a key-value map stored as a `list` (i.e. a linked list).
  It is a wrapper around certain `list` functions with the added constraint
  that the list have unique keys. -/
structure alist (β : α → Type v) : Type (max u v) :=
(entries : list (sigma β))
(nodupkeys : entries.nodupkeys)

/-- Given `l : list (sigma β)`, create a term of type `alist β` by removing
entries with duplicate keys. -/
def list.to_alist [decidable_eq α] {β : α → Type v} (l : list (sigma β)) : alist β :=
{ entries := _,
  nodupkeys := nodupkeys_erase_dupkeys l }

namespace alist

@[ext] theorem ext : ∀ {s t : alist β}, s.entries = t.entries → s = t
| ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ H := by congr'

lemma ext_iff {s t : alist β} : s = t ↔ s.entries = t.entries :=
⟨congr_arg _, ext⟩

instance [decidable_eq α] [∀ a, decidable_eq (β a)] : decidable_eq (alist β) :=
λ xs ys, by rw ext_iff; apply_instance

/-! ### keys -/

/-- The list of keys of an association list. -/
def keys (s : alist β) : list α := s.entries.keys

theorem keys_nodup (s : alist β) : s.keys.nodup := s.nodupkeys

/-! ### mem -/

/-- The predicate `a ∈ s` means that `s` has a value associated to the key `a`. -/
instance : has_mem α (alist β) := ⟨λ a s, a ∈ s.keys⟩

theorem mem_keys {a : α} {s : alist β} : a ∈ s ↔ a ∈ s.keys := iff.rfl

theorem mem_of_perm {a : α} {s₁ s₂ : alist β} (p : s₁.entries ~ s₂.entries) : a ∈ s₁ ↔ a ∈ s₂ :=
(p.map sigma.fst).mem_iff

/-! ### empty -/

/-- The empty association list. -/
instance : has_emptyc (alist β) := ⟨⟨[], nodupkeys_nil⟩⟩

instance : inhabited (alist β) := ⟨∅⟩

theorem not_mem_empty (a : α) : a ∉ (∅ : alist β) :=
not_mem_nil a

@[simp] theorem empty_entries : (∅ : alist β).entries = [] := rfl

@[simp] theorem keys_empty : (∅ : alist β).keys = [] := rfl

/-! ### singleton -/

/-- The singleton association list. -/
def singleton (a : α) (b : β a) : alist β :=
⟨[⟨a, b⟩], nodupkeys_singleton _⟩

@[simp] theorem singleton_entries (a : α) (b : β a) :
  (singleton a b).entries = [sigma.mk a b] := rfl

@[simp] theorem keys_singleton (a : α) (b : β a) : (singleton a b).keys = [a] := rfl

/-! ### lookup -/

section

variables [decidable_eq α]

/-- Look up the value associated to a key in an association list. -/
def lookup (a : α) (s : alist β) : option (β a) :=
s.entries.lookup a

@[simp] theorem lookup_empty (a) : lookup a (∅ : alist β) = none :=
rfl

theorem lookup_is_some {a : α} {s : alist β} :
  (s.lookup a).is_some ↔ a ∈ s := lookup_is_some

theorem lookup_eq_none {a : α} {s : alist β} :
  lookup a s = none ↔ a ∉ s :=
lookup_eq_none

theorem perm_lookup {a : α} {s₁ s₂ : alist β} (p : s₁.entries ~ s₂.entries) :
  s₁.lookup a = s₂.lookup a :=
perm_lookup _ s₁.nodupkeys s₂.nodupkeys p

instance (a : α) (s : alist β) : decidable (a ∈ s) :=
decidable_of_iff _ lookup_is_some

/-! ### replace -/

/-- Replace a key with a given value in an association list.
  If the key is not present it does nothing. -/
def replace (a : α) (b : β a) (s : alist β) : alist β :=
⟨kreplace a b s.entries, (kreplace_nodupkeys a b).2 s.nodupkeys⟩

@[simp] theorem keys_replace (a : α) (b : β a) (s : alist β) :
  (replace a b s).keys = s.keys :=
keys_kreplace _ _ _

@[simp] theorem mem_replace {a a' : α} {b : β a} {s : alist β} :
  a' ∈ replace a b s ↔ a' ∈ s :=
by rw [mem_keys, keys_replace, ←mem_keys]

theorem perm_replace {a : α} {b : β a} {s₁ s₂ : alist β} :
  s₁.entries ~ s₂.entries → (replace a b s₁).entries ~ (replace a b s₂).entries :=
perm.kreplace s₁.nodupkeys

end

/-- Fold a function over the key-value pairs in the map. -/
def foldl {δ : Type w} (f : δ → Π a, β a → δ) (d : δ) (m : alist β) : δ :=
m.entries.foldl (λ r a, f r a.1 a.2) d

/-! ### erase -/

section

variables [decidable_eq α]

/-- Erase a key from the map. If the key is not present, do nothing. -/
def erase (a : α) (s : alist β) : alist β :=
⟨kerase a s.entries, kerase_nodupkeys _ s.nodupkeys⟩

@[simp] theorem keys_erase (a : α) (s : alist β) :
  (erase a s).keys = s.keys.erase a :=
by simp only [erase, keys, keys_kerase]

@[simp] theorem mem_erase {a a' : α} {s : alist β} : a' ∈ erase a s ↔ a' ≠ a ∧ a' ∈ s :=
by rw [mem_keys, keys_erase, mem_erase_iff_of_nodup s.keys_nodup, ←mem_keys]

theorem perm_erase {a : α} {s₁ s₂ : alist β} :
  s₁.entries ~ s₂.entries → (erase a s₁).entries ~ (erase a s₂).entries :=
perm.kerase s₁.nodupkeys

@[simp] theorem lookup_erase (a) (s : alist β) : lookup a (erase a s) = none :=
lookup_kerase a s.nodupkeys

@[simp] theorem lookup_erase_ne {a a'} {s : alist β} (h : a ≠ a') :
  lookup a (erase a' s) = lookup a s :=
lookup_kerase_ne h

theorem erase_erase (a a' : α) (s : alist β) :
  (s.erase a).erase a' = (s.erase a').erase a :=
ext $ kerase_kerase

/-! ### insert -/

/-- Insert a key-value pair into an association list and erase any existing pair
  with the same key. -/
def insert (a : α) (b : β a) (s : alist β) : alist β :=
⟨kinsert a b s.entries, kinsert_nodupkeys a b s.nodupkeys⟩

@[simp] theorem insert_entries {a} {b : β a} {s : alist β} :
  (insert a b s).entries = sigma.mk a b :: kerase a s.entries :=
rfl

theorem insert_entries_of_neg {a} {b : β a} {s : alist β} (h : a ∉ s) :
  (insert a b s).entries = ⟨a, b⟩ :: s.entries :=
by rw [insert_entries, kerase_of_not_mem_keys h]

@[simp] theorem mem_insert {a a'} {b' : β a'} (s : alist β) :
  a ∈ insert a' b' s ↔ a = a' ∨ a ∈ s :=
mem_keys_kinsert

@[simp] theorem keys_insert {a} {b : β a} (s : alist β) :
  (insert a b s).keys = a :: s.keys.erase a :=
by simp [insert, keys, keys_kerase]

theorem perm_insert {a} {b : β a} {s₁ s₂ : alist β} (p : s₁.entries ~ s₂.entries) :
  (insert a b s₁).entries ~ (insert a b s₂).entries :=
by simp only [insert_entries]; exact p.kinsert s₁.nodupkeys

@[simp] theorem lookup_insert {a} {b : β a} (s : alist β) : lookup a (insert a b s) = some b :=
by simp only [lookup, insert, lookup_kinsert]

@[simp] theorem lookup_insert_ne {a a'} {b' : β a'} {s : alist β} (h : a ≠ a') :
  lookup a (insert a' b' s) = lookup a s :=
lookup_kinsert_ne h

@[simp] theorem lookup_to_alist {a} (s : list (sigma β)) : lookup a s.to_alist = s.lookup a :=
by rw [list.to_alist,lookup,lookup_erase_dupkeys]

@[simp] theorem insert_insert {a} {b b' : β a} (s : alist β) :
  (s.insert a b).insert a b' = s.insert a b' :=
by ext : 1; simp only [alist.insert_entries, list.kerase_cons_eq];
   constructor_matching* [_ ∧ _]; refl

theorem insert_insert_of_ne {a a'} {b : β a} {b' : β a'} (s : alist β) (h : a ≠ a') :
  ((s.insert a b).insert a' b').entries ~ ((s.insert a' b').insert a b).entries :=
by simp only [insert_entries]; rw [kerase_cons_ne,kerase_cons_ne,kerase_comm];
   [apply perm.swap, exact h, exact h.symm]

@[simp] lemma insert_singleton_eq {a : α} {b b' : β a} :
  insert a b (singleton a b') = singleton a b :=
ext $ by simp only [alist.insert_entries, list.kerase_cons_eq, and_self, alist.singleton_entries,
  heq_iff_eq, eq_self_iff_true]

@[simp] theorem entries_to_alist (xs : list (sigma β)) :
  (list.to_alist xs).entries = erase_dupkeys xs := rfl

theorem to_alist_cons (a : α) (b : β a) (xs : list (sigma β)) :
  list.to_alist (⟨a,b⟩ :: xs) = insert a b xs.to_alist := rfl

/-! ### extract -/

/-- Erase a key from the map, and return the corresponding value, if found. -/
def extract (a : α) (s : alist β) : option (β a) × alist β :=
have (kextract a s.entries).2.nodupkeys,
by rw [kextract_eq_lookup_kerase]; exact kerase_nodupkeys _ s.nodupkeys,
match kextract a s.entries, this with
| (b, l), h := (b, ⟨l, h⟩)
end

@[simp] theorem extract_eq_lookup_erase (a : α) (s : alist β) :
  extract a s = (lookup a s, erase a s) :=
by simp [extract]; split; refl

/-! ### union -/

/-- `s₁ ∪ s₂` is the key-based union of two association lists. It is
left-biased: if there exists an `a ∈ s₁`, `lookup a (s₁ ∪ s₂) = lookup a s₁`.
-/
def union (s₁ s₂ : alist β) : alist β :=
⟨kunion s₁.entries s₂.entries, kunion_nodupkeys s₁.nodupkeys s₂.nodupkeys⟩

instance : has_union (alist β) := ⟨union⟩

@[simp] theorem union_entries {s₁ s₂ : alist β} :
  (s₁ ∪ s₂).entries = kunion s₁.entries s₂.entries :=
rfl

@[simp] theorem empty_union {s : alist β} : (∅ : alist β) ∪ s = s :=
ext rfl

@[simp] theorem union_empty {s : alist β} : s ∪ (∅ : alist β) = s :=
ext $ by simp

@[simp] theorem mem_union {a} {s₁ s₂ : alist β} :
  a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ :=
mem_keys_kunion

theorem perm_union {s₁ s₂ s₃ s₄ : alist β}
  (p₁₂ : s₁.entries ~ s₂.entries) (p₃₄ : s₃.entries ~ s₄.entries) :
  (s₁ ∪ s₃).entries ~ (s₂ ∪ s₄).entries :=
by simp [p₁₂.kunion s₃.nodupkeys p₃₄]

theorem union_erase (a : α) (s₁ s₂ : alist β) : erase a (s₁ ∪ s₂) = erase a s₁ ∪ erase a s₂ :=
ext kunion_kerase.symm

@[simp] theorem lookup_union_left {a} {s₁ s₂ : alist β} :
  a ∈ s₁ → lookup a (s₁ ∪ s₂) = lookup a s₁ :=
lookup_kunion_left

@[simp] theorem lookup_union_right {a} {s₁ s₂ : alist β} :
  a ∉ s₁ → lookup a (s₁ ∪ s₂) = lookup a s₂ :=
lookup_kunion_right

@[simp] theorem mem_lookup_union {a} {b : β a} {s₁ s₂ : alist β} :
  b ∈ lookup a (s₁ ∪ s₂) ↔ b ∈ lookup a s₁ ∨ a ∉ s₁ ∧ b ∈ lookup a s₂ :=
mem_lookup_kunion

theorem mem_lookup_union_middle {a} {b : β a} {s₁ s₂ s₃ : alist β} :
  b ∈ lookup a (s₁ ∪ s₃) → a ∉ s₂ → b ∈ lookup a (s₁ ∪ s₂ ∪ s₃) :=
mem_lookup_kunion_middle

theorem insert_union {a} {b : β a} {s₁ s₂ : alist β} :
  insert a b (s₁ ∪ s₂) = insert a b s₁ ∪ s₂ :=
by ext; simp

theorem union_assoc {s₁ s₂ s₃ : alist β} : ((s₁ ∪ s₂) ∪ s₃).entries ~ (s₁ ∪ (s₂ ∪ s₃)).entries :=
lookup_ext (alist.nodupkeys _) (alist.nodupkeys _)
(by simp [decidable.not_or_iff_and_not,or_assoc,and_or_distrib_left,and_assoc])

end

/-! ### disjoint -/

/-- Two associative lists are disjoint if they have no common keys. -/
def disjoint (s₁ s₂ : alist β) : Prop :=
∀ k ∈ s₁.keys, ¬ k ∈ s₂.keys

variables [decidable_eq α]

theorem union_comm_of_disjoint {s₁ s₂ : alist β} (h : disjoint s₁ s₂) :
  (s₁ ∪ s₂).entries ~ (s₂ ∪ s₁).entries :=
lookup_ext (alist.nodupkeys _) (alist.nodupkeys _)
(begin
   intros, simp,
   split; intro h',
   cases h',
   { right, refine ⟨_,h'⟩,
     apply h, rw [keys,← list.lookup_is_some,h'], exact rfl },
   { left, rw h'.2 },
   cases h',
   { right, refine ⟨_,h'⟩, intro h'',
     apply h _ h'', rw [keys,← list.lookup_is_some,h'], exact rfl },
   { left, rw h'.2 },
 end)

end alist
