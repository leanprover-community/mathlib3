/-
Copyright (c) 2018 Sean Leather. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Leather, Mario Carneiro

Association lists.
-/
import data.list.sigma

universes u v w
open list
variables {α : Type u} {β : α → Type v}

/-- `alist β` is a key-value map stored as a `list` (i.e. a linked list).
  It is a wrapper around certain `list` functions with the added constraint
  that the list have unique keys. -/
structure alist (β : α → Type v) : Type (max u v) :=
(entries : list (sigma β))
(nodupkeys : entries.nodupkeys)

namespace alist

@[extensionality] theorem ext : ∀ {s t : alist β}, s.entries = t.entries → s = t
| ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ H := by congr'

/- keys -/

/-- The list of keys of an association list. -/
def keys (s : alist β) : list α := s.entries.keys

theorem keys_nodup (s : alist β) : s.keys.nodup := s.nodupkeys

/- mem -/

/-- The predicate `a ∈ s` means that `s` has a value associated to the key `a`. -/
instance : has_mem α (alist β) := ⟨λ a s, a ∈ s.keys⟩

theorem mem_keys {a : α} {s : alist β} : a ∈ s ↔ a ∈ s.keys := iff.rfl

theorem mem_of_perm {a : α} {s₁ s₂ : alist β} (p : s₁.entries ~ s₂.entries) : a ∈ s₁ ↔ a ∈ s₂ :=
mem_of_perm $ perm_map sigma.fst p

/- empty -/

/-- The empty association list. -/
instance : has_emptyc (alist β) := ⟨⟨[], nodupkeys_nil⟩⟩

theorem not_mem_empty (a : α) : a ∉ (∅ : alist β) :=
not_mem_nil a

@[simp] theorem keys_empty : (∅ : alist β).keys = [] := rfl

/- singleton -/

/-- The singleton association list. -/
def singleton (a : α) (b : β a) : alist β :=
⟨[⟨a, b⟩], nodupkeys_singleton _⟩

@[simp] theorem keys_singleton (a : α) (b : β a) : (singleton a b).keys = [a] := rfl

variables [decidable_eq α]

/- lookup -/

/-- Look up the value associated to a key in an association list. -/
def lookup (a : α) (s : alist β) : option (β a) :=
s.entries.lookup a

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

/- replace -/

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
perm_kreplace s₁.nodupkeys

/-- Fold a function over the key-value pairs in the map. -/
def foldl {δ : Type w} (f : δ → Π a, β a → δ) (d : δ) (m : alist β) : δ :=
m.entries.foldl (λ r a, f r a.1 a.2) d

/- erase -/

/-- Erase a key from the map. If the key is not present it does nothing. -/
def erase (a : α) (s : alist β) : alist β :=
⟨kerase a s.entries, kerase_nodupkeys _ s.nodupkeys⟩

@[simp] theorem keys_erase (a : α) (s : alist β) :
  (erase a s).keys = s.keys.erase a :=
by simp only [erase, keys, keys_kerase]

@[simp] theorem mem_erase {a a' : α} {s : alist β} : a' ∈ erase a s ↔ a' ≠ a ∧ a' ∈ s :=
by rw [mem_keys, keys_erase, mem_erase_iff_of_nodup s.keys_nodup, ←mem_keys]

theorem perm_erase {a : α} {s₁ s₂ : alist β} :
  s₁.entries ~ s₂.entries → (erase a s₁).entries ~ (erase a s₂).entries :=
perm_kerase s₁.nodupkeys

@[simp] theorem lookup_erase (a) (s : alist β) : lookup a (erase a s) = none :=
lookup_kerase a s.nodupkeys

@[simp] theorem lookup_erase_ne {a a'} {s : alist β} (h : a ≠ a') :
  lookup a' (erase a s) = lookup a' s :=
lookup_kerase_ne h

/- insert -/

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

@[simp] theorem mem_insert {a a'} {b : β a} (s : alist β) :
  a' ∈ insert a b s ↔ a = a' ∨ a' ∈ s :=
mem_keys_kinsert

@[simp] theorem keys_insert {a} {b : β a} (s : alist β) :
  (insert a b s).keys = a :: s.keys.erase a :=
by simp [insert, keys, keys_kerase]

theorem perm_insert {a} {b : β a} {s₁ s₂ : alist β} (p : s₁.entries ~ s₂.entries) :
  (insert a b s₁).entries ~ (insert a b s₂).entries :=
by simp only [insert_entries]; exact perm_kinsert s₁.nodupkeys p

@[simp] theorem lookup_insert {a} {b : β a} (s : alist β) : lookup a (insert a b s) = some b :=
by simp only [lookup, insert, lookup_kinsert]

@[simp] theorem lookup_insert_ne {a a'} {b : β a} {s : alist β} (h : a ≠ a') :
  lookup a' (insert a b s) = lookup a' s :=
lookup_kinsert_ne h

/- extract -/

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

end alist
