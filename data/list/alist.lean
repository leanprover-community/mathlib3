/-
Copyright (c) 2018 Sean Leather. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Leather, Mario Carneiro

Association lists.
-/
import data.list.sigma

universes u v w
open list

/-- `alist α β` is a key-value map stored as a linked list.
  It is a wrapper around certain `list` functions with the added constraint
  that the list have unique keys. -/
structure alist (α : Type u) (β : α → Type v) : Type (max u v) :=
(entries : list (sigma β))
(nodupkeys : entries.nodupkeys)

namespace alist
variables {α : Type u} {β : α → Type v}

@[extensionality] theorem ext : ∀ {s t : alist α β}, s.entries = t.entries → s = t
| ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ H := by congr'

/-- The predicate `a ∈ s` means that `s` has a value associated to the key `a`. -/
instance : has_mem α (alist α β) := ⟨λ a s, ∃ b : β a, sigma.mk a b ∈ s.entries⟩

theorem mem_def {a : α} {s : alist α β} :
  a ∈ s ↔ ∃ b : β a, sigma.mk a b ∈ s.entries := iff.rfl

theorem mem_of_perm {a : α} {s₁ s₂ : alist α β} (p : s₁.entries ~ s₂.entries) : a ∈ s₁ ↔ a ∈ s₂ :=
exists_congr $ λ b, mem_of_perm p

/-- The list of keys of an association list. -/
def keys (s : alist α β) : list α := s.entries.map sigma.fst

theorem mem_keys {a : α} {s : alist α β} : a ∈ s.keys ↔ a ∈ s :=
by rw [keys, mem_map]; exact
⟨λ ⟨⟨_, b⟩, h, rfl⟩, ⟨b, h⟩, λ ⟨b, h⟩, ⟨_, h, rfl⟩⟩

theorem keys_nodup (s : alist α β) : s.keys.nodup := s.nodupkeys

/-- The empty association list. -/
instance : has_emptyc (alist α β) := ⟨⟨[], nodupkeys_nil⟩⟩

theorem not_mem_empty_entries {s : sigma β} : s ∉ (∅ : alist α β).entries :=
not_mem_nil _

theorem not_mem_empty {a : α} : a ∉ (∅ : alist α β) :=
λ ⟨b, h⟩, not_mem_empty_entries h

@[simp] theorem keys_empty : (∅ : alist α β).keys = [] := rfl

/-- The singleton association list. -/
def singleton (a : α) (b : β a) : alist α β :=
⟨[⟨a, b⟩], nodupkeys_singleton _⟩

@[simp] theorem keys_singleton (a : α) (b : β a) : (singleton a b).keys = [a] := rfl

variables [decidable_eq α]

/-- Look up the value associated to a key in an association list. -/
def lookup (a : α) (s : alist α β) : option (β a) :=
s.entries.lookup a

theorem lookup_is_some {a : α} {s : alist α β} :
  (s.lookup a).is_some ↔ a ∈ s := lookup_is_some

theorem perm_lookup {a : α} {s₁ s₂ : alist α β} (p : s₁.entries ~ s₂.entries) :
  s₁.lookup a = s₂.lookup a :=
perm_lookup _ s₁.nodupkeys s₂.nodupkeys p

instance (a : α) (s : alist α β) : decidable (a ∈ s) :=
decidable_of_iff _ lookup_is_some

/-- Insert a key-value pair into an association list.
  If the key is already present it does nothing. -/
def insert (a : α) (b : β a) (s : alist α β) : alist α β :=
if h : a ∈ s then s else ⟨⟨a, b⟩ :: s.entries,
  nodup_cons.2 ⟨mt mem_keys.1 h, s.nodupkeys⟩⟩

@[simp] theorem insert_of_pos {a : α} {b : β a} {s : alist α β} (h : a ∈ s) :
  insert a b s = s := dif_pos h

theorem insert_entries_of_neg {a : α} {b : β a} {s : alist α β} (h : a ∉ s) :
  (insert a b s).entries = ⟨a, b⟩ :: s.entries := by simp [insert, h]

@[simp] theorem keys_insert (a : α) (b : β a) (s : alist α β) :
  (insert a b s).keys = _root_.insert a s.keys :=
begin
  by_cases a ∈ s,
  { simp [h, mem_keys.2 h] },
  { simp [keys, insert_entries_of_neg h],
    exact (insert_of_not_mem (mt mem_keys.1 h)).symm }
end

@[simp] theorem mem_insert {a a' : α} {b : β a} {s : alist α β} :
  a' ∈ insert a b s ↔ a' = a ∨ a' ∈ s :=
by rw [← mem_keys, ← mem_keys]; simp

theorem perm_insert {a : α} {b : β a} {s₁ s₂ : alist α β}
  (p : s₁.entries ~ s₂.entries) : (insert a b s₁).entries ~ (insert a b s₂).entries :=
begin
  by_cases a ∈ s₁,
  { simp [h, (mem_of_perm p).1 h, p] },
  { simp [insert_entries_of_neg h, insert_entries_of_neg (mt (mem_of_perm p).2 h)],
    exact p.skip _ }
end

/-- Replace a key with a given value in an association list.
  If the key is not present it does nothing. -/
def replace (a : α) (b : β a) (s : alist α β) : alist α β :=
⟨kreplace a b s.entries, (kreplace_nodupkeys a b).2 s.nodupkeys⟩

@[simp] theorem keys_replace (a : α) (b : β a) (s : alist α β) :
  (replace a b s).keys = s.keys :=
kreplace_map_fst _ _ _

@[simp] theorem mem_replace {a a' : α} {b : β a} {s : alist α β} :
  a' ∈ replace a b s ↔ a' ∈ s :=
by rw [← mem_keys, keys_replace, mem_keys]

theorem perm_replace {a : α} {b : β a} {s₁ s₂ : alist α β} :
  s₁.entries ~ s₂.entries → (replace a b s₁).entries ~ (replace a b s₂).entries :=
perm_kreplace s₁.nodupkeys

/-- Fold a function over the key-value pairs in the map. -/
def foldl {δ : Type w} (f : δ → Π a, β a → δ) (d : δ) (m : alist α β) : δ :=
m.entries.foldl (λ r a, f r a.1 a.2) d

/-- Erase a key from the map. If the key is not present it does nothing. -/
def erase (a : α) (s : alist α β) : alist α β :=
⟨kerase a s.entries, kerase_nodupkeys _ s.nodupkeys⟩

@[simp] theorem keys_erase (a : α) (s : alist α β) :
  (erase a s).keys = s.keys.erase a :=
by rw [erase_eq_erasep, keys, keys, erasep_map]; refl

@[simp] theorem mem_erase {a a' : α} {s : alist α β} : a' ∈ erase a s ↔ a' ≠ a ∧ a' ∈ s :=
by rw [← mem_keys, keys_erase, mem_erase_iff_of_nodup s.keys_nodup, mem_keys]

theorem perm_erase {a : α} {s₁ s₂ : alist α β} :
  s₁.entries ~ s₂.entries → (erase a s₁).entries ~ (erase a s₂).entries :=
perm_kerase s₁.nodupkeys

/-- Erase a key from the map, and return the corresponding value, if found. -/
def extract (a : α) (s : alist α β) : option (β a) × alist α β :=
have (kextract a s.entries).2.nodupkeys,
by rw [kextract_eq_lookup_kerase]; exact kerase_nodupkeys _ s.nodupkeys,
match kextract a s.entries, this with
| (b, l), h := (b, ⟨l, h⟩)
end

@[simp] theorem extract_eq_lookup_erase (a : α) (s : alist α β) :
  extract a s = (lookup a s, erase a s) :=
by simp [extract]; split; refl

end alist
