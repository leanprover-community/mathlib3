/-
Copyright (c) 2018 Sean Leather. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Leather, Mario Carneiro

Finite maps over `multiset`.
-/
import data.list.alist data.multiset data.pfun

universes u v w
open list

namespace multiset
variables {α : Type*} {β : α → Type*}

/-- `nodupkeys s` means that `s` has no duplicate keys. -/
def nodupkeys (s : multiset (sigma β)) : Prop :=
quot.lift_on s list.nodupkeys (λ s t p, propext $ perm_nodupkeys p)

@[simp] theorem coe_nodupkeys {l : list (sigma β)} : @nodupkeys α β l ↔ l.nodupkeys := iff.rfl

end multiset

/-- `finmap α β` is the type of finite maps over a multiset. It is effectively
  a quotient of `alist α β` by permutation of the underlying list. -/
structure finmap (α : Type u) (β : α → Type v) : Type (max u v) :=
(entries : multiset (sigma β))
(nodupkeys : entries.nodupkeys)

/-- The quotient map from `alist` to `finmap`. -/
def alist.to_finmap {α β} (s : alist α β) : finmap α β := ⟨s.entries, s.nodupkeys⟩
local notation `⟦`:max a `⟧`:0 := alist.to_finmap a

theorem alist.to_finmap_eq {α β} {s₁ s₂ : alist α β} :
  ⟦s₁⟧ = ⟦s₂⟧ ↔ s₁.entries ~ s₂.entries :=
by cases s₁; cases s₂; simp [alist.to_finmap]

@[simp] theorem alist.to_finmap_entries {α β} (s : alist α β) : ⟦s⟧.entries = s.entries := rfl

namespace finmap
variables {α : Type u} {β : α → Type v}
open alist

/-- Lift a permutation-respecting function on `alist` to `finmap`. -/
@[elab_as_eliminator] def lift_on
  {γ} (s : finmap α β) (f : alist α β → γ)
  (H : ∀ a b : alist α β, a.entries ~ b.entries → f a = f b) : γ :=
begin
  refine (quotient.lift_on s.1 (λ l, (⟨_, λ nd, f ⟨l, nd⟩⟩ : roption γ))
    (λ l₁ l₂ p, roption.ext' (perm_nodupkeys p) _) : roption γ).get _,
  { exact λ h₁ h₂, H _ _ (by exact p) },
  { have := s.nodupkeys, rcases s.entries with ⟨l⟩, exact id }
end

@[simp] theorem lift_on_to_finmap {γ} (s : alist α β) (f : alist α β → γ) (H) :
  lift_on ⟦s⟧ f H = f s := by cases s; refl

@[elab_as_eliminator] theorem induction_on
  {C : finmap α β → Prop} (s : finmap α β) (H : ∀ a, C ⟦a⟧) : C s :=
by rcases s with ⟨⟨a⟩, h⟩; exact H ⟨a, h⟩

@[extensionality] theorem ext : ∀ {s t : finmap α β}, s.entries = t.entries → s = t
| ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ H := by congr'

/-- The predicate `a ∈ s` means that `s` has a value associated to the key `a`. -/
instance : has_mem α (finmap α β) := ⟨λ a s, ∃ b : β a, sigma.mk a b ∈ s.entries⟩

theorem mem_def {a : α} {s : finmap α β} :
  a ∈ s ↔ ∃ b : β a, sigma.mk a b ∈ s.entries := iff.rfl

@[simp] theorem mem_to_finmap {a : α} {s : alist α β} :
  a ∈ ⟦s⟧ ↔ a ∈ s := iff.rfl

/-- The list of keys of a finite map. -/
def keys (s : finmap α β) : multiset α := s.entries.map sigma.fst

@[simp] theorem keys_to_finmap (s : alist α β) :
  keys ⟦s⟧ = s.keys := rfl

theorem mem_keys {a : α} {s : finmap α β} : a ∈ s.keys ↔ a ∈ s :=
induction_on s $ λ s, mem_keys

theorem keys_nodup (s : finmap α β) : s.keys.nodup :=
induction_on s $ λ s, s.keys_nodup

/-- The empty map. -/
instance : has_emptyc (finmap α β) := ⟨⟨0, nodupkeys_nil⟩⟩

@[simp] theorem empty_to_finmap (s : alist α β) :
  (⟦∅⟧ : finmap α β) = ∅ := rfl

theorem not_mem_empty_entries {s : sigma β} : s ∉ (∅ : finmap α β).entries :=
multiset.not_mem_zero _

theorem not_mem_empty {a : α} : a ∉ (∅ : finmap α β) :=
λ ⟨b, h⟩, not_mem_empty_entries h

@[simp] theorem keys_empty : (∅ : finmap α β).keys = 0 := rfl

/-- The singleton map. -/
def singleton (a : α) (b : β a) : finmap α β :=
⟨⟨a, b⟩::0, nodupkeys_singleton _⟩

@[simp] theorem keys_singleton (a : α) (b : β a) : (singleton a b).keys = [a] := rfl

variables [decidable_eq α]

/-- Look up the value associated to a key in a map. -/
def lookup (a : α) (s : finmap α β) : option (β a) :=
lift_on s (lookup a) (λ s t, perm_lookup)

@[simp] theorem lookup_to_finmap (a : α) (s : alist α β) :
  lookup a ⟦s⟧ = s.lookup a := rfl

theorem lookup_is_some {a : α} {s : finmap α β} :
  (s.lookup a).is_some ↔ a ∈ s :=
induction_on s $ λ s, alist.lookup_is_some

instance (a : α) (s : finmap α β) : decidable (a ∈ s) :=
decidable_of_iff _ lookup_is_some

/-- Insert a key-value pair into a finite map.
  If the key is already present it does nothing. -/
def insert (a : α) (b : β a) (s : finmap α β) : finmap α β :=
lift_on s (λ t, ⟦insert a b t⟧) $
λ s₁ s₂ p, to_finmap_eq.2 $ perm_insert p

@[simp] theorem insert_to_finset (a : α) (b : β a) (s : alist α β) :
  insert a b ⟦s⟧ = ⟦s.insert a b⟧ := by simp [insert]

@[simp] theorem insert_of_pos {a : α} {b : β a} {s : finmap α β} : a ∈ s →
  insert a b s = s :=
induction_on s $ λ ⟨s, nd⟩ h, congr_arg to_finmap $
insert_of_pos (mem_to_finmap.2 h)

theorem insert_entries_of_neg {a : α} {b : β a} {s : finmap α β} : a ∉ s →
  (insert a b s).entries = ⟨a, b⟩ :: s.entries :=
induction_on s $ λ s h,
by simp [insert_entries_of_neg (mt mem_to_finmap.1 h)]

@[simp] theorem keys_insert (a : α) (b : β a) (s : finmap α β) :
  (insert a b s).keys = s.keys.ndinsert a :=
induction_on s $ λ s, by simp

@[simp] theorem mem_insert {a a' : α} {b : β a} {s : finmap α β} :
  a' ∈ insert a b s ↔ a' = a ∨ a' ∈ s :=
by rw [← mem_keys, ← mem_keys]; simp

/-- Replace a key with a given value in a finite map.
  If the key is not present it does nothing. -/
def replace (a : α) (b : β a) (s : finmap α β) : finmap α β :=
lift_on s (λ t, ⟦replace a b t⟧) $
λ s₁ s₂ p, to_finmap_eq.2 $ perm_replace p

@[simp] theorem replace_to_finset (a : α) (b : β a) (s : alist α β) :
  replace a b ⟦s⟧ = ⟦s.replace a b⟧ := by simp [replace]

@[simp] theorem keys_replace (a : α) (b : β a) (s : finmap α β) :
  (replace a b s).keys = s.keys :=
induction_on s $ λ s, by simp

@[simp] theorem mem_replace {a a' : α} {b : β a} {s : finmap α β} :
  a' ∈ replace a b s ↔ a' ∈ s :=
induction_on s $ λ s, by simp

/-- Fold a commutative function over the key-value pairs in the map -/
def foldl {δ : Type w} (f : δ → Π a, β a → δ)
  (H : ∀ d a₁ b₁ a₂ b₂, f (f d a₁ b₁) a₂ b₂ = f (f d a₂ b₂) a₁ b₁)
  (d : δ) (m : finmap α β) : δ :=
m.entries.foldl (λ d s, f d s.1 s.2) (λ d s t, H _ _ _ _ _) d

/-- Erase a key from the map. If the key is not present it does nothing. -/
def erase (a : α) (s : finmap α β) : finmap α β :=
lift_on s (λ t, ⟦erase a t⟧) $
λ s₁ s₂ p, to_finmap_eq.2 $ perm_erase p

@[simp] theorem erase_to_finset (a : α) (s : alist α β) :
  erase a ⟦s⟧ = ⟦s.erase a⟧ := by simp [erase]

@[simp] theorem keys_erase (a : α) (s : finmap α β) :
  (erase a s).keys = s.keys.erase a :=
induction_on s $ λ s, by simp

@[simp] theorem mem_erase {a a' : α} {s : finmap α β} : a' ∈ erase a s ↔ a' ≠ a ∧ a' ∈ s :=
induction_on s $ λ s, by simp

/-- Erase a key from the map, and return the corresponding value, if found. -/
def extract (a : α) (s : finmap α β) : option (β a) × finmap α β :=
lift_on s (λ t, prod.map id to_finmap (extract a t)) $
λ s₁ s₂ p, by simp [perm_lookup p, to_finmap_eq, perm_erase p]

@[simp] theorem extract_eq_lookup_erase (a : α) (s : finmap α β) :
  extract a s = (lookup a s, erase a s) :=
induction_on s $ λ s, by simp [extract]

end finmap
