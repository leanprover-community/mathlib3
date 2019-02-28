/-
Copyright (c) 2018 Sean Leather. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Leather, Mario Carneiro

Finite maps over `multiset`.
-/
import data.list.alist data.finset data.pfun

universes u v w
open list
variables {α : Type u} {β : α → Type v}

namespace multiset

/-- Multiset of keys of an association multiset. -/
def keys (s : multiset (sigma β)) : multiset α :=
s.map sigma.fst

@[simp] theorem coe_keys {l : list (sigma β)} :
  keys (l : multiset (sigma β)) = (l.keys : multiset α) :=
rfl

/-- `nodupkeys s` means that `s` has no duplicate keys. -/
def nodupkeys (s : multiset (sigma β)) : Prop :=
quot.lift_on s list.nodupkeys (λ s t p, propext $ perm_nodupkeys p)

@[simp] theorem coe_nodupkeys {l : list (sigma β)} : @nodupkeys α β l ↔ l.nodupkeys := iff.rfl

end multiset

/-- `finmap β` is the type of finite maps over a multiset. It is effectively
  a quotient of `alist β` by permutation of the underlying list. -/
structure finmap (β : α → Type v) : Type (max u v) :=
(entries : multiset (sigma β))
(nodupkeys : entries.nodupkeys)

/-- The quotient map from `alist` to `finmap`. -/
def alist.to_finmap (s : alist β) : finmap β := ⟨s.entries, s.nodupkeys⟩

local notation `⟦`:max a `⟧`:0 := alist.to_finmap a

theorem alist.to_finmap_eq {s₁ s₂ : alist β} :
  ⟦s₁⟧ = ⟦s₂⟧ ↔ s₁.entries ~ s₂.entries :=
by cases s₁; cases s₂; simp [alist.to_finmap]

@[simp] theorem alist.to_finmap_entries (s : alist β) : ⟦s⟧.entries = s.entries := rfl

namespace finmap
open alist

/-- Lift a permutation-respecting function on `alist` to `finmap`. -/
@[elab_as_eliminator] def lift_on
  {γ} (s : finmap β) (f : alist β → γ)
  (H : ∀ a b : alist β, a.entries ~ b.entries → f a = f b) : γ :=
begin
  refine (quotient.lift_on s.1 (λ l, (⟨_, λ nd, f ⟨l, nd⟩⟩ : roption γ))
    (λ l₁ l₂ p, roption.ext' (perm_nodupkeys p) _) : roption γ).get _,
  { exact λ h₁ h₂, H _ _ (by exact p) },
  { have := s.nodupkeys, rcases s.entries with ⟨l⟩, exact id }
end

@[simp] theorem lift_on_to_finmap {γ} (s : alist β) (f : alist β → γ) (H) :
  lift_on ⟦s⟧ f H = f s := by cases s; refl

/-- Lift a permutation-respecting function on 2 `alist`s to 2 `finmap`s. -/
@[elab_as_eliminator] def lift_on₂
  {γ} (s₁ s₂ : finmap β) (f : alist β → alist β → γ)
  (H : ∀ a₁ b₁ a₂ b₂ : alist β, a₁.entries ~ a₂.entries → b₁.entries ~ b₂.entries → f a₁ b₁ = f a₂ b₂) : γ :=
lift_on s₁
  (λ l₁, lift_on s₂ (f l₁) (λ b₁ b₂ p, H _ _ _ _ (perm.refl _) p))
  (λ a₁ a₂ p, have H' : f a₁ = f a₂ := funext (λ _, H _ _ _ _ p (perm.refl _)), by simp only [H'])

@[simp] theorem lift_on₂_to_finmap {γ} (s₁ s₂ : alist β) (f : alist β → alist β → γ) (H) :
  lift_on₂ ⟦s₁⟧ ⟦s₂⟧ f H = f s₁ s₂ :=
by cases s₁; cases s₂; refl

@[elab_as_eliminator] theorem induction_on
  {C : finmap β → Prop} (s : finmap β) (H : ∀ (a : alist β), C ⟦a⟧) : C s :=
by rcases s with ⟨⟨a⟩, h⟩; exact H ⟨a, h⟩

@[extensionality] theorem ext : ∀ {s t : finmap β}, s.entries = t.entries → s = t
| ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ H := by congr'

/-- The predicate `a ∈ s` means that `s` has a value associated to the key `a`. -/
instance : has_mem α (finmap β) := ⟨λ a s, a ∈ s.entries.keys⟩

theorem mem_def {a : α} {s : finmap β} :
  a ∈ s ↔ a ∈ s.entries.keys := iff.rfl

@[simp] theorem mem_to_finmap {a : α} {s : alist β} :
  a ∈ ⟦s⟧ ↔ a ∈ s := iff.rfl

/-- The set of keys of a finite map. -/
def keys (s : finmap β) : finset α :=
⟨s.entries.keys, induction_on s keys_nodup⟩

@[simp] theorem keys_val (s : alist β) : (keys ⟦s⟧).val = s.keys := rfl

@[simp] theorem keys_ext {s₁ s₂ : alist β} :
  keys ⟦s₁⟧ = keys ⟦s₂⟧ ↔ s₁.keys ~ s₂.keys :=
by simp [keys, alist.keys]

theorem mem_keys {a : α} {s : finmap β} : a ∈ s.keys ↔ a ∈ s :=
induction_on s $ λ s, alist.mem_keys

/-- The empty map. -/
instance : has_emptyc (finmap β) := ⟨⟨0, nodupkeys_nil⟩⟩

@[simp] theorem empty_to_finmap (s : alist β) :
  (⟦∅⟧ : finmap β) = ∅ := rfl

theorem not_mem_empty {a : α} : a ∉ (∅ : finmap β) :=
multiset.not_mem_zero a

@[simp] theorem keys_empty : (∅ : finmap β).keys = ∅ := rfl

/-- The singleton map. -/
def singleton (a : α) (b : β a) : finmap β :=
⟨⟨a, b⟩::0, nodupkeys_singleton _⟩

@[simp] theorem keys_singleton (a : α) (b : β a) :
  (singleton a b).keys = finset.singleton a := rfl

variables [decidable_eq α]

/-- Look up the value associated to a key in a map. -/
def lookup (a : α) (s : finmap β) : option (β a) :=
lift_on s (lookup a) (λ s t, perm_lookup)

@[simp] theorem lookup_to_finmap (a : α) (s : alist β) :
  lookup a ⟦s⟧ = s.lookup a := rfl

theorem lookup_is_some {a : α} {s : finmap β} :
  (s.lookup a).is_some ↔ a ∈ s :=
induction_on s $ λ s, alist.lookup_is_some

theorem lookup_eq_none {a} {s : finmap β} : lookup a s = none ↔ a ∉ s :=
induction_on s $ λ s, alist.lookup_eq_none

instance (a : α) (s : finmap β) : decidable (a ∈ s) :=
decidable_of_iff _ lookup_is_some

/-- Replace a key with a given value in a finite map.
  If the key is not present it does nothing. -/
def replace (a : α) (b : β a) (s : finmap β) : finmap β :=
lift_on s (λ t, ⟦replace a b t⟧) $
λ s₁ s₂ p, to_finmap_eq.2 $ perm_replace p

@[simp] theorem replace_to_finmap (a : α) (b : β a) (s : alist β) :
  replace a b ⟦s⟧ = ⟦s.replace a b⟧ := by simp [replace]

@[simp] theorem keys_replace (a : α) (b : β a) (s : finmap β) :
  (replace a b s).keys = s.keys :=
induction_on s $ λ s, by simp

@[simp] theorem mem_replace {a a' : α} {b : β a} {s : finmap β} :
  a' ∈ replace a b s ↔ a' ∈ s :=
induction_on s $ λ s, by simp

/-- Fold a commutative function over the key-value pairs in the map -/
def foldl {δ : Type w} (f : δ → Π a, β a → δ)
  (H : ∀ d a₁ b₁ a₂ b₂, f (f d a₁ b₁) a₂ b₂ = f (f d a₂ b₂) a₁ b₁)
  (d : δ) (m : finmap β) : δ :=
m.entries.foldl (λ d s, f d s.1 s.2) (λ d s t, H _ _ _ _ _) d

/-- Erase a key from the map. If the key is not present it does nothing. -/
def erase (a : α) (s : finmap β) : finmap β :=
lift_on s (λ t, ⟦erase a t⟧) $
λ s₁ s₂ p, to_finmap_eq.2 $ perm_erase p

@[simp] theorem erase_to_finmap (a : α) (s : alist β) :
  erase a ⟦s⟧ = ⟦s.erase a⟧ := by simp [erase]

@[simp] theorem keys_erase_to_finset (a : α) (s : alist β) :
  keys ⟦s.erase a⟧ = (keys ⟦s⟧).erase a :=
by simp [finset.erase, keys, alist.erase, keys_kerase]

@[simp] theorem keys_erase (a : α) (s : finmap β) :
  (erase a s).keys = s.keys.erase a :=
induction_on s $ λ s, by simp

@[simp] theorem mem_erase {a a' : α} {s : finmap β} : a' ∈ erase a s ↔ a' ≠ a ∧ a' ∈ s :=
induction_on s $ λ s, by simp

@[simp] theorem lookup_erase (a) (s : finmap β) : lookup a (erase a s) = none :=
induction_on s $ lookup_erase a

@[simp] theorem lookup_erase_ne {a a'} {s : finmap β} (h : a ≠ a') :
  lookup a' (erase a s) = lookup a' s :=
induction_on s $ λ s, lookup_erase_ne h

/- insert -/

/-- Insert a key-value pair into a finite map, replacing any existing pair with
  the same key. -/
def insert (a : α) (b : β a) (s : finmap β) : finmap β :=
lift_on s (λ t, ⟦insert a b t⟧) $
λ s₁ s₂ p, to_finmap_eq.2 $ perm_insert p

@[simp] theorem insert_to_finmap (a : α) (b : β a) (s : alist β) :
  insert a b ⟦s⟧ = ⟦s.insert a b⟧ := by simp [insert]

theorem insert_entries_of_neg {a : α} {b : β a} {s : finmap β} : a ∉ s →
  (insert a b s).entries = ⟨a, b⟩ :: s.entries :=
induction_on s $ λ s h,
by simp [insert_entries_of_neg (mt mem_to_finmap.1 h)]

@[simp] theorem mem_insert {a a' : α} {b : β a} {s : finmap β} :
  a' ∈ insert a b s ↔ a = a' ∨ a' ∈ s :=
induction_on s mem_insert

@[simp] theorem lookup_insert {a} {b : β a} (s : finmap β) :
  lookup a (insert a b s) = some b :=
induction_on s $ λ s,
by simp only [insert_to_finmap, lookup_to_finmap, lookup_insert]

/- extract -/

/-- Erase a key from the map, and return the corresponding value, if found. -/
def extract (a : α) (s : finmap β) : option (β a) × finmap β :=
lift_on s (λ t, prod.map id to_finmap (extract a t)) $
λ s₁ s₂ p, by simp [perm_lookup p, to_finmap_eq, perm_erase p]

@[simp] theorem extract_eq_lookup_erase (a : α) (s : finmap β) :
  extract a s = (lookup a s, erase a s) :=
induction_on s $ λ s, by simp [extract]

end finmap
