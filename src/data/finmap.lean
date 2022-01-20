/-
Copyright (c) 2018 Sean Leather. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Leather, Mario Carneiro
-/
import data.list.alist
import data.finset.basic
import data.part
/-!
# Finite maps over `multiset`
-/

universes u v w
open list
variables {α : Type u} {β : α → Type v}

/-! ### multisets of sigma types-/

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

/-! ### finmap -/

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

/-- Given `l : list (sigma β)`, create a term of type `finmap β` by removing
entries with duplicate keys. -/
def list.to_finmap [decidable_eq α] (s : list (sigma β)) : finmap β := s.to_alist.to_finmap

namespace finmap
open alist

/-! ### lifting from alist -/

/-- Lift a permutation-respecting function on `alist` to `finmap`. -/
@[elab_as_eliminator] def lift_on
  {γ} (s : finmap β) (f : alist β → γ)
  (H : ∀ a b : alist β, a.entries ~ b.entries → f a = f b) : γ :=
begin
  refine (quotient.lift_on s.1 (λ l, (⟨_, λ nd, f ⟨l, nd⟩⟩ : part γ))
    (λ l₁ l₂ p, part.ext' (perm_nodupkeys p) _) : part γ).get _,
  { exact λ h₁ h₂, H _ _ (by exact p) },
  { have := s.nodupkeys, rcases s.entries with ⟨l⟩, exact id }
end

@[simp] theorem lift_on_to_finmap {γ} (s : alist β) (f : alist β → γ) (H) :
  lift_on ⟦s⟧ f H = f s := by cases s; refl

/-- Lift a permutation-respecting function on 2 `alist`s to 2 `finmap`s. -/
@[elab_as_eliminator] def lift_on₂
  {γ} (s₁ s₂ : finmap β) (f : alist β → alist β → γ)
  (H : ∀ a₁ b₁ a₂ b₂ : alist β, a₁.entries ~ a₂.entries → b₁.entries ~ b₂.entries →
    f a₁ b₁ = f a₂ b₂) : γ :=
lift_on s₁
  (λ l₁, lift_on s₂ (f l₁) (λ b₁ b₂ p, H _ _ _ _ (perm.refl _) p))
  (λ a₁ a₂ p, have H' : f a₁ = f a₂ := funext (λ _, H _ _ _ _ p (perm.refl _)), by simp only [H'])

@[simp] theorem lift_on₂_to_finmap {γ} (s₁ s₂ : alist β) (f : alist β → alist β → γ) (H) :
  lift_on₂ ⟦s₁⟧ ⟦s₂⟧ f H = f s₁ s₂ :=
by cases s₁; cases s₂; refl

/-! ### induction -/

@[elab_as_eliminator] theorem induction_on
  {C : finmap β → Prop} (s : finmap β) (H : ∀ (a : alist β), C ⟦a⟧) : C s :=
by rcases s with ⟨⟨a⟩, h⟩; exact H ⟨a, h⟩

@[elab_as_eliminator] theorem induction_on₂ {C : finmap β → finmap β → Prop}
  (s₁ s₂ : finmap β) (H : ∀ (a₁ a₂ : alist β), C ⟦a₁⟧ ⟦a₂⟧) : C s₁ s₂ :=
induction_on s₁ $ λ l₁, induction_on s₂ $ λ l₂, H l₁ l₂

@[elab_as_eliminator] theorem induction_on₃ {C : finmap β →  finmap β → finmap β → Prop}
  (s₁ s₂ s₃ : finmap β) (H : ∀ (a₁ a₂ a₃ : alist β), C ⟦a₁⟧ ⟦a₂⟧ ⟦a₃⟧) : C s₁ s₂ s₃ :=
induction_on₂ s₁ s₂ $ λ l₁ l₂, induction_on s₃ $ λ l₃, H l₁ l₂ l₃

/-! ### extensionality -/

@[ext] theorem ext : ∀ {s t : finmap β}, s.entries = t.entries → s = t
| ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ H := by congr'

@[simp] theorem ext_iff {s t : finmap β} : s.entries = t.entries ↔ s = t :=
⟨ext, congr_arg _⟩

/-! ### mem -/

/-- The predicate `a ∈ s` means that `s` has a value associated to the key `a`. -/
instance : has_mem α (finmap β) := ⟨λ a s, a ∈ s.entries.keys⟩

theorem mem_def {a : α} {s : finmap β} :
  a ∈ s ↔ a ∈ s.entries.keys := iff.rfl

@[simp] theorem mem_to_finmap {a : α} {s : alist β} :
  a ∈ ⟦s⟧ ↔ a ∈ s := iff.rfl

/-! ### keys -/

/-- The set of keys of a finite map. -/
def keys (s : finmap β) : finset α :=
⟨s.entries.keys, induction_on s keys_nodup⟩

@[simp] theorem keys_val (s : alist β) : (keys ⟦s⟧).val = s.keys := rfl

@[simp] theorem keys_ext {s₁ s₂ : alist β} :
  keys ⟦s₁⟧ = keys ⟦s₂⟧ ↔ s₁.keys ~ s₂.keys :=
by simp [keys, alist.keys]

theorem mem_keys {a : α} {s : finmap β} : a ∈ s.keys ↔ a ∈ s :=
induction_on s $ λ s, alist.mem_keys

/-! ### empty -/

/-- The empty map. -/
instance : has_emptyc (finmap β) := ⟨⟨0, nodupkeys_nil⟩⟩

instance : inhabited (finmap β) := ⟨∅⟩

@[simp] theorem empty_to_finmap : (⟦∅⟧ : finmap β) = ∅ := rfl

@[simp] theorem to_finmap_nil [decidable_eq α] : ([].to_finmap : finmap β) = ∅ := rfl

theorem not_mem_empty {a : α} : a ∉ (∅ : finmap β) :=
multiset.not_mem_zero a

@[simp] theorem keys_empty : (∅ : finmap β).keys = ∅ := rfl

/-! ### singleton -/

/-- The singleton map. -/
def singleton (a : α) (b : β a) : finmap β := ⟦alist.singleton a b⟧

@[simp] theorem keys_singleton (a : α) (b : β a) :
  (singleton a b).keys = {a} := rfl

@[simp] lemma mem_singleton (x y : α) (b : β y) : x ∈ singleton y b ↔ x = y :=
by simp only [singleton]; erw [mem_cons_eq, mem_nil_iff, or_false]

section

variables [decidable_eq α]

instance has_decidable_eq [∀ a, decidable_eq (β a)] : decidable_eq (finmap β)
| s₁ s₂ := decidable_of_iff _ ext_iff

/-! ### lookup -/

/-- Look up the value associated to a key in a map. -/
def lookup (a : α) (s : finmap β) : option (β a) :=
lift_on s (lookup a) (λ s t, perm_lookup)

@[simp] theorem lookup_to_finmap (a : α) (s : alist β) :
  lookup a ⟦s⟧ = s.lookup a := rfl

@[simp] theorem lookup_list_to_finmap (a : α) (s : list (sigma β)) :
  lookup a s.to_finmap = s.lookup a :=
by rw [list.to_finmap, lookup_to_finmap, lookup_to_alist]

@[simp] theorem lookup_empty (a) : lookup a (∅ : finmap β) = none :=
rfl

theorem lookup_is_some {a : α} {s : finmap β} :
  (s.lookup a).is_some ↔ a ∈ s :=
induction_on s $ λ s, alist.lookup_is_some

theorem lookup_eq_none {a} {s : finmap β} : lookup a s = none ↔ a ∉ s :=
induction_on s $ λ s, alist.lookup_eq_none

@[simp] lemma lookup_singleton_eq {a : α} {b : β a} : (singleton a b).lookup a = some b :=
by rw [singleton, lookup_to_finmap, alist.singleton, alist.lookup, lookup_cons_eq]

instance (a : α) (s : finmap β) : decidable (a ∈ s) :=
decidable_of_iff _ lookup_is_some

lemma mem_iff {a : α} {s : finmap β} : a ∈ s ↔ ∃ b, s.lookup a = some b :=
induction_on s $ λ s,
iff.trans list.mem_keys $ exists_congr $ λ b,
(mem_lookup_iff s.nodupkeys).symm

lemma mem_of_lookup_eq_some {a : α} {b : β a} {s : finmap β} (h : s.lookup a = some b) : a ∈ s :=
mem_iff.mpr ⟨_, h⟩

theorem ext_lookup {s₁ s₂ : finmap β} : (∀ x, s₁.lookup x = s₂.lookup x) → s₁ = s₂ :=
induction_on₂ s₁ s₂ $ λ s₁ s₂ h,
begin
  simp only [alist.lookup, lookup_to_finmap] at h,
  rw [alist.to_finmap_eq],
  apply lookup_ext s₁.nodupkeys s₂.nodupkeys,
  intros x y,
  rw h,
end

/-! ### replace -/

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

end

/-! ### foldl -/

/-- Fold a commutative function over the key-value pairs in the map -/
def foldl {δ : Type w} (f : δ → Π a, β a → δ)
  (H : ∀ d a₁ b₁ a₂ b₂, f (f d a₁ b₁) a₂ b₂ = f (f d a₂ b₂) a₁ b₁)
  (d : δ) (m : finmap β) : δ :=
m.entries.foldl (λ d s, f d s.1 s.2) (λ d s t, H _ _ _ _ _) d

/-- `any f s` returns `tt` iff there exists a value `v` in `s` such that `f v = tt`. -/
def any (f : Π x, β x → bool) (s : finmap β) : bool :=
s.foldl (λ x y z, x ∨ f y z) (by { intros,  simp [or.right_comm] }) ff

/-- `all f s` returns `tt` iff `f v = tt` for all values `v` in `s`. -/
def all (f : Π x, β x → bool) (s : finmap β) : bool :=
s.foldl (λ x y z, x ∧ f y z) (by { intros, simp [and.right_comm] }) ff

/-! ### erase -/

section

variables [decidable_eq α]

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

theorem not_mem_erase_self {a : α} {s : finmap β} : ¬ a ∈ erase a s :=
by rw [mem_erase, not_and_distrib, not_not]; left; refl

@[simp] theorem lookup_erase (a) (s : finmap β) : lookup a (erase a s) = none :=
induction_on s $ lookup_erase a

@[simp] theorem lookup_erase_ne {a a'} {s : finmap β} (h : a ≠ a') :
  lookup a (erase a' s) = lookup a s :=
induction_on s $ λ s, lookup_erase_ne h

theorem erase_erase {a a' : α} {s : finmap β} : erase a (erase a' s) = erase a' (erase a s) :=
induction_on s $ λ s, ext (by simp only [erase_erase, erase_to_finmap])

/-! ### sdiff -/

/-- `sdiff s s'` consists of all key-value pairs from `s` and `s'` where the keys are in `s` or
`s'` but not both. -/
def sdiff (s s' : finmap β) : finmap β :=
s'.foldl (λ s x _, s.erase x) (λ a₀ a₁ _ a₂ _, erase_erase) s

instance : has_sdiff (finmap β) := ⟨sdiff⟩

/-! ### insert -/

/-- Insert a key-value pair into a finite map, replacing any existing pair with
  the same key. -/
def insert (a : α) (b : β a) (s : finmap β) : finmap β :=
lift_on s (λ t, ⟦insert a b t⟧) $
λ s₁ s₂ p, to_finmap_eq.2 $ perm_insert p

@[simp] theorem insert_to_finmap (a : α) (b : β a) (s : alist β) :
  insert a b ⟦s⟧ = ⟦s.insert a b⟧ := by simp [insert]

theorem insert_entries_of_neg {a : α} {b : β a} {s : finmap β} : a ∉ s →
  (insert a b s).entries = ⟨a, b⟩ ::ₘ s.entries :=
induction_on s $ λ s h,
by simp [insert_entries_of_neg (mt mem_to_finmap.1 h)]

@[simp] theorem mem_insert {a a' : α} {b' : β a'} {s : finmap β} :
  a ∈ insert a' b' s ↔ a = a' ∨ a ∈ s :=
induction_on s mem_insert

@[simp] theorem lookup_insert {a} {b : β a} (s : finmap β) :
  lookup a (insert a b s) = some b :=
induction_on s $ λ s,
by simp only [insert_to_finmap, lookup_to_finmap, lookup_insert]

@[simp] theorem lookup_insert_of_ne {a a'} {b : β a} (s : finmap β) (h : a' ≠ a) :
  lookup a' (insert a b s) = lookup a' s :=
induction_on s $ λ s,
by simp only [insert_to_finmap, lookup_to_finmap, lookup_insert_ne h]

@[simp] theorem insert_insert {a} {b b' : β a} (s : finmap β) :
  (s.insert a b).insert a b' = s.insert a b' :=
induction_on s $ λ s,
by simp only [insert_to_finmap, insert_insert]

theorem insert_insert_of_ne {a a'} {b : β a} {b' : β a'} (s : finmap β) (h : a ≠ a') :
  (s.insert a b).insert a' b' = (s.insert a' b').insert a b :=
induction_on s $ λ s,
by simp only [insert_to_finmap, alist.to_finmap_eq, insert_insert_of_ne _ h]

theorem to_finmap_cons (a : α) (b : β a) (xs : list (sigma β)) :
  list.to_finmap (⟨a,b⟩ :: xs) = insert a b xs.to_finmap := rfl

theorem mem_list_to_finmap (a : α) (xs : list (sigma β)) :
  a ∈ xs.to_finmap ↔ (∃ b : β a, sigma.mk a b ∈ xs) :=
by { induction xs with x xs; [skip, cases x];
     simp only [to_finmap_cons, *, not_mem_empty, exists_or_distrib, not_mem_nil, to_finmap_nil,
                exists_false, mem_cons_iff, mem_insert, exists_and_distrib_left];
     apply or_congr _ iff.rfl,
     conv { to_lhs, rw ← and_true (a = x_fst) },
     apply and_congr_right, rintro ⟨⟩, simp only [exists_eq, iff_self, heq_iff_eq] }

@[simp] theorem insert_singleton_eq {a : α} {b b' : β a} :
  insert a b (singleton a b') = singleton a b :=
by simp only [singleton, finmap.insert_to_finmap, alist.insert_singleton_eq]

/-! ### extract -/

/-- Erase a key from the map, and return the corresponding value, if found. -/
def extract (a : α) (s : finmap β) : option (β a) × finmap β :=
lift_on s (λ t, prod.map id to_finmap (extract a t)) $
λ s₁ s₂ p, by simp [perm_lookup p, to_finmap_eq, perm_erase p]

@[simp] theorem extract_eq_lookup_erase (a : α) (s : finmap β) :
  extract a s = (lookup a s, erase a s) :=
induction_on s $ λ s, by simp [extract]

/-! ### union -/

/-- `s₁ ∪ s₂` is the key-based union of two finite maps. It is left-biased: if
there exists an `a ∈ s₁`, `lookup a (s₁ ∪ s₂) = lookup a s₁`. -/
def union (s₁ s₂ : finmap β) : finmap β :=
lift_on₂ s₁ s₂ (λ s₁ s₂, ⟦s₁ ∪ s₂⟧) $
λ s₁ s₂ s₃ s₄ p₁₃ p₂₄, to_finmap_eq.mpr $ perm_union p₁₃ p₂₄

instance : has_union (finmap β) := ⟨union⟩

@[simp] theorem mem_union {a} {s₁ s₂ : finmap β} :
  a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ :=
induction_on₂ s₁ s₂ $ λ _ _, mem_union

@[simp] theorem union_to_finmap (s₁ s₂ : alist β) : ⟦s₁⟧ ∪ ⟦s₂⟧ = ⟦s₁ ∪ s₂⟧ :=
by simp [(∪), union]

theorem keys_union {s₁ s₂ : finmap β} : (s₁ ∪ s₂).keys = s₁.keys ∪ s₂.keys :=
induction_on₂ s₁ s₂ $ λ s₁ s₂, finset.ext $ by simp [keys]

@[simp] theorem lookup_union_left {a} {s₁ s₂ : finmap β} :
  a ∈ s₁ → lookup a (s₁ ∪ s₂) = lookup a s₁ :=
induction_on₂ s₁ s₂ $ λ s₁ s₂, lookup_union_left

@[simp] theorem lookup_union_right {a} {s₁ s₂ : finmap β} :
  a ∉ s₁ → lookup a (s₁ ∪ s₂) = lookup a s₂ :=
induction_on₂ s₁ s₂ $ λ s₁ s₂, lookup_union_right

theorem lookup_union_left_of_not_in {a} {s₁ s₂ : finmap β} (h : a ∉ s₂) :
  lookup a (s₁ ∪ s₂) = lookup a s₁ :=
begin
  by_cases h' : a ∈ s₁,
  { rw lookup_union_left h' },
  { rw [lookup_union_right h', lookup_eq_none.mpr h, lookup_eq_none.mpr h'] }
end

@[simp] theorem mem_lookup_union {a} {b : β a} {s₁ s₂ : finmap β} :
  b ∈ lookup a (s₁ ∪ s₂) ↔ b ∈ lookup a s₁ ∨ a ∉ s₁ ∧ b ∈ lookup a s₂ :=
induction_on₂ s₁ s₂ $ λ s₁ s₂, mem_lookup_union

theorem mem_lookup_union_middle {a} {b : β a} {s₁ s₂ s₃ : finmap β} :
  b ∈ lookup a (s₁ ∪ s₃) → a ∉ s₂ → b ∈ lookup a (s₁ ∪ s₂ ∪ s₃) :=
induction_on₃ s₁ s₂ s₃ $ λ s₁ s₂ s₃, mem_lookup_union_middle

theorem insert_union {a} {b : β a} {s₁ s₂ : finmap β} :
  insert a b (s₁ ∪ s₂) = insert a b s₁ ∪ s₂ :=
induction_on₂ s₁ s₂ $ λ a₁ a₂, by simp [insert_union]

theorem union_assoc {s₁ s₂ s₃ : finmap β} : (s₁ ∪ s₂) ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) :=
induction_on₃ s₁ s₂ s₃ $ λ s₁ s₂ s₃,
by simp only [alist.to_finmap_eq, union_to_finmap, alist.union_assoc]

@[simp] theorem empty_union {s₁ : finmap β} : ∅ ∪ s₁ = s₁ :=
induction_on s₁ $ λ s₁, by rw ← empty_to_finmap;
  simp [- empty_to_finmap, alist.to_finmap_eq, union_to_finmap, alist.union_assoc]

@[simp] theorem union_empty {s₁ : finmap β} : s₁ ∪ ∅ = s₁ :=
induction_on s₁ $ λ s₁, by rw ← empty_to_finmap;
  simp [- empty_to_finmap, alist.to_finmap_eq, union_to_finmap, alist.union_assoc]

theorem erase_union_singleton (a : α) (b : β a) (s : finmap β) (h : s.lookup a = some b) :
  s.erase a ∪ singleton a b = s :=
ext_lookup
(λ x, by { by_cases h' : x = a,
      { subst a, rw [lookup_union_right not_mem_erase_self, lookup_singleton_eq, h], },
      { have : x ∉ singleton a b, { rwa mem_singleton },
        rw [lookup_union_left_of_not_in this, lookup_erase_ne h'] } } )

end

/-! ### disjoint -/

/-- `disjoint s₁ s₂` holds if `s₁` and `s₂` have no keys in common. -/
def disjoint (s₁ s₂ : finmap β) : Prop :=
∀ x ∈ s₁, ¬ x ∈ s₂

lemma disjoint_empty (x : finmap β) : disjoint ∅ x .

@[symm]
lemma disjoint.symm (x y : finmap β) (h : disjoint x y) : disjoint y x :=
λ p hy hx, h p hx hy

lemma disjoint.symm_iff (x y : finmap β) : disjoint x y ↔ disjoint y x :=
⟨disjoint.symm x y, disjoint.symm y x⟩

section

variables [decidable_eq α]

instance : decidable_rel (@disjoint α β) :=
λ x y, by dsimp only [disjoint]; apply_instance

lemma disjoint_union_left (x y z : finmap β) : disjoint (x ∪ y) z ↔ disjoint x z ∧ disjoint y z :=
by simp [disjoint, finmap.mem_union, or_imp_distrib, forall_and_distrib]

lemma disjoint_union_right (x y z : finmap β) : disjoint x (y ∪ z) ↔ disjoint x y ∧ disjoint x z :=
by rw [disjoint.symm_iff, disjoint_union_left, disjoint.symm_iff _ x, disjoint.symm_iff _ x]

theorem union_comm_of_disjoint {s₁ s₂ : finmap β} : disjoint s₁ s₂ → s₁ ∪ s₂ = s₂ ∪ s₁ :=
induction_on₂ s₁ s₂ $ λ s₁ s₂,
by { intros h, simp only [alist.to_finmap_eq, union_to_finmap, alist.union_comm_of_disjoint h] }

theorem union_cancel {s₁ s₂ s₃ : finmap β} (h : disjoint s₁ s₃) (h' : disjoint s₂ s₃) :
  s₁ ∪ s₃ = s₂ ∪ s₃ ↔ s₁ = s₂ :=
⟨λ h'', begin
          apply ext_lookup, intro x,
          have : (s₁ ∪ s₃).lookup x = (s₂ ∪ s₃).lookup x, from h'' ▸ rfl,
          by_cases hs₁ : x ∈ s₁,
          { rwa [lookup_union_left hs₁, lookup_union_left_of_not_in (h _ hs₁)] at this, },
          { by_cases hs₂ : x ∈ s₂,
            { rwa [lookup_union_left_of_not_in (h' _ hs₂), lookup_union_left hs₂] at this, },
            { rw [lookup_eq_none.mpr hs₁, lookup_eq_none.mpr hs₂] } }
        end,
 λ h, h ▸ rfl⟩

end

end finmap
