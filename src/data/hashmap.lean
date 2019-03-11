/-
Copyright (c) 2019 Sean Leather. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Leather

Hash maps
-/
import data.array.lemmas data.list.alist data.pnat

universes u v

/-- Lift `f : α → ℕ` to `α → fin n` using the result modulo `n : ℕ+` -/
def fin.lift_mod_pnat (n : ℕ+) {α} (f : α → ℕ) (a : α) : fin n :=
⟨f a % n, nat.mod_lt _ n.property⟩

variables {n : ℕ} {α : Type u} {β : α → Type v}

/-- A hash map is valid if every bucket has no duplicate keys and every key
  hash equals the array index of the key's bucket. -/
def hashmap.is_valid (bs : array n (list (sigma β))) (h : α → fin n) : Prop :=
∀ (i : fin n), (bs.read i).nodupkeys ∧ ∀ a ∈ (bs.read i).keys, i = h a

/-- A hash map is a finite key-value map implemented with an n-sized array of
  buckets, a hash function, and a proof of validity. -/
structure hashmap (n : ℕ) {α : Type u} (β : α → Type v) :=
/- Array of buckets -/
(buckets : array n (list (sigma β)))
/- Hash function from key to bucket index -/
(hash : α → fin n)
/- Validity proof -/
(valid : hashmap.is_valid buckets hash)

/- Notes on alternative structures for a hashmap:

Bundling `n`:

```
structure hashmap {α : Type u} (β : α → Type v) :=
(n : ℕ)
(buckets : array n (list (sigma β)))
-- ...
```

Having `n` be a field instead of a parameter means that the size of the
underlying array would be hidden in the type of a hash map. At first blush,
this appears attractive because, from a usage perspective, it doesn't matter
what size the array is. However, the size is integral to the type of a hash
map, useful when equating two hashmaps (see `ext`), and necessary when indexing
into the `buckets`. So, rather than have use type such as `fin m.n`, we expose
`n`.

Using `alist`:

```
structure hashmap (n : ℕ) {α : Type u} (β : α → Type v) :=
(buckets : array n (alist β))
(hash : α → fin n)
(valid : ∀ (i : fin n), ∀ a ∈ (buckets.read i).keys, i = hash a)
```

Using `alist` instead of `list` in the `buckets` would allow us to reduce the
`valid` theorem as shown above. However, we cannot `map` an `array` to a
different element type (i.e. in `map f`, `f : α → α` and not `f : α → β`), and
that makes proofs significantly more difficult.

-/

namespace hashmap
open list

/- nth -/

/-- The list at the given bucket index -/
def nth (m : hashmap n β) : fin n → list (sigma β) :=
m.buckets.read

theorem nth_nodupkeys (m : hashmap n β) (i : fin n) : (m.nth i).nodupkeys :=
(m.valid i).left

theorem index_eq_hash {a} {i : fin n} {m : hashmap n β} (h : a ∈ (m.nth i).keys) :
  i = m.hash a :=
(m.valid i).right a h

/- bucket -/

/-- The bucket for the given key -/
def bucket (m : hashmap n β) (a : α) : list (sigma β) :=
m.nth (m.hash a)

section bucket
variables {s : sigma β} {m : hashmap n β}

theorem mem_bucket_nth : s ∈ m.bucket s.1 ↔ ∃ (i : fin n), s ∈ m.nth i :=
⟨λ h, ⟨m.hash s.1, h⟩,
 λ ⟨i, h⟩, by simpa only [index_eq_hash (mem_keys_of_mem h)] using h⟩

theorem mem_bucket_list : s ∈ m.bucket s.1 ↔ ∃ (l : list (sigma β)), l ∈ m.buckets ∧ s ∈ l :=
⟨λ h, ⟨m.bucket s.1, ⟨m.hash s.1, rfl⟩, h⟩,
 λ ⟨l, h₁, h₂⟩, by cases h₁ with i h₁; induction h₁; exact mem_bucket_nth.mpr ⟨_, h₂⟩⟩

end bucket /- section -/

/- constructing empty hashmaps -/

/-- Construct an empty hash map with a `fin n`-valued hash function -/
def mk_empty (β : α → Type v) (f : α → fin n) : hashmap n β :=
⟨mk_array n [], f, λ _, ⟨nodupkeys_nil, λ _ h, by cases h⟩⟩

/-- Construct an empty hashmap with size `n > 0` and a `nat`-valued hash function -/
def mk_empty_pos (n : ℕ+) {α} (β : α → Type v) (f : α → ℕ) : hashmap n β :=
mk_empty β (fin.lift_mod_pnat n f)

/- extensionality -/

section ext
variables {m₁ m₂ : hashmap n β}

theorem ext_core : m₁.buckets = m₂.buckets → m₁.hash = m₂.hash → m₁ = m₂ :=
by cases m₁; cases m₂; intros; congr; repeat { assumption }

@[extensionality] theorem ext
  (hr : ∀ (i : fin n), m₁.nth i = m₂.nth i)
  (hh : ∀ a, m₁.hash a = m₂.hash a) :
  m₁ = m₂ :=
ext_core (array.ext hr) (funext hh)

end ext /- section -/

/- mem -/

/-- The predicate `a ∈ m` means that `m` has a value associated to the key `a`. -/
instance : has_mem α (hashmap n β) :=
⟨λ a m, a ∈ (m.bucket a).keys⟩

section mem
variables {a : α} {m : hashmap n β}

theorem mem_bucket_keys : a ∈ m ↔ a ∈ (m.bucket a).keys :=
iff.rfl

theorem mem_bucket : a ∈ m ↔ ∃ (b : β a), sigma.mk a b ∈ m.bucket a :=
mem_bucket_keys.trans $ by simp [keys]

theorem mem_nth_keys : a ∈ m ↔ ∃ (i : fin n), a ∈ (m.nth i).keys :=
⟨λ h, ⟨m.hash a, h⟩, λ ⟨i, h⟩, by simpa only [index_eq_hash h] using h⟩

end mem /- section -/

/- is_empty -/

/-- A hash map is empty if every bucket is empty -/
def is_empty (m : hashmap n β) : Prop :=
∀ i : fin n, m.nth i = []

theorem is_empty_mk_empty (β) (f : α → fin n) : (mk_empty β f).is_empty :=
λ _, rfl

theorem is_empty_mk_empty_pos (n : ℕ+) (β) (f : α → ℕ) : (mk_empty_pos n β f).is_empty :=
λ _, rfl

@[simp] theorem is_empty_zero (m : hashmap 0 β) : m.is_empty :=
λ i, fin_zero_elim i

theorem mem_is_empty {m : hashmap n β} : m.is_empty ↔ ∀ a, a ∉ m :=
iff.intro
  (λ h₁ a h₂, by simpa [mem_bucket_keys, bucket, h₁ (m.hash a)] using h₂)
  (λ h₁ _, eq_nil_iff_forall_not_mem.mpr $ λ _ h₂, h₁ _ $
   mem_nth_keys.mpr ⟨_, mem_keys_of_mem h₂⟩)

/-- The bucket list of a hashmap -/
def to_lists (m : hashmap n β) : list (list (sigma β)) :=
m.buckets.to_list

section to_lists
variables {i : ℕ} {m : hashmap n β} {l : list (sigma β)}

@[simp] theorem mem_to_lists : l ∈ m.to_lists ↔ l ∈ m.buckets :=
array.mem_to_list

theorem index_eq_hash_of_to_lists (he : (i, l) ∈ m.to_lists.enum) {a} (hl : a ∈ l.keys) :
  i = (m.hash a).1 :=
have h₁ : ∃ p, m.nth ⟨i, p⟩ = l := array.mem_to_list_enum.1 he,
have h₂ : ∃ p, fin.mk i p = m.hash a := h₁.imp (λ p h, index_eq_hash (h.symm ▸ hl)),
let ⟨_, h⟩ := h₂ in by rw ←h

theorem nodupkeys_to_lists (h : l ∈ m.to_lists) : l.nodupkeys :=
by simp [to_lists] at h; cases h with i h; induction h; exact m.nth_nodupkeys i

theorem disjoint_keys_to_lists :
  pairwise (λ l₁ l₂ : list (sigma β), disjoint l₁.keys l₂.keys) m.to_lists :=
begin
  rw [←enum_map_snd m.to_lists, pairwise_map],
  refine pairwise.imp_of_mem _ ((pairwise_map prod.fst).mp (nodup_enum_map_fst m.to_lists)),
  rw prod.forall,
  intros n₁ s₁,
  rw prod.forall,
  intros n₂ s₂ hme₁ hme₂ n₁_ne_n₂ a hm₁ hm₂,
  apply n₁_ne_n₂,
  rw index_eq_hash_of_to_lists hme₁ hm₁,
  rw index_eq_hash_of_to_lists hme₂ hm₂
end

end to_lists /- section -/

/- to_alist -/

/-- The association list of a hash map -/
def to_alist (m : hashmap n β) : alist β :=
⟨m.to_lists.join, nodupkeys_join.mpr ⟨λ _, nodupkeys_to_lists, disjoint_keys_to_lists⟩⟩

section to_alist
variables {a : α} {b : β a} {m m₁ m₂ : hashmap n β}

theorem is_empty_to_alist : m.is_empty ↔ m.to_alist = ∅ :=
by simp only [is_empty, nth, to_alist, to_lists, has_emptyc.emptyc, array.to_list_join_nil]

theorem mem_bucket_to_alist : sigma.mk a b ∈ m.bucket a ↔ sigma.mk a b ∈ m.to_alist.entries :=
by simp [to_alist, mem_bucket_list]

theorem mem_to_alist : a ∈ m ↔ a ∈ m.to_alist :=
calc a ∈ m ↔ ∃ (b : β a), sigma.mk a b ∈ m.bucket a  : mem_bucket
... ↔ ∃ (b : β a), sigma.mk a b ∈ m.to_alist.entries : exists_congr $ λ _, mem_bucket_to_alist
... ↔ a ∈ m.to_alist                                 : alist.mem_entries.symm

theorem to_alist_ext (h : a ∈ m₁.to_alist ↔ a ∈ m₂.to_alist) : a ∈ m₁ ↔ a ∈ m₂ :=
by simp only [mem_to_alist, h]

end to_alist /- section -/

/- keys -/

/-- The list of keys of a hash map. -/
def keys (m : hashmap n β) : list α :=
m.to_alist.keys

theorem keys_nodup (m : hashmap n β) : m.keys.nodup :=
m.to_alist.keys_nodup

section decidable_eq_α
variables [decidable_eq α]

/- lookup -/

/-- Look up a key in a hash map to find the value, if it exists -/
def lookup (a : α) (m : hashmap n β) : option (β a) :=
lookup a $ m.bucket a

section lookup
variables {a : α} {b : β a} {m : hashmap n β}

theorem lookup_is_some : (m.lookup a).is_some ↔ a ∈ m :=
lookup_is_some

theorem lookup_eq_none : m.lookup a = none ↔ a ∉ m :=
lookup_eq_none

theorem mem_lookup_iff : b ∈ m.lookup a ↔ sigma.mk a b ∈ m.bucket a :=
mem_lookup_iff (nth_nodupkeys _ _)

theorem perm_lookup {m₁ m₂ : hashmap n β} :
  m₁.bucket a ~ m₂.bucket a → m₁.lookup a = m₂.lookup a :=
perm_lookup a (nth_nodupkeys _ _) (nth_nodupkeys _ _)

theorem lookup_to_alist : m.lookup a = m.to_alist.lookup a :=
begin
  by_cases h : a ∈ m,
  { cases exists_of_mem_keys h with b h,
    have h₁ : m.lookup a = some b := mem_lookup_iff.mpr h,
    have h₂ : m.to_alist.lookup a = some b :=
      alist.mem_lookup_iff.mpr (mem_bucket_to_alist.mp h),
    rwa ←h₂ at h₁},
  { rw lookup_eq_none.mpr h,
    rw alist.lookup_eq_none.mpr ((not_iff_not_of_iff mem_to_alist).mp h) }
end

theorem is_empty_lookup : m.is_empty ↔ ∀ a, m.lookup a = none :=
mem_is_empty.trans $ by simp only [lookup_eq_none.symm]

end lookup /- section -/

end decidable_eq_α /- section -/

end hashmap
