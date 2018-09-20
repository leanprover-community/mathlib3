import data.list.sigma

universes u v w
open list

structure alist (α : Type u) (β : α → Type v) : Type (max u v) :=
(val : list (sigma β))
(nd : val.knodup)

namespace alist
variables {α : Type u} {β : α → Type v}

@[extensionality] theorem ext : ∀ {s t : alist α β}, s.val = t.val → s = t
| ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ H := by congr'

instance : has_mem α (alist α β) := ⟨λ a s, ∃ b : β a, sigma.mk a b ∈ s.val⟩

theorem mem_def {a : α} {s : alist α β} :
  a ∈ s ↔ ∃ b : β a, sigma.mk a b ∈ s.val := iff.rfl

theorem mem_of_perm {a : α} {s₁ s₂ : alist α β} (p : s₁.val ~ s₂.val) : a ∈ s₁ ↔ a ∈ s₂ :=
exists_congr $ λ b, mem_of_perm p

def keys (s : alist α β) : list α := s.val.map sigma.fst

theorem mem_keys {a : α} {s : alist α β} : a ∈ s.keys ↔ a ∈ s :=
by rw [keys, mem_map]; exact
⟨λ ⟨⟨_, b⟩, h, rfl⟩, ⟨b, h⟩, λ ⟨b, h⟩, ⟨_, h, rfl⟩⟩

theorem keys_nodup (s : alist α β) : s.keys.nodup := s.nd

instance : has_emptyc (alist α β) := ⟨⟨[], knodup_nil⟩⟩

theorem not_mem_empty_val {s : sigma β} : s ∉ (∅ : alist α β).val :=
not_mem_nil _

theorem not_mem_empty {a : α} : a ∉ (∅ : alist α β) :=
λ ⟨b, h⟩, not_mem_empty_val h

@[simp] theorem keys_empty : (∅ : alist α β).keys = [] := rfl

def singleton (a : α) (b : β a) : alist α β :=
⟨[⟨a, b⟩], knodup_singleton _⟩

@[simp] theorem keys_singleton (a : α) (b : β a) : (singleton a b).keys = [a] := rfl

variables [decidable_eq α]

def lookup (a : α) (s : alist α β) : option (β a) :=
s.val.lookup a

theorem lookup_is_some {a : α} {s : alist α β} :
  (s.lookup a).is_some ↔ a ∈ s := lookup_is_some

theorem perm_lookup {a : α} {s₁ s₂ : alist α β} (p : s₁.val ~ s₂.val) :
  s₁.lookup a = s₂.lookup a :=
perm_lookup _ s₁.nd s₂.nd p

instance (a : α) (s : alist α β) : decidable (a ∈ s) :=
decidable_of_iff _ lookup_is_some

def insert (a : α) (b : β a) (s : alist α β) : alist α β :=
if h : a ∈ s then s else ⟨⟨a, b⟩ :: s.val,
  nodup_cons.2 ⟨mt mem_keys.1 h, s.nd⟩⟩

@[simp] theorem insert_of_pos {a : α} {b : β a} {s : alist α β} (h : a ∈ s) :
  insert a b s = s := dif_pos h

theorem insert_val_of_neg {a : α} {b : β a} {s : alist α β} (h : a ∉ s) :
  (insert a b s).val = ⟨a, b⟩ :: s.val := by simp [insert, h]

@[simp] theorem keys_insert (a : α) (b : β a) (s : alist α β) :
  (insert a b s).keys = _root_.insert a s.keys :=
begin
  by_cases a ∈ s,
  { simp [h, mem_keys.2 h] },
  { simp [keys, insert_val_of_neg h],
    exact (insert_of_not_mem (mt mem_keys.1 h)).symm }
end

@[simp] theorem mem_insert {a a' : α} {b : β a} {s : alist α β} :
  a' ∈ insert a b s ↔ a' = a ∨ a' ∈ s :=
by rw [← mem_keys, ← mem_keys]; simp

theorem perm_insert {a : α} {b : β a} {s₁ s₂ : alist α β}
  (p : s₁.val ~ s₂.val) : (insert a b s₁).val ~ (insert a b s₂).val :=
begin
  by_cases a ∈ s₁,
  { simp [h, (mem_of_perm p).1 h, p] },
  { simp [insert_val_of_neg h, insert_val_of_neg (mt (mem_of_perm p).2 h)],
    exact p.skip _ }
end

def replace (a : α) (b : β a) (s : alist α β) : alist α β :=
⟨kreplace a b s.val, (kreplace_knodup a b).2 s.nd⟩

@[simp] theorem keys_replace (a : α) (b : β a) (s : alist α β) :
  (replace a b s).keys = s.keys :=
kreplace_map_fst _ _ _

@[simp] theorem mem_replace {a a' : α} {b : β a} {s : alist α β} :
  a' ∈ replace a b s ↔ a' ∈ s :=
by rw [← mem_keys, keys_replace, mem_keys]

theorem perm_replace {a : α} {b : β a} {s₁ s₂ : alist α β} :
  s₁.val ~ s₂.val → (replace a b s₁).val ~ (replace a b s₂).val :=
perm_kreplace s₁.nd

/-- Fold a function over the key-value pairs in the map -/
def foldl {δ : Type w} (f : δ → Π a, β a → δ) (d : δ) (m : alist α β) : δ :=
m.val.foldl (λ r a, f r a.1 a.2) d

def erase (a : α) (s : alist α β) : alist α β :=
⟨kerase a s.val, kerase_knodup _ s.nd⟩

@[simp] theorem keys_erase (a : α) (s : alist α β) :
  (erase a s).keys = s.keys.erase a :=
by rw [erase_eq_erasep, keys, keys, erasep_map]; refl

@[simp] theorem mem_erase {a a' : α} {s : alist α β} : a' ∈ erase a s ↔ a' ≠ a ∧ a' ∈ s :=
by rw [← mem_keys, keys_erase, mem_erase_iff_of_nodup s.keys_nodup, mem_keys]

theorem perm_erase {a : α} {s₁ s₂ : alist α β} :
  s₁.val ~ s₂.val → (erase a s₁).val ~ (erase a s₂).val :=
perm_kerase s₁.nd

def extract (a : α) (s : alist α β) : option (β a) × alist α β :=
have (kextract a s.val).2.knodup,
by rw [kextract_eq_lookup_kerase]; exact kerase_knodup _ s.nd,
match kextract a s.val, this with
| (b, l), h := (b, ⟨l, h⟩)
end

@[simp] theorem extract_eq_lookup_erase (a : α) (s : alist α β) :
  extract a s = (lookup a s, erase a s) :=
by simp [extract]; split; refl

end alist
