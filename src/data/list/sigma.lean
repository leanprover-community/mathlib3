/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sean Leather

Functions on lists of sigma types.
-/
import data.list.perm

universes u v

namespace list
variables {α : Type u} {β : α → Type v}

/- keys -/

/-- List of keys from a list of key-value pairs -/
def keys : list (sigma β) → list α :=
map sigma.fst

@[simp] theorem keys_nil : @keys α β [] = [] :=
rfl

@[simp] theorem keys_cons {s} {l : list (sigma β)} : (s :: l).keys = s.1 :: l.keys :=
rfl

theorem mem_keys_of_mem {s : sigma β} {l : list (sigma β)} : s ∈ l → s.1 ∈ l.keys :=
mem_map_of_mem sigma.fst

theorem exists_of_mem_keys {a} {l : list (sigma β)} (h : a ∈ l.keys) :
  ∃ (b : β a), sigma.mk a b ∈ l :=
let ⟨⟨a', b'⟩, m, e⟩ := exists_of_mem_map h in
eq.rec_on e (exists.intro b' m)

theorem mem_keys {a} {l : list (sigma β)} : a ∈ l.keys ↔ ∃ (b : β a), sigma.mk a b ∈ l :=
⟨exists_of_mem_keys, λ ⟨b, h⟩, mem_keys_of_mem h⟩

theorem not_mem_keys {a} {l : list (sigma β)} : a ∉ l.keys ↔ ∀ b : β a, sigma.mk a b ∉ l :=
(not_iff_not_of_iff mem_keys).trans not_exists

theorem not_eq_key {a} {l : list (sigma β)} : a ∉ l.keys ↔ ∀ s : sigma β, s ∈ l → a ≠ s.1 :=
iff.intro
  (λ h₁ s h₂ e, absurd (mem_keys_of_mem h₂) (by rwa e at h₁))
  (λ f h₁, let ⟨b, h₂⟩ := exists_of_mem_keys h₁ in f _ h₂ rfl)

/- nodupkeys -/

def nodupkeys (l : list (sigma β)) : Prop :=
l.keys.nodup

theorem nodupkeys_iff_pairwise {l} : nodupkeys l ↔
  pairwise (λ s s' : sigma β, s.1 ≠ s'.1) l := pairwise_map _

@[simp] theorem nodupkeys_nil : @nodupkeys α β [] := pairwise.nil

@[simp] theorem nodupkeys_cons {s : sigma β} {l : list (sigma β)} :
  nodupkeys (s::l) ↔ s.1 ∉ l.keys ∧ nodupkeys l :=
by simp [keys, nodupkeys]

theorem nodupkeys.eq_of_fst_eq {l : list (sigma β)}
  (nd : nodupkeys l) {s s' : sigma β} (h : s ∈ l) (h' : s' ∈ l) :
  s.1 = s'.1 → s = s' :=
@forall_of_forall_of_pairwise _
  (λ s s' : sigma β, s.1 = s'.1 → s = s')
  (λ s s' H h, (H h.symm).symm) _ (λ x h _, rfl)
  ((nodupkeys_iff_pairwise.1 nd).imp (λ s s' h h', (h h').elim)) _ h _ h'

theorem nodupkeys.eq_of_mk_mem {a : α} {b b' : β a} {l : list (sigma β)}
  (nd : nodupkeys l) (h : sigma.mk a b ∈ l) (h' : sigma.mk a b' ∈ l) : b = b' :=
by cases nd.eq_of_fst_eq h h' rfl; refl

theorem nodupkeys_singleton (s : sigma β) : nodupkeys [s] := nodup_singleton _

theorem nodupkeys_of_sublist {l₁ l₂ : list (sigma β)} (h : l₁ <+ l₂) : nodupkeys l₂ → nodupkeys l₁ :=
nodup_of_sublist (map_sublist_map _ h)

theorem nodup_of_nodupkeys {l : list (sigma β)} : nodupkeys l → nodup l :=
nodup_of_nodup_map _

theorem perm_nodupkeys {l₁ l₂ : list (sigma β)} (h : l₁ ~ l₂) : nodupkeys l₁ ↔ nodupkeys l₂ :=
perm_nodup $ perm_map _ h

theorem nodupkeys_join {L : list (list (sigma β))} :
  nodupkeys (join L) ↔ (∀ l ∈ L, nodupkeys l) ∧ pairwise disjoint (L.map keys) :=
begin
  rw [nodupkeys_iff_pairwise, pairwise_join, pairwise_map],
  refine and_congr (ball_congr $ λ l h, by simp [nodupkeys_iff_pairwise]) _,
  apply iff_of_eq, congr', ext l₁ l₂,
  simp [keys, disjoint_iff_ne]
end

theorem nodup_enum_map_fst (l : list α) : (l.enum.map prod.fst).nodup :=
by simp [list.nodup_range]

variables [decidable_eq α]

/- lookup -/

/-- `lookup a l` is the first value in `l` corresponding to the key `a`,
  or `none` if no such element exists. -/
def lookup (a : α) : list (sigma β) → option (β a)
| []             := none
| (⟨a', b⟩ :: l) := if h : a' = a then some (eq.rec_on h b) else lookup l

@[simp] theorem lookup_nil (a : α) : lookup a [] = @none (β a) := rfl

@[simp] theorem lookup_cons_eq (l) (a : α) (b : β a) : lookup a (⟨a, b⟩::l) = some b :=
dif_pos rfl

@[simp] theorem lookup_cons_ne (l) {a} :
  ∀ s : sigma β, a ≠ s.1 → lookup a (s::l) = lookup a l
| ⟨a', b⟩ h := dif_neg h.symm

theorem lookup_is_some {a : α} : ∀ {l : list (sigma β)},
  (lookup a l).is_some ↔ a ∈ l.keys
| []             := by simp
| (⟨a', b⟩ :: l) := begin
  by_cases h : a = a',
  { subst a', simp },
  { simp [h, lookup_is_some] },
end

theorem lookup_eq_none {a : α} {l : list (sigma β)} :
  lookup a l = none ↔ a ∉ l.keys :=
begin
  have := not_congr (@lookup_is_some _ _ _ a l),
  simp at this, refine iff.trans _ this,
  cases lookup a l; exact dec_trivial
end

theorem of_mem_lookup
  {a : α} {b : β a} : ∀ {l : list (sigma β)}, b ∈ lookup a l → sigma.mk a b ∈ l
| (⟨a', b'⟩ :: l) H := begin
  by_cases h : a = a',
  { subst a', simp at H, simp [H] },
  { simp [h] at H, exact or.inr (of_mem_lookup H) }
end

theorem mem_lookup {a} {b : β a} {l : list (sigma β)} (nd : l.nodupkeys)
  (h : sigma.mk a b ∈ l) : b ∈ lookup a l :=
begin
  cases option.is_some_iff_exists.mp (lookup_is_some.mpr (mem_keys_of_mem h)) with b' h',
  cases nd.eq_of_mk_mem h (of_mem_lookup h'),
  exact h'
end

theorem map_lookup_eq_find (a : α) : ∀ l : list (sigma β),
  (lookup a l).map (sigma.mk a) = find (λ s, a = s.1) l
| [] := rfl
| (⟨a', b'⟩ :: l) := begin
  by_cases h : a = a',
  { subst a', simp },
  { simp [h, map_lookup_eq_find] }
end

theorem mem_lookup_iff {a : α} {b : β a} {l : list (sigma β)} (nd : l.nodupkeys) :
  b ∈ lookup a l ↔ sigma.mk a b ∈ l :=
⟨of_mem_lookup, mem_lookup nd⟩

theorem perm_lookup (a : α) {l₁ l₂ : list (sigma β)}
  (nd₁ : l₁.nodupkeys) (nd₂ : l₂.nodupkeys) (p : l₁ ~ l₂) : lookup a l₁ = lookup a l₂ :=
by ext b; simp [mem_lookup_iff, nd₁, nd₂]; exact mem_of_perm p

/- lookup_all -/

/-- `lookup_all a l` is the list of all values in `l` corresponding to the key `a`. -/
def lookup_all (a : α) : list (sigma β) → list (β a)
| []             := []
| (⟨a', b⟩ :: l) := if h : a' = a then eq.rec_on h b :: lookup_all l else lookup_all l

@[simp] theorem lookup_all_nil (a : α) : lookup_all a [] = @nil (β a) := rfl

@[simp] theorem lookup_all_cons_eq (l) (a : α) (b : β a) :
  lookup_all a (⟨a, b⟩::l) = b :: lookup_all a l :=
dif_pos rfl

@[simp] theorem lookup_all_cons_ne (l) {a} :
  ∀ s : sigma β, a ≠ s.1 → lookup_all a (s::l) = lookup_all a l
| ⟨a', b⟩ h := dif_neg h.symm

theorem lookup_all_eq_nil {a : α} : ∀ {l : list (sigma β)},
  lookup_all a l = [] ↔ ∀ b : β a, sigma.mk a b ∉ l
| []             := by simp
| (⟨a', b⟩ :: l) := begin
  by_cases h : a = a',
  { subst a', simp, exact λ H, H b (or.inl rfl) },
  { simp [h, lookup_all_eq_nil] },
end

theorem head_lookup_all (a : α) : ∀ l : list (sigma β),
  head' (lookup_all a l) = lookup a l
| []             := by simp
| (⟨a', b⟩ :: l) := by by_cases h : a = a'; [{subst h, simp}, simp *]

theorem mem_lookup_all {a : α} {b : β a} :
  ∀ {l : list (sigma β)}, b ∈ lookup_all a l ↔ sigma.mk a b ∈ l
| []              := by simp
| (⟨a', b'⟩ :: l) := by by_cases h : a = a'; [{subst h, simp *}, simp *]

theorem lookup_all_sublist (a : α) :
  ∀ l : list (sigma β), (lookup_all a l).map (sigma.mk a) <+ l
| []              := by simp
| (⟨a', b'⟩ :: l) := begin
    by_cases h : a = a',
    { subst h, simp, exact (lookup_all_sublist l).cons2 _ _ _ },
    { simp [h], exact (lookup_all_sublist l).cons _ _ _ }
  end

theorem lookup_all_length_le_one (a : α) {l : list (sigma β)} (h : l.nodupkeys) :
  length (lookup_all a l) ≤ 1 :=
by have := nodup_of_sublist (map_sublist_map _ $ lookup_all_sublist a l) h;
   rw map_map at this; rwa [← nodup_repeat, ← map_const _ a]

theorem lookup_all_eq_lookup (a : α) {l : list (sigma β)} (h : l.nodupkeys) :
  lookup_all a l = (lookup a l).to_list :=
begin
  rw ← head_lookup_all,
  have := lookup_all_length_le_one a h, revert this,
  rcases lookup_all a l with _|⟨b, _|⟨c, l⟩⟩; intro; try {refl},
  exact absurd this dec_trivial
end

theorem lookup_all_nodup (a : α) {l : list (sigma β)} (h : l.nodupkeys) :
  (lookup_all a l).nodup :=
by rw lookup_all_eq_lookup a h; apply option.to_list_nodup

theorem perm_lookup_all (a : α) {l₁ l₂ : list (sigma β)}
  (nd₁ : l₁.nodupkeys) (nd₂ : l₂.nodupkeys) (p : l₁ ~ l₂) : lookup_all a l₁ = lookup_all a l₂ :=
by simp [lookup_all_eq_lookup, nd₁, nd₂, perm_lookup a nd₁ nd₂ p]

/- kreplace -/

def kreplace (a : α) (b : β a) : list (sigma β) → list (sigma β) :=
lookmap $ λ s, if h : a = s.1 then some ⟨a, b⟩ else none

theorem kreplace_of_forall_not (a : α) (b : β a) {l : list (sigma β)}
  (H : ∀ b : β a, sigma.mk a b ∉ l) : kreplace a b l = l :=
lookmap_of_forall_not _ $ begin
  rintro ⟨a', b'⟩ h, dsimp, split_ifs,
  { subst a', exact H _ h }, {refl}
end

theorem kreplace_self {a : α} {b : β a} {l : list (sigma β)}
  (nd : nodupkeys l) (h : sigma.mk a b ∈ l) : kreplace a b l = l :=
begin
  refine (lookmap_congr _).trans
    (lookmap_id' (option.guard (λ s, a = s.1)) _ _),
  { rintro ⟨a', b'⟩ h', dsimp [option.guard], split_ifs,
    { subst a', exact ⟨rfl, heq_of_eq $ nd.eq_of_mk_mem h h'⟩ },
    { refl } },
  { rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩, dsimp [option.guard], split_ifs,
    { subst a₁, rintro ⟨⟩, simp }, { rintro ⟨⟩ } },
end

theorem keys_kreplace (a : α) (b : β a) : ∀ l : list (sigma β),
  (kreplace a b l).keys = l.keys :=
lookmap_map_eq _ _ $ by rintro ⟨a₁, b₂⟩ ⟨a₂, b₂⟩;
  dsimp; split_ifs; simp [h] {contextual := tt}

theorem kreplace_nodupkeys (a : α) (b : β a) {l : list (sigma β)} :
  (kreplace a b l).nodupkeys ↔ l.nodupkeys :=
by simp [nodupkeys, keys_kreplace]

theorem perm_kreplace {a : α} {b : β a} {l₁ l₂ : list (sigma β)}
  (nd : l₁.nodupkeys) : l₁ ~ l₂ →
  kreplace a b l₁ ~ kreplace a b l₂ :=
perm_lookmap _ $ begin
  refine (nodupkeys_iff_pairwise.1 nd).imp _,
  intros x y h z h₁ w h₂,
  split_ifs at h₁ h₂; cases h₁; cases h₂,
  exact (h (h_2.symm.trans h_1)).elim
end

/- kerase -/

/-- Remove the first pair with the key `a`. -/
def kerase (a : α) : list (sigma β) → list (sigma β) :=
erasep $ λ s, a = s.1

@[simp] theorem kerase_nil {a} : @kerase _ β _ a [] = [] :=
rfl

@[simp] theorem kerase_cons_eq {a} {s : sigma β} {l : list (sigma β)} (h : a = s.1) :
  kerase a (s :: l) = l :=
by simp [kerase, h]

@[simp] theorem kerase_cons_ne {a} {s : sigma β} {l : list (sigma β)} (h : a ≠ s.1) :
  kerase a (s :: l) = s :: kerase a l :=
by simp [kerase, h]

@[simp] theorem kerase_of_not_mem_keys {a} {l : list (sigma β)} (h : a ∉ l.keys) :
  kerase a l = l :=
by induction l with _ _ ih;
   [refl, { simp [not_or_distrib] at h, simp [h.1, ih h.2] }]

theorem kerase_sublist (a : α) (l : list (sigma β)) : kerase a l <+ l :=
erasep_sublist _

theorem kerase_keys_subset (a) (l : list (sigma β)) :
  (kerase a l).keys ⊆ l.keys :=
subset_of_sublist (map_sublist_map _ (kerase_sublist a l))

theorem mem_keys_of_mem_keys_kerase {a₁ a₂} {l : list (sigma β)} :
  a₁ ∈ (kerase a₂ l).keys → a₁ ∈ l.keys :=
@kerase_keys_subset _ _ _ _ _ _

theorem exists_of_kerase {a : α} {l : list (sigma β)} (h : a ∈ l.keys) :
  ∃ (b : β a) (l₁ l₂ : list (sigma β)),
    a ∉ l₁.keys ∧
    l = l₁ ++ ⟨a, b⟩ :: l₂ ∧
    kerase a l = l₁ ++ l₂ :=
begin
  induction l,
  case list.nil { cases h },
  case list.cons : hd tl ih {
    by_cases e : a = hd.1,
    { subst e,
      exact ⟨hd.2, [], tl, by simp, by cases hd; refl, by simp⟩ },
    { simp at h,
      cases h,
      case or.inl : h { exact absurd h e },
      case or.inr : h {
        rcases ih h with ⟨b, tl₁, tl₂, h₁, h₂, h₃⟩,
        exact ⟨b, hd :: tl₁, tl₂, not_mem_cons_of_ne_of_not_mem e h₁,
               by rw h₂; refl, by simp [e, h₃]⟩ } } }
end

@[simp] theorem mem_keys_kerase_of_ne {a₁ a₂} {l : list (sigma β)} (h : a₁ ≠ a₂) :
  a₁ ∈ (kerase a₂ l).keys ↔ a₁ ∈ l.keys :=
iff.intro mem_keys_of_mem_keys_kerase $ λ p,
  if q : a₂ ∈ l.keys then
    match l, kerase a₂ l, exists_of_kerase q, p with
    | _, _, ⟨_, _, _, _, rfl, rfl⟩, p := by simpa [keys, h] using p
    end
  else
    by simp [q, p]

theorem keys_kerase {a} {l : list (sigma β)} : (kerase a l).keys = l.keys.erase a :=
by rw [keys, kerase, ←erasep_map sigma.fst l, erase_eq_erasep]

theorem kerase_nodupkeys (a : α) {l : list (sigma β)} : nodupkeys l → (kerase a l).nodupkeys :=
nodupkeys_of_sublist $ kerase_sublist _ _

theorem perm_kerase {a : α} {l₁ l₂ : list (sigma β)}
  (nd : l₁.nodupkeys) : l₁ ~ l₂ → kerase a l₁ ~ kerase a l₂ :=
perm_erasep _ $ (nodupkeys_iff_pairwise.1 nd).imp $
by rintro x y h rfl; exact h

@[simp] theorem not_mem_keys_kerase (a) {l : list (sigma β)} (nd : l.nodupkeys) :
  a ∉ (kerase a l).keys :=
begin
  induction l,
  case list.nil { simp },
  case list.cons : hd tl ih {
    simp at nd,
    by_cases h : a = hd.1,
    { subst h, simp [nd.1] },
    { simp [h, ih nd.2] } }
end

@[simp] theorem lookup_kerase (a) {l : list (sigma β)} (nd : l.nodupkeys) :
  lookup a (kerase a l) = none :=
lookup_eq_none.mpr (not_mem_keys_kerase a nd)

@[simp] theorem lookup_kerase_ne {a a'} {l : list (sigma β)} (h : a ≠ a') :
  lookup a' (kerase a l) = lookup a' l :=
begin
  induction l,
  case list.nil { refl },
  case list.cons : hd tl ih {
    cases hd with ah bh,
    by_cases h₁ : a = ah; by_cases h₂ : a' = ah,
    { substs h₁ h₂, cases ne.irrefl h },
    { subst h₁, simp [h₂] },
    { subst h₂, simp [h] },
    { simp [h₁, h₂, ih] }
  }
end

/- kinsert -/

/-- Insert the pair `⟨a, b⟩` and erase the first pair with the key `a`. -/
def kinsert (a : α) (b : β a) (l : list (sigma β)) : list (sigma β) :=
⟨a, b⟩ :: kerase a l

@[simp] theorem kinsert_def {a} {b : β a} {l : list (sigma β)} :
  kinsert a b l = ⟨a, b⟩ :: kerase a l := rfl

@[simp] theorem mem_keys_kinsert {a a'} {b : β a} {l : list (sigma β)} :
  a' ∈ (kinsert a b l).keys ↔ a = a' ∨ a' ∈ l.keys :=
by by_cases h : a = a'; [simp [h], simp [h, ne.symm h]]

theorem kinsert_nodupkeys (a) (b : β a) {l : list (sigma β)} (nd : l.nodupkeys) :
  (kinsert a b l).nodupkeys :=
nodupkeys_cons.mpr ⟨not_mem_keys_kerase a nd, kerase_nodupkeys a nd⟩

theorem perm_kinsert {a} {b : β a} {l₁ l₂ : list (sigma β)} (nd₁ : l₁.nodupkeys)
  (p : l₁ ~ l₂) : kinsert a b l₁ ~ kinsert a b l₂ :=
perm.skip ⟨a, b⟩ $ perm_kerase nd₁ p

@[simp] theorem lookup_kinsert {a} {b : β a} (l : list (sigma β)) :
  lookup a (kinsert a b l) = some b :=
by simp only [kinsert, lookup_cons_eq]

@[simp] theorem lookup_kinsert_ne {a a'} {b : β a} {l : list (sigma β)} (h : a ≠ a') :
  lookup a' (kinsert a b l) = lookup a' l :=
by simp [h, lookup_cons_ne _ ⟨a, b⟩ (ne.symm h)]

/- kextract -/

def kextract (a : α) : list (sigma β) → option (β a) × list (sigma β)
| []     := (none, [])
| (s::l) := if h : s.1 = a then (some (eq.rec_on h s.2), l) else
  let (b', l') := kextract l in (b', s :: l')

@[simp] theorem kextract_eq_lookup_kerase (a : α) :
  ∀ l : list (sigma β), kextract a l = (lookup a l, kerase a l)
| []     := rfl
| (⟨a', b⟩::l) := begin
    simp [kextract], dsimp, split_ifs,
    { subst a', simp [kerase] },
    { simp [kextract, ne.symm h, kextract_eq_lookup_kerase l, kerase] }
  end

end list
