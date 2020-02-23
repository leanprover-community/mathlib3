/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sean Leather

Functions on lists of sigma types.
-/
import data.list.perm data.sigma

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

lemma mem_ext {l₀ l₁ : list (sigma β)}
  (nd₀ : l₀.nodup) (nd₁ : l₁.nodup)
  (h : ∀ x, x ∈ l₀ ↔ x ∈ l₁) : l₀ ~ l₁ :=
begin
  induction l₀ with x xs generalizing l₁; cases l₁ with x ys,
  { constructor },
  iterate 2
  { specialize h x, simp at h,
    cases h },
  simp at nd₀ nd₁, rename x y, classical,
  cases nd₀, cases nd₁,
  by_cases h' : x = y,
  { subst y, constructor, apply l₀_ih ‹ _ › ‹ nodup ys ›,
    intro a, specialize h a, simp at h,
    by_cases h' : a = x,
    { subst a, rw ← not_iff_not, split; intro; assumption },
    { simp [h'] at h, exact h } },
  { transitivity x :: y :: ys.erase x,
    { constructor, apply l₀_ih ‹ _ ›,
      { simp, split, { intro, apply nd₁_left, apply mem_of_mem_erase a },
        apply nodup_erase_of_nodup; assumption },
      { intro a, specialize h a, simp at h,
        by_cases h' : a = x,
        { subst a, rw ← not_iff_not, split; intro, simp [mem_erase_of_nodup,*], assumption },
        { simp [h'] at h, simp [h], apply or_congr, refl,
          simp [mem_erase_of_ne,*] } } },
    transitivity y :: x :: ys.erase x,
    { constructor },
    { constructor, symmetry, apply perm_erase,
      specialize h x, simp [h'] at h, exact h } }
end

lemma lookup_ext {l₀ l₁ : list (sigma β)}
  (nd₀ : l₀.nodupkeys) (nd₁ : l₁.nodupkeys)
  (h : ∀ x y, y ∈ l₀.lookup x ↔ y ∈ l₁.lookup x) : l₀ ~ l₁ :=
mem_ext (nodup_of_nodupkeys nd₀) (nodup_of_nodupkeys nd₁)
  (λ ⟨a,b⟩, by rw [← mem_lookup_iff, ← mem_lookup_iff, h]; assumption)

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

theorem kerase_kerase {a a'} {l : list (sigma β)} : (kerase a' l).kerase a = (kerase a l).kerase a' :=
begin
  by_cases a = a',
  { subst a' },
  induction l with x xs, { refl },
  { by_cases a' = x.1,
    { subst a', simp [kerase_cons_ne h,kerase_cons_eq rfl] },
    by_cases h' : a = x.1,
    { subst a, simp [kerase_cons_eq rfl,kerase_cons_ne (ne.symm h)] },
    { simp [kerase_cons_ne,*] } }
end

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
  lookup a (kerase a' l) = lookup a l :=
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

theorem kerase_append_left {a} : ∀ {l₁ l₂ : list (sigma β)},
  a ∈ l₁.keys → kerase a (l₁ ++ l₂) = kerase a l₁ ++ l₂
| []        _  h  := by cases h
| (s :: l₁) l₂ h₁ :=
  if h₂ : a = s.1 then
    by simp [h₂]
  else
    by simp at h₁;
       cases h₁;
       [exact absurd h₁ h₂, simp [h₂, kerase_append_left h₁]]

theorem kerase_append_right {a} : ∀ {l₁ l₂ : list (sigma β)},
  a ∉ l₁.keys → kerase a (l₁ ++ l₂) = l₁ ++ kerase a l₂
| []        _  h := rfl
| (_ :: l₁) l₂ h := by simp [not_or_distrib] at h;
                       simp [h.1, kerase_append_right h.2]

theorem kerase_comm (a₁ a₂) (l : list (sigma β)) :
  kerase a₂ (kerase a₁ l) = kerase a₁ (kerase a₂ l) :=
if h : a₁ = a₂ then
  by simp [h]
else if ha₁ : a₁ ∈ l.keys then
  if ha₂ : a₂ ∈ l.keys then
    match l, kerase a₁ l, exists_of_kerase ha₁, ha₂ with
    | _, _, ⟨b₁, l₁, l₂, a₁_nin_l₁, rfl, rfl⟩, a₂_in_l₁_app_l₂ :=
      if h' : a₂ ∈ l₁.keys then
        by simp [kerase_append_left h',
                 kerase_append_right (mt (mem_keys_kerase_of_ne h).mp a₁_nin_l₁)]
      else
        by simp [kerase_append_right h', kerase_append_right a₁_nin_l₁,
                 @kerase_cons_ne _ _ _ a₂ ⟨a₁, b₁⟩ _ (ne.symm h)]
    end
  else
    by simp [ha₂, mt mem_keys_of_mem_keys_kerase ha₂]
else
  by simp [ha₁, mt mem_keys_of_mem_keys_kerase ha₁]

/- kinsert -/

/-- Insert the pair `⟨a, b⟩` and erase the first pair with the key `a`. -/
def kinsert (a : α) (b : β a) (l : list (sigma β)) : list (sigma β) :=
⟨a, b⟩ :: kerase a l

@[simp] theorem kinsert_def {a} {b : β a} {l : list (sigma β)} :
  kinsert a b l = ⟨a, b⟩ :: kerase a l := rfl

theorem mem_keys_kinsert {a a'} {b' : β a'} {l : list (sigma β)} :
  a ∈ (kinsert a' b' l).keys ↔ a = a' ∨ a ∈ l.keys :=
by by_cases h : a = a'; simp [h]

theorem kinsert_nodupkeys (a) (b : β a) {l : list (sigma β)} (nd : l.nodupkeys) :
  (kinsert a b l).nodupkeys :=
nodupkeys_cons.mpr ⟨not_mem_keys_kerase a nd, kerase_nodupkeys a nd⟩

theorem perm_kinsert {a} {b : β a} {l₁ l₂ : list (sigma β)} (nd₁ : l₁.nodupkeys)
  (p : l₁ ~ l₂) : kinsert a b l₁ ~ kinsert a b l₂ :=
perm.skip ⟨a, b⟩ $ perm_kerase nd₁ p

theorem lookup_kinsert {a} {b : β a} (l : list (sigma β)) :
  lookup a (kinsert a b l) = some b :=
by simp only [kinsert, lookup_cons_eq]

theorem lookup_kinsert_ne {a a'} {b' : β a'} {l : list (sigma β)} (h : a ≠ a') :
  lookup a (kinsert a' b' l) = lookup a l :=
by simp [h]

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

/- erase_dupkeys -/

def erase_dupkeys : list (sigma β) → list (sigma β) :=
list.foldr (λ ⟨x,y⟩, kinsert x y) []

lemma erase_dupkeys_cons {x : α} {y : β x} (l : list (sigma β)) : erase_dupkeys (⟨x,y⟩ :: l) = kinsert x y (erase_dupkeys l) := rfl

lemma nodupkeys_erase_dupkeys (l : list (sigma β)) : nodupkeys (erase_dupkeys l) :=
begin
  dsimp [erase_dupkeys], generalize hl : nil = l',
  have : nodupkeys l', { rw ← hl, apply nodup_nil },
  clear hl,
  induction l with x xs,
  { apply this },
  { cases x, simp [erase_dupkeys], split,
    { simp [keys_kerase], apply mem_erase_of_nodup l_ih },
    apply kerase_nodupkeys _ l_ih, }
end

lemma lookup_erase_dupkeys (a : α) (l : list (sigma β)) : lookup a (erase_dupkeys l) = lookup a l :=
begin
  induction l, refl,
  cases l_hd with a' b,
  by_cases a = a',
  { subst a', rw [erase_dupkeys_cons,lookup_kinsert,lookup_cons_eq] },
  { rw [erase_dupkeys_cons,lookup_kinsert_ne h,l_ih,lookup_cons_ne], exact h },
end

/- kunion -/

/-- `kunion l₁ l₂` is the append to l₁ of l₂ after, for each key in l₁, the
first matching pair in l₂ is erased. -/
def kunion : list (sigma β) → list (sigma β) → list (sigma β)
| []        l₂ := l₂
| (s :: l₁) l₂ := s :: kunion l₁ (kerase s.1 l₂)

@[simp] theorem nil_kunion {l : list (sigma β)} : kunion [] l = l :=
rfl

@[simp] theorem kunion_nil : ∀ {l : list (sigma β)}, kunion l [] = l
| []       := rfl
| (_ :: l) := by rw [kunion, kerase_nil, kunion_nil]

@[simp] theorem kunion_cons {s} {l₁ l₂ : list (sigma β)} :
  kunion (s :: l₁) l₂ = s :: kunion l₁ (kerase s.1 l₂) :=
rfl

@[simp] theorem mem_keys_kunion {a} {l₁ l₂ : list (sigma β)} :
  a ∈ (kunion l₁ l₂).keys ↔ a ∈ l₁.keys ∨ a ∈ l₂.keys :=
begin
  induction l₁ generalizing l₂,
  case list.nil { simp },
  case list.cons : s l₁ ih { by_cases h : a = s.1; [simp [h], simp [h, ih]] }
end

@[simp] theorem kunion_kerase {a} : ∀ {l₁ l₂ : list (sigma β)},
  kunion (kerase a l₁) (kerase a l₂) = kerase a (kunion l₁ l₂)
| []       _ := rfl
| (s :: _) l := by by_cases h : a = s.1;
                   simp [h, kerase_comm a s.1 l, kunion_kerase]

theorem kunion_nodupkeys {l₁ l₂ : list (sigma β)}
  (nd₁ : l₁.nodupkeys) (nd₂ : l₂.nodupkeys) : (kunion l₁ l₂).nodupkeys :=
begin
  induction l₁ generalizing l₂,
  case list.nil { simp only [nil_kunion, nd₂] },
  case list.cons : s l₁ ih {
    simp at nd₁,
    simp [not_or_distrib, nd₁.1, nd₂, ih nd₁.2 (kerase_nodupkeys s.1 nd₂)] }
end

theorem perm_kunion_left {l₁ l₂ : list (sigma β)} (p : l₁ ~ l₂) (l) :
  kunion l₁ l ~ kunion l₂ l :=
begin
  induction p generalizing l,
  case list.perm.nil { refl },
  case list.perm.skip : hd tl₁ tl₂ p ih {
    simp [ih (kerase hd.1 l), perm.skip] },
  case list.perm.swap : s₁ s₂ l {
    simp [kerase_comm, perm.swap] },
  case list.perm.trans : l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ {
    exact perm.trans (ih₁₂ l) (ih₂₃ l) }
end

theorem perm_kunion_right : ∀ l {l₁ l₂ : list (sigma β)},
  l₁.nodupkeys → l₁ ~ l₂ → kunion l l₁ ~ kunion l l₂
| []       _  _  _   p := p
| (s :: l) l₁ l₂ nd₁ p :=
  by simp [perm.skip s
    (perm_kunion_right l (kerase_nodupkeys s.1 nd₁) (perm_kerase nd₁ p))]

theorem perm_kunion {l₁ l₂ l₃ l₄ : list (sigma β)} (nd₃ : l₃.nodupkeys)
  (p₁₂ : l₁ ~ l₂) (p₃₄ : l₃ ~ l₄) : kunion l₁ l₃ ~ kunion l₂ l₄ :=
perm.trans (perm_kunion_left p₁₂ l₃) (perm_kunion_right l₂ nd₃ p₃₄)

@[simp] theorem lookup_kunion_left {a} {l₁ l₂ : list (sigma β)} (h : a ∈ l₁.keys) :
  lookup a (kunion l₁ l₂) = lookup a l₁ :=
begin
  induction l₁ with s _ ih generalizing l₂; simp at h; cases h; cases s with a',
  { subst h, simp },
  { rw kunion_cons,
    by_cases h' : a = a',
    { subst h', simp },
    { simp [h', ih h] } }
end

@[simp] theorem lookup_kunion_right {a} {l₁ l₂ : list (sigma β)} (h : a ∉ l₁.keys) :
  lookup a (kunion l₁ l₂) = lookup a l₂ :=
begin
  induction l₁ generalizing l₂,
  case list.nil { simp },
  case list.cons : _ _ ih { simp [not_or_distrib] at h, simp [h.1, ih h.2] }
end

@[simp] theorem mem_lookup_kunion {a} {b : β a} {l₁ l₂ : list (sigma β)} :
  b ∈ lookup a (kunion l₁ l₂) ↔ b ∈ lookup a l₁ ∨ a ∉ l₁.keys ∧ b ∈ lookup a l₂ :=
begin
  induction l₁ generalizing l₂,
  case list.nil { simp },
  case list.cons : s _ ih {
    cases s with a',
    by_cases h₁ : a = a',
    { subst h₁, simp },
    { let h₂ := @ih (kerase a' l₂), simp [h₁] at h₂, simp [h₁, h₂] } }
end

theorem mem_lookup_kunion_middle {a} {b : β a} {l₁ l₂ l₃ : list (sigma β)}
  (h₁ : b ∈ lookup a (kunion l₁ l₃)) (h₂ : a ∉ keys l₂) :
  b ∈ lookup a (kunion (kunion l₁ l₂) l₃) :=
match mem_lookup_kunion.mp h₁ with
| or.inl h := mem_lookup_kunion.mpr (or.inl (mem_lookup_kunion.mpr (or.inl h)))
| or.inr h := mem_lookup_kunion.mpr $
  or.inr ⟨mt mem_keys_kunion.mp (not_or_distrib.mpr ⟨h.1, h₂⟩), h.2⟩
end

end list
