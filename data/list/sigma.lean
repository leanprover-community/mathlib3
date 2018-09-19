import data.list.basic

universes u v

namespace list
variables {α : Type u} {β : α → Type v}

/- knodup -/

def knodup (l : list (sigma β)) : Prop :=
(l.map sigma.fst).nodup

@[simp] theorem knodup_nil : @knodup α β [] := pairwise.nil _

@[simp] theorem knodup_cons {a : α} {b : β a} {l : list (sigma β)} :
  knodup (⟨a, b⟩::l) ↔ (∀ b' : β a, sigma.mk a b' ∉ l) ∧ knodup l :=
by simp [knodup]

theorem knodup_singleton (s : sigma β) : knodup [s] := nodup_singleton _

theorem knodup_of_sublist {l₁ l₂ : list (sigma β)} (h : l₁ <+ l₂) : knodup l₂ → knodup l₁ :=
nodup_of_sublist (map_sublist_map _ h)

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
  (lookup a l).is_some ↔ ∃ b : β a, sigma.mk a b ∈ l
| []             := by simp
| (⟨a', b⟩ :: l) := begin
  by_cases h : a = a',
  { subst a', simp, exact ⟨b, or.inl rfl⟩ },
  { simp [h, lookup_is_some] },
end

theorem lookup_eq_none {a : α} {l : list (sigma β)} :
  lookup a l = none ↔ ∀ b : β a, sigma.mk a b ∉ l :=
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

theorem map_lookup_eq_find (a : α) : ∀ l : list (sigma β),
  (lookup a l).map (sigma.mk a) = find (λ s, a = s.1) l
| [] := rfl
| (⟨a', b'⟩ :: l) := begin
  by_cases h : a = a',
  { subst a', simp },
  { simp [h, map_lookup_eq_find] }
end

theorem mem_lookup_iff {a : α} {b : β a} {l : list (sigma β)} (nd : l.knodup) :
  b ∈ lookup a l ↔ sigma.mk a b ∈ l :=
⟨of_mem_lookup, λ h, begin
  induction l with s l IH generalizing b; cases h with h h,
  { subst s, simp },
  { cases s with a' b',
    by_cases h' : a = a',
    { subst h', simp,
      exact (not_mem_of_nodup_cons nd).elim (mem_map_of_mem sigma.fst h : _) },
    { simpa [h'] using IH (nodup_of_nodup_cons nd) h } }
end⟩

/- lookup_all -/

/-- `lookup_all a l` is the first value in `l` corresponding to the key `a`,
  or `none` if no such element exists. -/
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


/- kreplace -/

def kreplace (a : α) (b : β a) : list (sigma β) → list (sigma β) :=
lookmap $ λ s, if h : a = s.1 then some ⟨a, b⟩ else none

theorem kreplace_map_fst (a : α) (b : β a) : ∀ l : list (sigma β),
  (kreplace a b l).map sigma.fst = l.map sigma.fst :=
lookmap_map_eq _ $ by rintro ⟨a₁, b₂⟩ ⟨a₂, b₂⟩;
  dsimp; split_ifs; simp [h] {contextual := tt}

theorem kreplace_knodup (a : α) (b : β a) {l : list (sigma β)} :
  (kreplace a b l).knodup ↔ l.knodup :=
by simp [knodup, kreplace_map_fst]

/- kerase -/

def kerase (a : α) : list (sigma β) → list (sigma β) :=
erasep $ λ s, s.1 = a

theorem kerase_sublist (a : α) (l : list (sigma β)) : kerase a l <+ l :=
erasep_sublist _

theorem kerase_knodup (a : α) {l : list (sigma β)} : knodup l → (kerase a l).knodup :=
knodup_of_sublist $ kerase_sublist _ _

end list