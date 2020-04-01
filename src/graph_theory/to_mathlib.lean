import tactic
import data.equiv.fin

-- TODO do these exist? find them or find homes for these

lemma exists_true_of_non_empty {α : Sort*} (n : nonempty α) : ∃ a : α, true :=
nonempty.dcases_on n (λ (n : α), Exists.intro n trivial)

noncomputable def nonempty.choose {α : Sort*} (n : nonempty α) : α :=
classical.indefinite_description _ (exists_true_of_non_empty n)

@[simp]
lemma foo {α β : Sort*} (e : α ≃ β) : function.embedding.trans (e.to_embedding) (e.symm.to_embedding) = function.embedding.refl _ :=
by { ext, simp, }
@[simp]
lemma foo' {α β : Sort*} (e : α ≃ β) : function.embedding.trans (e.symm.to_embedding) (e.to_embedding) = function.embedding.refl _ :=
by { ext, simp, }

def embedding.punit {β : Sort*} (b : β) : punit ↪ β :=
⟨λ _, b, by { rintros ⟨⟩ ⟨⟩ _, refl, }⟩

def embedding.inl {α : Sort*} (a : α) (β : Sort*): β ↪ α × β :=
⟨λ b, (a, b), λ b b' h, congr_arg prod.snd h⟩

def embedding.inr (α : Sort*) {β : Sort*} (b : β) : α ↪ α × β :=
⟨λ a, (a, b), λ a a' h, congr_arg prod.fst h⟩

def fintype.fibre {α : Type*} [fintype α] {β : Type*} [decidable_eq β] (f : α → β) (b : β) : finset α :=
set.to_finset { a | f a = b }

@[simp]
lemma fintype.mem_fibre {α : Type*} [fintype α] {β : Type*} [decidable_eq β] (f : α → β) (b : β) (a : α) :
  a ∈ fintype.fibre f b ↔ f a = b :=
by simp [fintype.fibre]

@[simp]
lemma fintype.fibre_prod_fst {α : Type*} [fintype α] [decidable_eq α] {β : Type*} [fintype β] (a : α) :
  fintype.fibre (λ p : α × β, p.1) a = (@finset.univ β _).map (embedding.inl a β) :=
begin
  ext p,
  simp,
  split,
  { rintros rfl, exact ⟨p.2, (by { ext; refl })⟩ },
  { rintros ⟨b, rfl⟩, refl, }
end

@[simp]
lemma fintype.fibre_prod_snd {α : Type*} [fintype α] {β : Type*} [fintype β] [decidable_eq β] (b : β) :
  fintype.fibre (λ p : α × β, p.2) b = (@finset.univ α _).map (embedding.inr α b) :=
begin
  ext p,
  simp,
  split,
  { rintros rfl, exact ⟨p.1, (by { ext; refl })⟩ },
  { rintros ⟨b, rfl⟩, refl, }
end


attribute [simp] finset.map_refl
@[simp]
lemma finset.map_trans {α β γ : Sort*} (i : α ↪ β) (j : β ↪ γ) (s) :
  finset.map (i.trans j) s = finset.map j (finset.map i s) :=
begin
  ext g, split,
  { simp, rintros a m rfl, exact ⟨i a, ⟨⟨a, ⟨m, rfl⟩⟩, rfl⟩⟩ },
  { simp, rintros b a m rfl rfl, exact ⟨_, ⟨m, rfl⟩⟩  },
end

@[simp]
lemma to_finset_card {α : Type*} (s : set α) [fintype s] : finset.card (set.to_finset s) = fintype.card s :=
multiset.card_map subtype.val finset.univ.val

@[simp]
lemma fintype.card_fibre {α : Type*} [fintype α] {β : Type*} [decidable_eq β] (f : α → β) (b : β) :
  finset.card (fintype.fibre f b) = fintype.card { a | f a = b } :=
to_finset_card _

def fintype.fibres_disjoint {α : Type*} [fintype α] [decidable_eq α] {β : Type*} [decidable_eq β] (f : α → β) (b₁ b₂ : β) (h : b₁ ≠ b₂) :
  disjoint (fintype.fibre f b₁) (fintype.fibre f b₂) :=
begin
  dsimp [disjoint],
  rintros a w,
  simp [fintype.fibre] at w,
  exact false.elim (h (w.1.symm.trans w.2))
end
