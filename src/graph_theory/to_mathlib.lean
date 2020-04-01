import tactic
import data.equiv.fin

-- TODO do these exist? find them or find homes for these

def fintype.fibre {α : Type*} [fintype α] {β : Type*} [decidable_eq β] (f : α → β) (b : β) : finset α :=
set.to_finset { a | f a = b }

@[simp]
lemma fintype.mem_fibre {α : Type*} [fintype α] {β : Type*} [decidable_eq β] (f : α → β) (b : β) (a : α) :
  a ∈ fintype.fibre f b ↔ f a = b :=
by simp [fintype.fibre]

@[simp]
lemma fintype.fibre_prod_fst {α : Type*} [fintype α] [decidable_eq α] {β : Type*} [fintype β] (a : α) :
  fintype.fibre (λ p : α × β, p.1) a = (@finset.univ β _).map (embedding.inr a β) :=
begin
  ext p,
  simp,
  split,
  { rintros rfl, exact ⟨p.2, (by { ext; refl })⟩ },
  { rintros ⟨b, rfl⟩, refl, }
end

@[simp]
lemma fintype.fibre_prod_snd {α : Type*} [fintype α] {β : Type*} [fintype β] [decidable_eq β] (b : β) :
  fintype.fibre (λ p : α × β, p.2) b = (@finset.univ α _).map (embedding.inl α b) :=
begin
  ext p,
  simp,
  split,
  { rintros rfl, exact ⟨p.1, (by { ext; refl })⟩ },
  { rintros ⟨b, rfl⟩, refl, }
end

@[simp]
lemma fintype.card_fibre {α : Type*} [fintype α] {β : Type*} [decidable_eq β] (f : α → β) (b : β) :
  finset.card (fintype.fibre f b) = fintype.card { a | f a = b } :=
to_finset_card _

lemma fintype.fibres_disjoint {α : Type*} [fintype α] [decidable_eq α] {β : Type*} [decidable_eq β] (f : α → β) (b₁ b₂ : β) (h : b₁ ≠ b₂) :
  disjoint (fintype.fibre f b₁) (fintype.fibre f b₂) :=
begin
  dsimp [disjoint],
  rintros a w,
  simp [fintype.fibre] at w,
  exact false.elim (h (w.1.symm.trans w.2))
end
