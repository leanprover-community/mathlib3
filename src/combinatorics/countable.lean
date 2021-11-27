import logic.embedding
import data.nat.pairing

/-!
-/

universes u v

open function

variables {α : Sort u} {β : Sort v}

class countable (α : Sort u) : Prop :=
(out' : nonempty (α ↪ ℕ))

instance : countable ℕ := ⟨⟨embedding.refl ℕ⟩⟩

lemma countable_iff_exists_injective :
  countable α ↔ ∃ f : α → ℕ, injective f :=
⟨λ ⟨⟨f⟩⟩, ⟨f, f.2⟩, λ ⟨f, hf⟩, ⟨⟨⟨f, hf⟩⟩⟩⟩

lemma countable_iff_nonempty_embedding : countable α ↔ nonempty (α ↪ ℕ) :=
⟨λ h, h.1, λ h, ⟨h⟩⟩

lemma nonempty_embedding_nat (α) [countable α] : nonempty (α ↪ ℕ) := ‹countable α›.1

protected lemma function.injective.countable [countable β] {f : α → β} (hf : injective f) :
  countable α :=
let ⟨e⟩ := nonempty_embedding_nat β in ⟨⟨embedding.trans ⟨f, hf⟩ e⟩⟩

protected lemma function.embedding.countable [countable β] (f : α ↪ β) : countable α :=
f.injective.countable

protected lemma function.surjective.countable [countable α] {f : α → β} (hf : surjective f) :
  countable β :=
(injective_surj_inv hf).countable

lemma countable_iff_exists_surjective [nonempty α] : countable α ↔ ∃ f : ℕ → α, surjective f :=
⟨λ ⟨⟨f⟩⟩, ⟨inv_fun f, inv_fun_surjective f.injective⟩, λ ⟨f, hf⟩, hf.countable⟩

protected lemma equiv.countable [countable β] (e : α ≃ β) : countable α := e.injective.countable

lemma equiv.countable_iff (e : α ≃ β) : countable α ↔ countable β :=
⟨λ h, @equiv.countable _ _ h e.symm, λ h, @equiv.countable _ _ h e⟩

instance [countable α] : countable (plift α) := equiv.plift.injective.countable

instance {α : Type u} [countable α] : countable (ulift.{v} α) :=
equiv.ulift.injective.countable

instance [countable α] [countable β] : countable (pprod α β) :=
let ⟨f⟩ := nonempty_embedding_nat α, ⟨g⟩ := nonempty_embedding_nat β in
((f.pprod_map g).trans (equiv.pprod_equiv_prod.trans nat.mkpair_equiv).to_embedding).countable

instance {α β : Type*} [countable α] [countable β] : countable (α × β) :=
equiv.pprod_equiv_prod.symm.countable

instance {π : α → Sort*} [countable α] [∀ a, countable (π a)] : countable (Σ' a, π a) :=
begin
  cases nonempty_embedding_nat α with f,
  set g : Π a : α, π a ↪ ℕ := λ a, (nonempty_embedding_nat (π a)).some,
  refine ⟨⟨⟨λ x, nat.mkpair (f x.1) (g x.1 x.2), _⟩⟩⟩,
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h,
  simp only [nat.mkpair_eq_mkpair, embedding.apply_eq_iff_eq] at h,
  rcases h with ⟨rfl, h⟩,
  obtain rfl : b₁ = b₂ := (g a₁).injective h,
  refl
end

instance {α} {π : α → Type*} [countable α] [∀ a, countable (π a)] : countable (Σ a, π a) :=
(equiv.psigma_equiv_sigma π).symm.countable

instance Prop.countable' (p : Prop) : countable p :=
by { refine ⟨⟨⟨λ _, 0, λ x y h, _⟩⟩⟩, refl }

instance bool.countable : countable bool :=
⟨⟨⟨λ b, cond b 0 1, bool.injective_iff.2 one_ne_zero⟩⟩⟩

instance : countable Prop := equiv.Prop_equiv_bool.countable

@[priority 500]
instance [countable α] {p : α → Prop} : countable {x // p x} := subtype.val_injective.countable

@[priority 500]
instance set_coe.countable {α} [countable α] (s : set α) : countable s := subtype.countable

instance [countable α] [countable β] : countable (psum α β) :=
begin
  rcases nonempty_embedding_nat α with ⟨ea⟩,
  rcases nonempty_embedding_nat β with ⟨eb⟩,
  refine ⟨⟨⟨λ x, psum.rec_on x (bit0 ∘ ea) (bit1 ∘ eb), _⟩⟩⟩,
  rintro (a|a) (b|b) h; simp only [embedding.apply_eq_iff_eq, nat.bit0_eq_bit0, nat.bit0_ne_bit1,
    nat.bit1_ne_bit0, nat.bit1_eq_bit1] at h,
  exacts [h ▸ rfl, h.elim, h.elim, h ▸ rfl]
end

instance {α β} [countable α] [countable β] : countable (α ⊕ β) :=
(equiv.psum_equiv_sum α β).symm.countable

