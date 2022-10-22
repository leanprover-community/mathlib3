import data.finite.basic
import data.enat.basic

/-!
-/

open_locale classical

namespace enat

variables (α β : Sort*)

protected noncomputable def card (α : Sort*) : ℕ∞ :=
if h : ∃ n, nonempty (α ≃ fin n) then h.some else ⊤

prefix `#ₑ`:70 := enat.card

protected noncomputable def _root_.nat.card (α : Sort*) : ℕ := (enat.card α).to_nat

prefix `#ₙ`:70 := nat.card

lemma card_lt_top [finite α] : #ₑα < ⊤ :=
by simp only [enat.card, dif_pos, finite.exists_equiv_fin α, with_top.coe_lt_top]

@[simp] lemma card_finite [finite α] : #ₑα = #ₙα :=
eq.symm $ enat.coe_to_nat_eq_self.2 (card_lt_top α).ne

@[simp] lemma card_infinite [infinite α] : #ₑα = ⊤ :=
dif_neg $ mt finite_iff_exists_equiv_fin.2 (@not_finite α _)

lemma card_eq_top_iff : #ₑα = ⊤ ↔ infinite α :=
⟨λ h₁, ⟨λ h₂, (@card_lt_top α h₂).ne h₁⟩, @card_infinite α⟩

lemma card_lt_top_iff : #ₑα < ⊤ ↔ finite α :=
by simp only [lt_top_iff_ne_top, ne.def, card_eq_top_iff, not_infinite_iff_finite]

variables {α β}

lemma card_congr (e : α ≃ β) : #ₑα = #ₑβ :=
begin
  have : ∀ n, nonempty (α ≃ fin n) ↔ nonempty (β ≃ fin n) :=
    λ n, nonempty.congr e.symm.trans e.trans,
  simp only [enat.card, this]
end

@[simp] lemma card_plift : #ₑ(plift α) = #ₑα := card_congr equiv.plift
@[simp] lemma {u v} card_ulift (α : Type v) : #ₑ(ulift.{u} α) = #ₑα := card_congr equiv.ulift

lemma card_fin (n : ℕ) : #ₑ(fin n) = n :=
begin
  have : ∃ k, nonempty (fin n ≃ fin k) := ⟨n, ⟨equiv.refl _⟩⟩,
  rw [enat.card, dif_pos this, with_top.coe_eq_coe, eq_comm, ← fin.equiv_iff_eq],
  exact this.some_spec
end

lemma card_of_equiv_fin {n} (e : α ≃ fin n) : #ₑα = n := by rw [card_congr e, card_fin]

lemma card_eq_nat_iff {n : ℕ} : #ₑα = n ↔ nonempty (α ≃ fin n) :=
begin
  refine ⟨λ h, _, λ ⟨e⟩, card_of_equiv_fin e⟩,
  haveI : finite α, by { rw [← card_lt_top_iff, h], exact with_top.coe_lt_top _ },
  rcases finite.exists_equiv_fin α with ⟨k, hk⟩,
  rw [hk.elim card_of_equiv_fin, with_top.coe_eq_coe] at h,
  rwa [← h]
end

lemma card_eq_zero_iff : #ₑα = 0 ↔ is_empty α :=
begin
  rw [← nat.cast_zero, card_eq_nat_iff],
  exact ⟨λ ⟨e⟩, e.is_empty, λ h, ⟨@equiv.equiv_of_is_empty _ _ h _⟩⟩,
end

lemma card_pos_iff : 0 < #ₑα ↔ nonempty α :=
by simpa only [not_is_empty_iff, ← nonpos_iff_eq_zero, not_le] using card_eq_zero_iff.not

lemma card_le_nat_iff {n : ℕ} : #ₑα ≤ n ↔ nonempty (α ↪ fin n) :=
begin
  casesI finite_or_infinite α,
  { rcases finite.exists_equiv_fin α with ⟨k, ⟨e⟩⟩,
    rw [card_congr e, card_fin, with_top.coe_le_coe,
      (e.embedding_congr (equiv.refl _)).nonempty_congr, function.embedding.nonempty_iff_card_le,
      fintype.card_fin, fintype.card_fin] },
  { simpa [card_infinite] using @function.embedding.is_empty α _ _ _, }
end

lemma card_le_card_iff [countable α] : #ₑα ≤ #ₑβ ↔ nonempty (α ↪ β) :=
begin
  
end

end enat

namespace nat

section sort

variables {α β : Sort*}

lemma card_congr (e : α ≃ β) : #ₙα = #ₙβ := congr_arg enat.to_nat (enat.card_congr e)
@[simp] lemma card_plift : #ₙ(plift α) = #ₙα := card_congr equiv.plift
@[simp] lemma {u v} card_ulift (α : Type v) : #ₙ(ulift.{u} α) = #ₙα := card_congr equiv.ulift

lemma card_of_equiv_fin {n} (e : α ≃ fin n) : #ₙα = n :=
by rw [nat.card, enat.card_of_equiv_fin e, enat.to_nat_coe]

@[simp] lemma card_infinite (α : Sort*) [infinite α] : #ₙα = 0 := by simp [nat.card]

end sort

variables {α β : Type*}

@[simp] lemma card_fintype [fintype α] : #ₙα = fintype.card α :=
card_of_equiv_fin $ fintype.equiv_fin _

lemma card_fin (n : ℕ) : #ₙ(fin n) = n := card_of_equiv_fin (equiv.refl _)

@[simp] lemma card_prod [finite α] [finite β] : #ₙ(α × β) = #ₙα * #ₙβ :=
by { casesI nonempty_fintype α, casesI nonempty_fintype β, simp }

@[simp] lemma card_sum [finite α] [finite β] : #ₙ(α ⊕ β) = #ₙα + #ₙβ :=
by { casesI nonempty_fintype α, casesI nonempty_fintype β, simp }

end nat

namespace enat

section sort

variables {α : Sort*}

lemma card_eq_zero_iff : #ₑα = 0 ↔ is_empty α :=


end sort

variables (α β : Type*)

@[simp] lemma card_prod : #ₑ(α × β) = #ₑα * #ₑβ :=
begin
  casesI is_empty_or_nonempty α, { simp },
  casesI is_empty_or_nonempty β, { simp },
  casesI finite_or_infinite α, rotate, { simp },
end

end enat
