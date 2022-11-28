import data.finite.defs
import data.enat.basic
import logic.equiv.fin

/-!
-/

open_locale classical
open function

variables {α β : Sort*} {γ δ : Type*}

protected noncomputable def enat.card (α : Sort*) : ℕ∞ :=
if h : ∃ n, nonempty (α ≃ fin n) then h.some else ⊤

prefix `#ₑ `:70 := enat.card

protected noncomputable def nat.card (α : Sort*) : ℕ := (#ₑ α).to_nat

prefix `#ₙ `:70 := nat.card

namespace enat

lemma card_eq_nat_iff {n : ℕ} : #ₑα = n ↔ nonempty (α ≃ fin n) :=
begin
  simp only [enat.card, dite_eq_iff, with_top.coe_eq_coe, with_top.top_ne_coe, exists_false,
    or_false],
  refine ⟨λ ⟨h, hn⟩, hn ▸ h.some_spec, λ h, ⟨⟨n, h⟩, fin.equiv_iff_eq.1 _⟩⟩,
  exact (Exists.some_spec (⟨n, h⟩ : ∃ n, nonempty (α ≃ fin n))).map2 (λ e₁ e₂, e₁.symm.trans e₂) h
end

variable (α)

@[simp] lemma to_nat_card : (#ₑ α).to_nat = #ₙ α := rfl

@[simp] lemma card_finite [finite α] : #ₑα = #ₙα :=
by simp only [enat.card, nat.card, dif_pos, finite.exists_equiv_fin α, to_nat_coe]

@[simp] lemma card_infinite [infinite α] : #ₑα = ⊤ :=
dif_neg $ mt finite_iff_exists_equiv_fin.2 (@not_finite α _)

lemma _root_.finite.nonempty_equiv_fin [finite α] : nonempty (α ≃ fin (#ₙ α)) :=
enat.card_eq_nat_iff.1 $ enat.card_finite _

lemma card_lt_top [finite α] : #ₑα < ⊤ := (card_finite α).symm ▸ with_top.coe_lt_top _
lemma card_ne_top [finite α] : #ₑα ≠ ⊤ := (card_lt_top α).ne

lemma card_eq_top_iff : #ₑα = ⊤ ↔ infinite α :=
⟨λ h₁, ⟨λ h₂, @card_ne_top α h₂ h₁⟩, @card_infinite α⟩

lemma card_lt_top_iff : #ₑα < ⊤ ↔ finite α :=
by simp only [lt_top_iff_ne_top, ne.def, card_eq_top_iff, not_infinite_iff_finite]

variable {α}

lemma card_congr (e : α ≃ β) : #ₑα = #ₑβ :=
have ∀ n, nonempty (α ≃ fin n) ↔ nonempty (β ≃ fin n),
  from λ n, nonempty.congr e.symm.trans e.trans,
by simp only [enat.card, this]


lemma card_eq_of_bijective (f : α → β) (hf : bijective f) : #ₑ α = #ₑ β :=
card_congr (equiv.of_bijective f hf)

@[simp] lemma {u v} card_ulift (α : Type v) : #ₑ(ulift.{u} α) = #ₑα := card_congr equiv.ulift

lemma card_fin (n : ℕ) : #ₑ(fin n) = n := card_eq_nat_iff.2 ⟨equiv.refl _⟩

lemma card_eq_of_equiv_fin {n} (e : α ≃ fin n) : #ₑα = n := by rw [card_congr e, card_fin]

lemma card_eq_zero_iff : #ₑα = 0 ↔ is_empty α :=
begin
  rw [← nat.cast_zero, card_eq_nat_iff],
  exact ⟨λ ⟨e⟩, e.is_empty, λ h, ⟨@equiv.equiv_of_is_empty _ _ h _⟩⟩,
end

lemma card_pos_iff : 0 < #ₑα ↔ nonempty α :=
by simpa only [not_is_empty_iff, ← nonpos_iff_eq_zero, not_le] using card_eq_zero_iff.not

lemma one_le_card_iff : 1 ≤ #ₑ α ↔ nonempty α := one_le_iff_pos.trans card_pos_iff

lemma card_le_nat_iff {n : ℕ} : #ₑα ≤ n ↔ nonempty (α ↪ fin n) :=
begin
  casesI finite_or_infinite α,
  { rcases finite.exists_equiv_fin α with ⟨k, ⟨e⟩⟩,
    rw [card_congr e, card_fin, with_top.coe_le_coe,
      (e.embedding_congr (equiv.refl _)).nonempty_congr, function.embedding.nonempty_iff_card_le,
      fintype.card_fin, fintype.card_fin] },
  { simpa [card_infinite] using @function.embedding.is_empty α _ _ _, }
end

lemma card_le_one_iff : #ₑ α ≤ 1 ↔ subsingleton α :=
card_le_nat_iff.trans $
  ⟨λ ⟨f⟩, f.2.subsingleton, λ h, ⟨⟨λ _, 0, @function.injective_of_subsingleton _ _ h _⟩⟩⟩

lemma card_eq_one_iff : #ₑ α = 1 ↔ subsingleton α ∧ nonempty α :=
by rw [le_antisymm_iff, one_le_card_iff, card_le_one_iff]

variables (α β γ δ)

@[simp] lemma card_unique [unique α] : #ₑ α = 1 := card_eq_of_equiv_fin $ equiv.equiv_of_unique _ _

lemma card_of_subsingleton (a : α) [subsingleton α] : #ₑ α = 1 :=
@card_unique α $ unique_of_subsingleton a

lemma card_punit : #ₑpunit = 1 := card_unique _
lemma card_true : #ₑ true = 1 := card_unique _
lemma card_fintype [fintype γ] : #ₑγ = fintype.card γ := card_eq_of_equiv_fin $ fintype.equiv_fin _
@[simp] lemma card_plift : #ₑ(plift α) = #ₑα := card_congr equiv.plift
@[simp] lemma card_empty [is_empty α] : #ₑα = 0 := card_eq_zero_iff.2 ‹_›
lemma card_false : #ₑ false = 0 := card_empty _

@[simp] lemma card_prod : #ₑ (γ × δ) = #ₑ γ * #ₑ δ :=
begin
  casesI finite_or_infinite γ; [casesI finite_or_infinite δ, casesI is_empty_or_nonempty δ],
  { rw [card_finite γ, card_finite δ, ← enat.coe_mul, card_eq_nat_iff],
    exact (finite.nonempty_equiv_fin γ).map2 (λ e₁ e₂, (e₁.prod_congr e₂).trans fin_prod_fin_equiv)
      (finite.nonempty_equiv_fin δ) },
  { casesI is_empty_or_nonempty γ,
    { rw [card_empty, card_empty, zero_mul] },
    { rw [card_infinite, card_infinite δ, with_top.mul_top],
      exact (card_pos_iff.2 ‹_›).ne' } },
  { rw [card_empty, card_empty δ, mul_zero] },
  { rw [card_infinite, card_infinite, with_top.top_mul],
    exact (card_pos_iff.2 ‹_›).ne' }
end

@[simp] lemma card_pprod : #ₑ(pprod α β) = #ₑα * #ₑβ :=
by rw [card_congr equiv.pprod_equiv_prod_plift, card_prod, card_plift, card_plift]

@[simp] lemma card_sum : #ₑ(γ ⊕ δ) = #ₑγ + #ₑδ :=
begin
  casesI finite_or_infinite γ; [casesI finite_or_infinite δ, skip],
  { rw [card_finite γ, card_finite δ, ← with_top.coe_add, card_eq_nat_iff],
    exact (finite.nonempty_equiv_fin γ).map2 (λ e₁ e₂, (e₁.sum_congr e₂).trans fin_sum_fin_equiv)
      (finite.nonempty_equiv_fin δ) },
  all_goals { simp only [card_infinite, add_top, top_add] }
end

@[simp] lemma card_psum : #ₑ(psum α β) = #ₑα + #ₑβ :=
by rw [card_congr (equiv.plift.symm.psum_sum equiv.plift.symm), card_sum, card_plift, card_plift]

@[simp] lemma card_option : #ₑ (option γ) = #ₑ γ + 1 :=
by rw [card_congr (equiv.option_equiv_sum_punit γ), card_sum, card_punit]

end enat

namespace nat

variables {α β}

lemma card_congr (e : α ≃ β) : #ₙα = #ₙβ := congr_arg enat.to_nat (enat.card_congr e)
@[simp] lemma {u v} card_ulift (α : Type v) : #ₙ(ulift.{u} α) = #ₙα := card_congr equiv.ulift

lemma card_eq_of_equiv_fin {n} (e : α ≃ fin n) : #ₙα = n :=
by rw [nat.card, enat.card_eq_of_equiv_fin e, enat.to_nat_coe]

lemma card_eq_of_bijective (f : α → β) (hf : bijective f) : #ₙ α = #ₙ β :=
card_congr (equiv.of_bijective f hf)

variables (α β γ δ)

@[simp] lemma card_plift : #ₙ(plift α) = #ₙα := card_congr equiv.plift
@[simp] lemma card_infinite [infinite α] : #ₙα = 0 := by simp [nat.card]

lemma _root_.finite.of_card_ne_zero (h : nat.card α ≠ 0) : finite α :=
finite.of_not_infinite $ h ∘ @nat.card_infinite α

@[simp] lemma card_fintype [fintype γ] : #ₙγ = fintype.card γ :=
card_eq_of_equiv_fin $ fintype.equiv_fin _

lemma card_fin (n : ℕ) : #ₙ(fin n) = n := card_eq_of_equiv_fin (equiv.refl _)

@[simp] lemma card_unique [unique α] : #ₙ α = 1 := card_eq_of_equiv_fin $ equiv.equiv_of_unique _ _

lemma card_of_subsingleton (a : α) [subsingleton α] : #ₙ α = 1 :=
@card_unique α $ unique_of_subsingleton a

lemma card_punit : #ₙ punit = 1 := card_unique _
lemma card_true : #ₙ true = 1 := card_unique _
@[simp] lemma card_empty [is_empty α] : #ₙ α = 0 := by rw [nat.card, enat.card_empty, map_zero]
lemma card_false : #ₙ false = 0 := card_empty _

@[simp] lemma card_prod : #ₙ(γ × δ) = #ₙγ * #ₙδ :=
by simp only [nat.card, enat.card_prod, map_mul]

@[simp] lemma card_pprod : #ₙ(pprod α β) = #ₙα * #ₙβ :=
by simp only [nat.card, enat.card_pprod, map_mul]

@[simp] lemma card_sum [finite γ] [finite δ] : #ₙ(γ ⊕ δ) = #ₙγ + #ₙδ :=
by simp only [nat.card, enat.card_sum, enat.to_nat_add (enat.card_ne_top γ) (enat.card_ne_top δ)]

@[simp] lemma card_psum [finite α] [finite β] : #ₙ(psum α β) = #ₙα + #ₙβ :=
by simp only [nat.card, enat.card_psum, enat.to_nat_add (enat.card_ne_top α) (enat.card_ne_top β)]

lemma card_eq_one_iff : #ₙ α = 1 ↔ subsingleton α ∧ nonempty α :=
by rw [← enat.card_eq_one_iff, nat.card, enat.to_nat_eq_iff one_ne_zero, coe_one]

end nat
