import data.finset.basic
import combinatorics.simplicial_complex.to_move.set

variables {α : Type*}

namespace finset

-- currently being added to mathlib
lemma strong_downward_induction_on {α : Type*} {p : finset α → Prop} {n : ℕ}
  (h : ∀ {t₁}, (∀ {t₂ : finset α}, t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → p t₁) {s : finset α} :
  s.card ≤ n → p s :=
begin
  apply well_founded.induction (measure_wf (λ (t : finset α), n - t.card)) s,
  exact (λ x ih hx, h (λ z hz xz, ih _ ((nat.sub_lt_sub_left_iff hz).2 (finset.card_lt_card xz)) hz)),
end

lemma strong_downward_induction_on' {α : Type*} {p : finset α → Prop} {A : set (finset α)}
  {n : ℕ} (hA : ∀ {t : finset α}, t ∈ A → t.card ≤ n) {s : finset α} (hs : s ∈ A)
  (h : ∀ {t₁}, t₁ ∈ A → (∀ {t₂}, t₂ ∈ A → t₁ ⊂ t₂ → p t₂) → p t₁) :
  p s :=
@strong_downward_induction_on _ (λ t₁, t₁ ∈ A → p t₁) n (λ t₁ ih ht₁, h ht₁ (λ Z hZ₁ hZ₂,
  ih (hA hZ₁) hZ₂ hZ₁)) s (hA hs) hs

end finset
