/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent.
-/

import computability.encoding
import computability.tm_computable

namespace computability

private def fsum_setoid {α β : Type*} (a : α) (b : β) : setoid (α ⊕ β) := {
  r := λ u v, sum.cases_on u
    (λ x, sum.cases_on v
      (λ y, x = y)
      (λ y, (x = a) ∧ (y = b)))
    (λ x, sum.cases_on v
      (λ y, (x = b) ∧ (y = a))
      (λ y, x = y)),
  iseqv := by tidy }

instance fsum_setoid.decidable_rel {α β : Type*} (a : α) (b : β) [dα : decidable_eq α] [dβ : decidable_eq β]:
decidable_rel (fsum_setoid a b).r := begin
  intros x y,
  cases x; cases y,
  exact dα x y,
  exact and.decidable,
  exact and.decidable,
  exact dβ x y,
end

def fsum {α β : Type*} (a : α) (b : β) : Type* := quotient (fsum_setoid a b)

def fsum.inl {α β : Type*} {a : α} {b : β} (x : α) : fsum a b := quotient.mk' (sum.inl x)
def fsum.inr {α β : Type*} {a : α} {b : β} (y : β) : fsum a b := quotient.mk' (sum.inr y)

def fsum.elim {α β γ : Type*} {a : α} {b : β} (f : α → γ) (g : β → γ) (h : f a = g b): fsum a b → γ := λ x,
begin
  apply quot.lift_on x (sum.elim f g) (λ u v h',
  begin
    cases u; cases v,
    {
      exact congr_arg (sum.elim f g) (congr_arg sum.inl h'),
    }, {
      suffices h'' : (u = a) ∧ (v = b),
      simp only [h, h'', sum.elim_inl, sum.elim_inr],
      exact h',
    }, {
      suffices h'' : (u = b) ∧ (v = a),
      simp only [h, h'', sum.elim_inl, sum.elim_inr],
      exact h',
    }, {
      exact congr_arg (sum.elim f g) (congr_arg sum.inr h'),
    }
  end),
end

instance fsum.inhabited {α β : Type*} (a : α) (b : β): inhabited (fsum a b) := ⟨fsum.inl a⟩
instance fsum.decidable_eq {α β : Type*} [dα : decidable_eq α] [dβ : decidable_eq β] (a : α) (b : β): decidable_eq (fsum a b) :=
@quotient.decidable_eq (α ⊕ β) (fsum_setoid a b) (fsum_setoid.decidable_rel a b)
instance fsum.fintype {α β : Type*} (a : α) (b : β) [hα : fintype α] [hβ : fintype β]
[hα' : decidable_eq α] [hβ' : decidable_eq β]: fintype (fsum a b) :=
@quotient.fintype _ (sum.fintype α β) (fsum_setoid a b) (fsum_setoid.decidable_rel a b)

noncomputable



def fin_tm_comp (tm₂ tm₁ : fin_tm2) (hΓ : tm₂.Γ tm₂.k₀ = tm₁.Γ tm₁.k₁) : fin_tm2 := {
  K := fsum tm₂.k₀ tm₁.k₁,
  K_decidable_eq := @fsum.decidable_eq _ _ (tm₂.K_decidable_eq) (tm₁.K_decidable_eq) _ _,
  k₀ := fsum.inr tm₁.k₀,
  k₁ := fsum.inl tm₂.k₁,
  Γ := fsum.elim tm₂.Γ tm₁.Γ hΓ,
  Λ := tm₂.Λ ⊕ tm₁.Λ,
  main := sum.inr tm₁.main,
  σ := fsum tm₂.initial_state tm₁.initial_state,
  initial_state := fsum.inr tm₁.initial_state,
  σ_fin := @fsum.fintype _ _ _ _ tm₂.σ_fin tm₁.σ_fin (classical.dec_eq tm₂.σ) (classical.dec_eq tm₁.σ), -- Horror!
  Γk₀_fin := tm₁.Γk₀_fin,
  M := λ (l : tm₂.Λ ⊕ tm₁.Λ), sorry
}


end computability
