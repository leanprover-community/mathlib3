/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import model_theory.satisfiability

/-!
# Quantifier Elimination
This file deals with quantifier elimination in first-order theories.

## Main Definitions
* 

## Main Results

## Implementation Details
* `first_order.language.Theory.has_qe` 

-/

universes u v w
open_locale first_order

namespace first_order
namespace language
namespace Theory

variables {L : language.{u v}} {α β : Type*} {m n : ℕ} (T : L.Theory)

/-- A theory eliminates quantifiers if every formula is equivalent over that theory to a 
  quantifier-free formula. -/
def has_qe : Prop :=
∀ {n : ℕ} (φ : L.bounded_formula empty n), ∃ (ψ : L.bounded_formula empty n),
  ψ.is_qf ∧ T.semantically_equivalent φ ψ

theorem has_qe_iff_elim_exists :
  T.has_qe ↔ ∀ {n} (φ : L.bounded_formula empty (n + 1)) (h : φ.is_qf),
    ∃ (ψ : L.bounded_formula empty n), ψ.is_qf ∧ T.semantically_equivalent φ.ex ψ :=
begin
  refine ⟨λ h _ φ _, h φ.ex, λ h _ φ, φ.induction_on_exists_not (λ m ψ hψ, ⟨ψ, hψ, refl _⟩) _ _ _⟩,
  { rintros m φ ⟨ψ, hψ, φψ⟩,
    exact ⟨ψ.not, hψ.not, φψ.not⟩ },
  { rintros m φ ⟨ψ, hψ, φψ⟩,
    obtain ⟨θ, hθ, ψθ⟩ := h ψ hψ,
    exact ⟨θ, hθ, φψ.ex.trans ψθ⟩ },
  { rintros m φ ψ φψ,
    split,
    { rintro ⟨θ, hθ, φθ⟩,
      exact ⟨θ, hθ, (φψ.mono T.empty_subset).symm.trans φθ⟩ },
    { rintro ⟨θ, hθ, ψθ⟩,
      exact ⟨θ, hθ, (φψ.mono T.empty_subset).trans ψθ⟩ } }
end

theorem has_qe.exists_qf_equiv (h : T.has_qe) (φ : L.bounded_formula α n) :
  ∃ (ψ : L.bounded_formula α n), ψ.is_qf ∧ T.semantically_equivalent φ ψ :=
begin
  classical,
  obtain ⟨ψ, hψ, φψ⟩ := h ((φ.restrict_free_var id).relabel (sum.inr ∘ (fintype.equiv_fin _))),
  refine ⟨bounded_formula.relabel
    ((sum.map (coe ∘ (fintype.equiv_fin _).symm) id) ∘ (sum.elim empty.elim fin_sum_fin_equiv.symm))
    ψ.to_formula, hψ.to_formula.relabel _, λ M v xs, _⟩,
  have φψ' := φψ M default (sum.elim v xs ∘ ((sum.map (coe ∘ (fintype.equiv_fin _).symm) id) ∘
    fin_sum_fin_equiv.symm)),
  simp only [bounded_formula.realize_iff, bounded_formula.realize_relabel, iff_eq_eq] at *,
  rw [← realize_restrict_free_var (set.subset.refl _), set.inclusion_eq_id],
  rw [unique.eq_default (xs ∘ (fin.nat_add n : fin 0 → fin n)),
      ← formula.realize, realize_to_formula],
  refine (congr (congr rfl _) _).trans
    (φψ'.trans (congr (congr rfl (unique.eq_default _).symm) _)),
  { ext i,
      simp only [free_var_finset, function.comp_app, sum.elim_inr,
        fin_sum_fin_equiv_symm_apply_cast_add, sum.map_inl,
        _root_.equiv.symm_apply_apply, sum.elim_inl, eq_self_iff_true], },
  { ext i,
    simp only [function.comp_app, fin_sum_fin_equiv_symm_apply_nat_add, sum.map_inr,
      id.def, sum.elim_inr], },
  { ext i,
    simp only [function.comp_app, fin.cast_add_zero, fin.cast_refl, order_iso.coe_refl,
      function.comp.right_id, sum.elim_inr], }
end

end Theory
end language
end first_order