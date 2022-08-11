/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.pi.lex
import data.finsupp.basic

/-!
# Lexicographic order on finsupps

This file defines the lexicographic order on finsupps.
-/

namespace finsupp

variables {α N : Type*} [has_zero N]

open_locale classical

lemma filter_ne_eq_empty_iff {f g : α →₀ N} :
  (f.support ∪ g.support).filter (λ a, f a ≠ g a) = ∅ ↔ f = g :=
begin
  refine ⟨λ h, _, λ h, h ▸ by simp⟩,
  ext a,
  contrapose h,
  refine finset.ne_empty_of_mem (_ : a ∈ _),
  simp only [ne.def, finset.mem_filter, finset.mem_union, finsupp.mem_support_iff],
  exact ⟨not_and_distrib.1 $ mt (and_imp.2 eq.substr) (ne.symm h), h⟩,
end

variables [linear_order α]

/--  The partial order on `finsupp`s obtained by the lexicographic ordering.
`finsupp.lex` is the proof that this partial order is in fact linear. -/
def lex.partial_order [partial_order N] : partial_order (lex (α →₀ N)) :=
partial_order.lift _ (@id (function.injective (_ : lex (α →₀ N) → lex (α → N)))
  finsupp.coe_fn_injective)

local attribute [instance] lex.partial_order

/--  The linear order on `finsupp`s obtained by the lexicographic ordering. -/
noncomputable def lex [linear_order N] :
  linear_order (lex (α →₀ N)) :=
{ le_total := λ f g, begin
    let dfug : finset α := (f.support ∪ g.support).filter (λ a, of_lex f a ≠ of_lex g a),
    cases dfug.eq_empty_or_nonempty,
    { exact or.inl (finsupp.filter_ne_eq_empty_iff.mp h).le },
    { cases le_or_lt (of_lex f (dfug.min' h)) (of_lex g (dfug.min' h)) with mf mg,
      { refine or.inl (or.inr _),
        rcases finset.mem_filter.mp (finset.min'_mem _ h) with ⟨-, h⟩,
        refine ⟨_, λ j hj, _, lt_of_le_of_ne mf h⟩, clear h,
        by_cases js : j ∈ f.support ∪ g.support,
        { contrapose! hj,
          exact finset.min'_le _ _ (finset.mem_filter.mpr ⟨js, hj⟩) },
        { simp only [finset.mem_union, not_or_distrib, finsupp.mem_support_iff, not_not] at js,
          simp only [js] } },
      { refine or.inr (or.inr ⟨_, λ j hj, _, mg⟩),
        by_cases js : j ∈ f.support ∪ g.support,
        { contrapose! hj,
          exact finset.min'_le _ _ (finset.mem_filter.mpr ⟨js, hj.symm⟩) },
        { simp only [finset.mem_union, not_or_distrib, finsupp.mem_support_iff, not_not] at js,
          simp only [js] } } }
    end,
  decidable_le := by apply_instance,
  ..lex.partial_order }

end finsupp
