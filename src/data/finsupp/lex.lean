/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.pi.lex
import data.finsupp.basic

/-!
# Lexicographic order on finitely supported functions

This file defines the lexicographic order on `finsupp`.
-/

lemma ne.or_ne_of_ne {α} {a b : α} (c : α) (ab : a ≠ b) :
  a ≠ c ∨ b ≠ c :=
@dite _ (a = c) (classical.prop_decidable (a = c))
  (λ ac, or.inr (ne_of_ne_of_eq ab.symm ac)) (λ ac, or.inl ac)

namespace finsupp

variables {α N : Type*} [has_zero N]

open_locale classical

lemma filter_ne_eq_empty_iff {f g : α →₀ N} :
  (f.support ∪ g.support).filter (λ a, f a ≠ g a) = ∅ ↔ f = g :=
begin
  refine ⟨λ de, _, λ fg, _⟩,
  { ext a,
    refine not_ne_iff.mp (λ h, not_ne_iff.mpr de _),
    refine finset.ne_empty_of_mem (_ : a ∈ _),
    simp only [ne.def, finset.mem_filter, finset.mem_union, finsupp.mem_support_iff],
    exact ⟨h.or_ne_of_ne _, h⟩ },
  { subst fg,
    simp only [ne.def, eq_self_iff_true, not_true, finset.filter_false] }
end

variables [linear_order α]

/--  The partial order on `finsupp`s obtained by the lexicographic ordering.
`finsupp.lex` is the proof that this partial order is in fact linear. -/
def _root_.finsupp_partial_order [partial_order N] : partial_order (lex (α →₀ N)) :=
partial_order.lift _ (@id (function.injective (_ : lex (α →₀ N) → lex (α → N)))
  finsupp.coe_fn_injective)

local attribute [instance] finsupp_partial_order

/--  The linear order on `finsupp`s obtained by the lexicographic ordering. -/
noncomputable def lex [linear_order N] :
  linear_order (lex (α →₀ N)) :=
{ le_total := λ f g, begin
  let dfug : finset α := (f.support ∪ g.support).filter (λ a, of_lex f a ≠ of_lex g a),
  by_cases de : dfug = ∅,
  { exact or.inl (finsupp.filter_ne_eq_empty_iff.mp de).le },
  { rw [← ne.def, ← finset.nonempty_iff_ne_empty] at de,
    cases le_or_lt (of_lex f (dfug.min' de)) (of_lex g (dfug.min' de)) with mf mf,
    { refine or.inl (or.inr _),
      rcases finset.mem_filter.mp (finset.min'_mem _ de) with ⟨-, h⟩,
      refine ⟨_, λ j hj, _, lt_of_le_of_ne mf h⟩, clear h,
      by_cases js : j ∈ f.support ∪ g.support,
      { contrapose! hj,
        exact finset.min'_le _ _ (finset.mem_filter.mpr ⟨js, hj⟩) },
      { simp only [finset.mem_union, not_or_distrib, finsupp.mem_support_iff, not_not] at js,
        simp only [js] } },
    { refine or.inr (or.inr ⟨_, λ j hj, _, not_le.mp mf⟩),
      by_cases js : j ∈ f.support ∪ g.support,
      { contrapose! hj,
        exact finset.min'_le _ _ (finset.mem_filter.mpr ⟨js, hj.symm⟩) },
      { simp only [finset.mem_union, not_or_distrib, finsupp.mem_support_iff, not_not] at js,
        simp only [js] } } }
    end,
  decidable_le := infer_instance,
  ..lex.partial_order }

end finsupp
