/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.pi.lex
import data.finsupp.order

/-!
# Lexicographic order on finitely supported functions

This file defines the lexicographic order on `finsupp`.
-/

variables {α N : Type*}

namespace finsupp

lemma filter_ne_eq_empty_iff [decidable_eq α] [decidable_eq N] [has_zero N] {f g : α →₀ N} :
  (f.support ∪ g.support).filter (λ a, f a ≠ g a) = ∅ ↔ f = g :=
begin
  refine ⟨λ h, _, λ h, h ▸ by simp⟩,
  ext a,
  contrapose h,
  refine finset.ne_empty_of_mem (_ : a ∈ _),
  simp only [ne.def, finset.mem_filter, finset.mem_union, finsupp.mem_support_iff],
  exact ⟨not_and_distrib.1 $ mt (and_imp.2 eq.substr) (ne.symm h), h⟩,
end

section N_has_zero
variables [has_zero N]

/-- The lexicographic relation on `α →₀ N`, where `α` is ordered by `r`,
  and `N` is ordered by `s`. -/
protected def lex (r : α → α → Prop) (s : N → N → Prop) (x y : α →₀ N) : Prop :=
pi.lex r (λ _, s) x y

instance [has_lt α] [has_lt N] : has_lt (lex (α →₀ N)) := ⟨finsupp.lex (<) (<)⟩

instance lex.is_strict_order [linear_order α] [partial_order N] :
  is_strict_order (lex (α →₀ N)) (<) :=
let i : is_strict_order (lex (α → N)) (<) := pi.lex.is_strict_order in
{ irrefl := to_lex.surjective.forall.2 $ λ a, @irrefl _ _ i.to_is_irrefl a,
  trans := to_lex.surjective.forall₃.2 $ λ a b c, @trans _ _ i.to_is_trans a b c }

variables [linear_order α]

/--  The partial order on `finsupp`s obtained by the lexicographic ordering.
`finsupp.lex.linear_order` is the proof that this partial order is in fact linear. -/
instance lex.partial_order [partial_order N] : partial_order (lex (α →₀ N)) :=
partial_order.lift (λ x, to_lex ⇑(of_lex x)) finsupp.coe_fn_injective--fun_like.coe_injective

variable [linear_order N]
/--  The linear order on `finsupp`s obtained by the lexicographic ordering. -/
noncomputable instance lex.linear_order : linear_order (lex (α →₀ N)) :=
{ le_total := to_lex.surjective.forall₂.2 $ λ f g, begin
    let dfug : finset α := (f.support ∪ g.support).filter (λ a, of_lex f a ≠ of_lex g a),
    cases dfug.eq_empty_or_nonempty,
    { exact or.inl (finsupp.filter_ne_eq_empty_iff.mp h).le },
    cases le_or_lt (of_lex f (dfug.min' h)) (of_lex g (dfug.min' h)) with mf mg,
    work_on_goal 1 { refine or.inl (or.inr _),
      rcases finset.mem_filter.mp (finset.min'_mem _ h) with ⟨-, h⟩,
      refine ⟨_, λ j hj, _, mf.lt_of_ne h⟩ },
    work_on_goal 2 { refine or.inr (or.inr ⟨_, λ j hj, eq.symm _, mg⟩) },
    all_goals { by_cases js : j ∈ f.support ∪ g.support,
      { contrapose! hj,
        exact finset.min'_le _ _ (finset.mem_filter.mpr ⟨js, hj⟩) },
      { simp only [finset.mem_union, not_or_distrib, finsupp.mem_support_iff, not_not] at js,
        simp only [js, of_lex_to_lex, pi.to_lex_apply] } },
    end,
  decidable_le := by { classical, apply_instance },
  ..lex.partial_order }

lemma lex.le_of_forall_le {a b : lex (α →₀ N)} (h : ∀ i, of_lex a i ≤ of_lex b i) : a ≤ b :=
le_of_not_lt (λ ⟨i, hi⟩, (h i).not_lt hi.2)

lemma lex.le_of_of_lex_le {a b : lex (α →₀ N)} (h : of_lex a ≤ of_lex b) : a ≤ b :=
lex.le_of_forall_le h

lemma to_lex_monotone : monotone (@to_lex (α →₀ N)) :=
λ _ _, lex.le_of_forall_le

end N_has_zero

end finsupp
