/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import model_theory.satisfiability

/-!
# Type Spaces
This file defines the space of complete types over a first-order theory.
(Note that types in model theory are different from types in type theory.)

## Main Definitions
* `first_order.language.Theory.complete_type`:
  `T.complete_type α` consists of complete types over the theory `T` with variables `α`.
* `first_order.language.Theory.type_of` is the type of a given tuple.
* `first_order.language.Theory.realized_types`: `T.realized_types M α` is the set of
  types in `T.complete_type α` that are realized in `M` - that is, the type of some tuple in `M`.

## Main Results
* `first_order.language.Theory.complete_type.nonempty_iff`:
  The space `T.complete_type α` is nonempty exactly when `T` is satisfiable.
* `first_order.language.Theory.complete_type.exists_Model_is_realized_in`: Every type is realized in
some model.

## Implementation Notes
* Complete types are implemented as maximal consistent theories in an expanded language.
More frequently they are described as maximal consistent sets of formulas, but this is equivalent.

## TODO
* Connect `T.complete_type α` to sets of formulas `L.formula α`.

-/

universes u v w w'

open cardinal set
open_locale cardinal first_order classical

namespace first_order
namespace language
namespace Theory

variables {L : language.{u v}} (T : L.Theory) (α : Type w)

/-- A complete type over a given theory in a certain type of variables is a maximally
  consistent (with the theory) set of formulas in that type. -/
structure complete_type :=
(to_Theory : L[[α]].Theory)
(subset' : (L.Lhom_with_constants α).on_Theory T ⊆ to_Theory)
(is_maximal' : to_Theory.is_maximal)

variables {T α}

namespace complete_type

instance : set_like (T.complete_type α) (L[[α]].sentence) :=
⟨λ p, p.to_Theory, λ p q h, begin
  cases p,
  cases q,
  congr',
end⟩

lemma is_maximal (p : T.complete_type α) : is_maximal (p : L[[α]].Theory) :=
p.is_maximal'

lemma subset (p : T.complete_type α) :
  (L.Lhom_with_constants α).on_Theory T ⊆ (p : L[[α]].Theory) :=
p.subset'

lemma mem_or_not_mem (p : T.complete_type α) (φ : L[[α]].sentence) : φ ∈ p ∨ φ.not ∈ p :=
p.is_maximal.mem_or_not_mem φ

lemma mem_of_models (p : T.complete_type α) {φ : L[[α]].sentence}
  (h : (L.Lhom_with_constants α).on_Theory T ⊨ φ) :
  φ ∈ p :=
(p.mem_or_not_mem φ).resolve_right (λ con, ((models_iff_not_satisfiable _).1 h)
  (p.is_maximal.1.mono (union_subset p.subset (singleton_subset_iff.2 con))))

lemma not_mem_iff (p : T.complete_type α) (φ : L[[α]].sentence) :
  φ.not ∈ p ↔ ¬ φ ∈ p :=
⟨λ hf ht, begin
  have h : ¬ is_satisfiable ({φ, φ.not} : L[[α]].Theory),
  { rintro ⟨@⟨_, _, h, _⟩⟩,
    simp only [model_iff, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
      forall_eq] at h,
    exact h.2 h.1 },
  refine h (p.is_maximal.1.mono _),
  rw [insert_subset, singleton_subset_iff],
  exact ⟨ht, hf⟩,
end, (p.mem_or_not_mem φ).resolve_left⟩

@[simp] lemma compl_set_of_mem {φ : L[[α]].sentence} :
  {p : T.complete_type α | φ ∈ p}ᶜ = {p : T.complete_type α | φ.not ∈ p} :=
ext (λ _, (not_mem_iff _ _).symm)

lemma set_of_subset_eq_empty_iff (S : L[[α]].Theory) :
  {p : T.complete_type α | S ⊆ ↑p} = ∅ ↔
    ¬ ((L.Lhom_with_constants α).on_Theory T ∪ S).is_satisfiable :=
begin
  rw [iff_not_comm, ← not_nonempty_iff_eq_empty, not_not, set.nonempty],
  refine ⟨λ h, ⟨⟨L[[α]].complete_theory h.some, (subset_union_left _ S).trans
    complete_theory.subset, complete_theory.is_maximal _ _⟩, (subset_union_right
      ((L.Lhom_with_constants α).on_Theory T) _).trans complete_theory.subset⟩, _⟩,
  rintro ⟨p, hp⟩,
  exact p.is_maximal.1.mono (union_subset p.subset hp),
end

lemma set_of_mem_eq_univ_iff (φ : L[[α]].sentence) :
  {p : T.complete_type α | φ ∈ p} = univ ↔ (L.Lhom_with_constants α).on_Theory T ⊨ φ :=
begin
  rw [models_iff_not_satisfiable, ← compl_empty_iff, compl_set_of_mem,
    ← set_of_subset_eq_empty_iff],
  simp,
end

lemma set_of_subset_eq_univ_iff (S : L[[α]].Theory) :
  {p : T.complete_type α | S ⊆ ↑p} = univ ↔
    (∀ φ, φ ∈ S → (L.Lhom_with_constants α).on_Theory T ⊨ φ) :=
begin
  have h : {p : T.complete_type α | S ⊆ ↑p} = ⋂₀ ((λ φ, {p | φ ∈ p}) '' S),
  { ext,
    simp [subset_def] },
  simp_rw [h, sInter_eq_univ, ← set_of_mem_eq_univ_iff],
  refine ⟨λ h φ φS, h _ ⟨_, φS, rfl⟩, _⟩,
  rintro h _ ⟨φ, h1, rfl⟩,
  exact h _ h1,
end

lemma nonempty_iff : nonempty (T.complete_type α) ↔
  T.is_satisfiable :=
begin
  rw ← is_satisfiable_on_Theory_iff (Lhom_with_constants_injective L α),
  rw [nonempty_iff_univ_nonempty, nonempty_iff_ne_empty, ne.def, not_iff_comm,
    ← union_empty ((L.Lhom_with_constants α).on_Theory T), ← set_of_subset_eq_empty_iff],
  simp,
end

instance : nonempty (complete_type ∅ α) :=
nonempty_iff.2 (is_satisfiable_empty L)

lemma Inter_set_of_subset {ι : Type*} (S : ι → L[[α]].Theory) :
  (⋂ (i : ι), {p : T.complete_type α | S i ⊆ p}) = {p | (⋃ (i : ι), S i) ⊆ p} :=
begin
  ext,
  simp only [mem_Inter, mem_set_of_eq, Union_subset_iff],
end

lemma to_list_foldr_inf_mem {p : T.complete_type α} {t : finset (L[[α]]).sentence} :
  t.to_list.foldr (⊓) ⊤ ∈ p ↔ (t : L[[α]].Theory) ⊆ ↑p :=
begin
  simp_rw [subset_def, ← set_like.mem_coe, p.is_maximal.mem_iff_models, models_sentence_iff,
    sentence.realize, formula.realize, bounded_formula.realize_foldr_inf, finset.mem_to_list],
  exact ⟨λ h φ hφ M, h _ _ hφ, λ h M φ hφ, h _ hφ _⟩,
end

end complete_type

variables {M : Type w'} [L.Structure M] [nonempty M] [M ⊨ T] (T)

/-- The set of all formulas true at a tuple in a structure forms a complete type. -/
def type_of (v : α → M) : T.complete_type α :=
begin
  haveI : (constants_on α).Structure M := constants_on.Structure v,
  exact { to_Theory := L[[α]].complete_theory M,
    subset' := model_iff_subset_complete_theory.1 ((Lhom.on_Theory_model _ T).2 infer_instance),
    is_maximal' := complete_theory.is_maximal _ _ },
end

namespace complete_type

variables {T} {v : α → M}

@[simp] lemma mem_type_of {φ : L[[α]].sentence} :
  φ ∈ T.type_of v ↔ (formula.equiv_sentence.symm φ).realize v :=
begin
  letI : (constants_on α).Structure M := constants_on.Structure v,
  exact mem_complete_theory.trans (formula.realize_equiv_sentence_symm _ _ _).symm,
end

lemma formula_mem_type_of {φ : L.formula α} :
  formula.equiv_sentence φ ∈ T.type_of v ↔ φ.realize v :=
by simp

end complete_type

variable (M)

/-- A complete type `p` is realized in a particular structure when there is some
  tuple `v` whose type is `p`. -/
@[simp] def realized_types (α : Type w) : set (T.complete_type α) :=
set.range (T.type_of : (α → M) → T.complete_type α)

theorem exists_Model_is_realized_in (p : T.complete_type α) :
  ∃ (M : Theory.Model.{u v (max u v w)} T),
    p ∈ T.realized_types M α :=
begin
  obtain ⟨M⟩ := p.is_maximal.1,
  refine ⟨(M.subtheory_Model p.subset).reduct (L.Lhom_with_constants α), (λ a, (L.con a : M)), _⟩,
  refine set_like.ext (λ φ, _),
  simp only [complete_type.mem_type_of],
  refine (formula.realize_equiv_sentence_symm_con _ _).trans (trans (trans _
    (p.is_maximal.is_complete.realize_sentence_iff φ M)) (p.is_maximal.mem_iff_models φ).symm),
  refl,
end

end Theory
end language
end first_order
