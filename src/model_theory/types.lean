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

## Main Results
* `first_order.language.Theory.complete_type.nonempty_iff`:
  The space `T.complete_type α` is nonempty exactly when `T` is satisfiable.

## Implementation Notes
* Complete types are implemented as maximal consistent theories in an expanded language.
More frequently they are described as maximal consistent sets of formulas, but this is equivalent.

## TODO
* Connect `T.complete_type α` to sets of formulas `L.formula α`.

-/

universes u v w w'

open cardinal set
open_locale cardinal first_order classical

variables {L : first_order.language.{u v}} (T : L.Theory) (α : Type w)

namespace first_order
namespace language
namespace Theory

/-- A complete type over a given theory in a certain type of variables is a maximally
  consistent (with the theory) set of formulas in that type. -/
structure complete_type :=
(to_Theory : L[[α]].Theory)
(subset' : (L.Lhom_with_constants α).on_Theory T ⊆ to_Theory)
(is_maximal' : to_Theory.is_maximal)

variables {T α}

namespace complete_type

/-! ### In terms of `L[[α]].sentence` -/

instance : has_coe (T.complete_type α) (L[[α]].Theory) := ⟨to_Theory⟩

lemma coe_Theory_injective :
  function.injective (coe : T.complete_type α → L[[α]].Theory) :=
begin
  rintros ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨rfl, _, _⟩,
  refl,
end

lemma is_maximal (p : T.complete_type α) : is_maximal (p : L[[α]].Theory) :=
p.is_maximal'

lemma subset (p : T.complete_type α) :
  (L.Lhom_with_constants α).on_Theory T ⊆ (p : L[[α]].Theory) :=
p.subset'

@[simp] lemma compl_set_of_mem {φ : L[[α]].sentence} :
  {p : T.complete_type α | φ ∈ (p : L[[α]].Theory)}ᶜ =
    {p : T.complete_type α | φ.not ∈ (p : L[[α]].Theory)} :=
ext (λ p, (p.is_maximal.not_mem_iff φ).symm)

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
  {p : T.complete_type α | φ ∈ (p : L[[α]].Theory)} = univ ↔
    (L.Lhom_with_constants α).on_Theory T ⊨ φ :=
begin
  rw [models_iff_not_satisfiable, ← compl_empty_iff, compl_set_of_mem,
    ← set_of_subset_eq_empty_iff],
  simp only [singleton_subset_iff],
end

lemma set_of_subset_eq_univ_iff (S : L[[α]].Theory) :
  {p : T.complete_type α | S ⊆ ↑p} = univ ↔
    (∀ φ, φ ∈ S → (L.Lhom_with_constants α).on_Theory T ⊨ φ) :=
begin
  have h : {p : T.complete_type α | S ⊆ ↑p} = ⋂₀ ((λ φ, {p | φ ∈ (p : L[[α]].Theory)}) '' S),
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
  rw [nonempty_iff_univ_nonempty, ← ne_empty_iff_nonempty, ne.def, not_iff_comm,
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
  t.to_list.foldr (⊓) ⊤ ∈ (p : L[[α]].Theory) ↔ (t : L[[α]].Theory) ⊆ ↑p :=
begin
  simp_rw [subset_def, p.is_maximal.mem_iff_models, models_sentence_iff,
    sentence.realize, formula.realize, bounded_formula.realize_foldr_inf, finset.mem_to_list],
  exact ⟨λ h φ hφ M, h _ _ hφ, λ h M φ hφ, h _ hφ _⟩,
end

/-! ### In terms of `L.formula α` -/

instance : set_like (T.complete_type α) (L.formula α) :=
{ coe := λ p φ, formula.equiv_sentence φ ∈ (p : L[[α]].Theory),
  coe_injective' := λ p q h, coe_Theory_injective (set.ext (λ φ, begin
    have h' := function.funext_iff.1 h (formula.equiv_sentence.symm φ),
    simp only [_root_.equiv.apply_symm_apply, eq_iff_iff] at h',
    exact h',
  end)) }

lemma formula_mem_iff (φ : L.formula α) (p : T.complete_type α) :
  φ ∈ p ↔ formula.equiv_sentence φ ∈ (p : L[[α]].Theory) :=
iff.rfl

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

variables {T} {v : α → M}

@[simp] lemma formula_mem_type_of {φ : L.formula α} : φ ∈ T.type_of v ↔ φ.realize v :=
begin
  letI : (constants_on α).Structure M := constants_on.Structure v,
  exact mem_complete_theory.trans (formula.realize_equiv_sentence _ _),
end

namespace complete_type

/-- A complete type `p` is realized in a particular structure when there is some
  tuple `v` whose type is `p`. -/
def is_realized_in (p : T.complete_type α) (M : Type w') [L.Structure M] [nonempty M] [M ⊨ T] :
  Prop :=
∃ v : α → M, T.type_of v = p

theorem exists_Model_is_realized_in (p : T.complete_type α) :
  ∃ (M : Theory.Model.{u v (max u v w)} T), p.is_realized_in M :=
begin
  obtain ⟨M⟩ := p.is_maximal.1,
  refine ⟨(M.subtheory_Model p.subset).reduct (L.Lhom_with_constants α), (λ a, (L.con a : M)), _⟩,
  refine set_like.ext (λ φ : L.formula α, _),
  simp only [formula_mem_type_of],
  rw [← formula.realize_equiv_sentence, formula_mem_iff, p.is_maximal.mem_iff_models,
    ← p.is_maximal.is_complete.realize_sentence_iff (formula.equiv_sentence φ) M],
  refl,
end

end complete_type

end Theory
end language
end first_order
