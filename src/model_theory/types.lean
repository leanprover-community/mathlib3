/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import model_theory.satisfiability
import topology.separation
import topology.metric_space.baire

/-!
# Type Spaces
This file defines the space of complete types over a first-order theory.
(Note that types in model theory are different from types in type theory.)

## Main Definitions
* `first_order.language.Theory.complete_type`:
  `T.complete_type α` consists of complete types over the theory `T` with variables `α`.
* `first_order.language.Theory.type_of` is the type of a given tuple.
* `first_order.language.Theory.complete_type.is_realized_in` indicates when a type is realized -
that is, the type of some tuple over a particular model.

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

open cardinal set topological_space
open_locale cardinal first_order classical

namespace first_order
namespace language
namespace Theory

variables {L : language.{u v}} (T : L.Theory) (α : Type w)

-- move
lemma models_inf_iff {n : ℕ} {φ ψ : L.bounded_formula α n} :
  T ⊨ φ ⊓ ψ ↔ T ⊨ φ ∧ T ⊨ ψ :=
by simp_rw [models_bounded_formula, ← forall_and_distrib, bounded_formula.realize_inf]

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

lemma mem_iff_coe_models (p : T.complete_type α) {φ : L[[α]].sentence} :
  φ ∈ p ↔ (p : L[[α]].Theory) ⊨ φ :=
p.is_maximal.mem_iff_models φ

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
  (formula.equiv_sentence φ) ∈ T.type_of v ↔ φ.realize v :=
by simp

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
  refine set_like.ext (λ φ, _),
  simp only [mem_type_of],
  refine (formula.realize_equiv_sentence_symm_con _ _).trans (trans (trans _
    (p.is_maximal.is_complete.realize_sentence_iff φ M)) (p.is_maximal.mem_iff_models φ).symm),
  refl,
end

/-! ### Topology -/

instance : topological_space (T.complete_type α) :=
topological_space.generate_from {s | ∃ (φ : L[[α]].sentence),
  {p : T.complete_type α | φ ∈ (p : L[[α]].Theory)} = s}

theorem sentence_basis :
  is_topological_basis {s : set (T.complete_type α) | ∃ (φ : L[[α]].sentence),
    {p : T.complete_type α | φ ∈ p} = s} :=
{ exists_subset_inter := begin
    rintro _ ⟨φ, rfl⟩ _ ⟨ψ, rfl⟩ p ⟨φp, ψp⟩,
    refine ⟨{ q | φ ∈ _ } ∩ { q | ψ ∈ _ }, ⟨φ ⊓ ψ, _⟩, ⟨φp, ψp⟩, refl _⟩,
    ext q,
    simp only [q.mem_iff_coe_models, mem_set_of_eq, mem_inter_iff, models_inf_iff]
  end,
  sUnion_eq := begin
    ext p,
    simp only [mem_sUnion, mem_set_of_eq, exists_prop, mem_univ, iff_true],
    refine ⟨_, ⟨⊤, rfl⟩, _⟩,
    simp only [mem_set_of_eq],
    refine p.is_maximal.mem_of_models (λ _ _ _, _),
    simp only [bounded_formula.realize_top],
  end,
  eq_generate_from := rfl, }

lemma is_clopen_set_of_mem (φ : L[[α]].sentence) :
  is_clopen {p : T.complete_type α | φ ∈ p} :=
begin
  rw [is_clopen, ← is_open_compl_iff, compl_set_of_mem],
  exact ⟨sentence_basis.is_open ⟨φ, rfl⟩, sentence_basis.is_open ⟨φ.not, rfl⟩⟩,
end

lemma is_closed_iff_exists_theory {s : set (T.complete_type α)} :
  is_closed s ↔ ∃ (S : L[[α]].Theory), {p | S ⊆ ↑p} = s :=
begin
  split,
  { intro h,
    rw [← is_open_compl_iff] at h,
    obtain ⟨_, h1, h2⟩ := sentence_basis.open_eq_sUnion h,
    obtain ⟨S, rfl⟩ := subset_range_iff_exists_image_eq.1 h1,
    rw [compl_eq_comm] at h2,
    refine ⟨formula.not '' S, trans _ h2⟩,
    ext,
    simp only [mem_set_of_eq, sUnion_image, compl_Union, compl_set_of_mem,
      mem_Inter, subset_def, mem_image, set_like.mem_coe, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] },
  { rintro ⟨S, rfl⟩,
    have h : {p : T.complete_type α | S ⊆ ↑p} = ⋂₀ ((λ φ, {p : T.complete_type α | φ ∈ p}) '' S),
    { ext p,
      simp [subset_def] },
    rw h,
    refine is_closed_sInter _,
    rintros _ ⟨φ, hφ, rfl⟩,
    exact (is_clopen_set_of_mem φ).is_closed }
end

lemma is_clopen_iff_exists_sentence {s : set (T.complete_type α)} :
  is_clopen s ↔ ∃ φ : L[[α]].sentence, {p | φ ∈ p} = s :=
⟨begin
  rw [is_clopen, ← is_closed_compl_iff, is_closed_iff_exists_theory, is_closed_iff_exists_theory],
  rintro ⟨⟨SF, h⟩, ⟨ST, rfl⟩⟩,
  have hd := (eq_compl_iff_is_compl.1 h).disjoint,
  simp only [ext_iff, mem_set_of_eq, mem_compl_iff] at h,
  simp_rw [disjoint_iff_inter_eq_empty, ← set_of_and, ← union_subset_iff,
    set_of_subset_eq_empty_iff, is_satisfiable_iff_is_finitely_satisfiable,
    is_finitely_satisfiable, not_forall] at hd,
  obtain ⟨t, h1, h2⟩ := hd,
  refine ⟨(t.filter (λ φ, φ ∈ ST)).to_list.foldr (⊓) ⊤, _⟩,
  ext p,
  simp only [mem_set_of_eq, to_list_foldr_inf_mem, finset.coe_filter, sep_mem_eq],
  refine ⟨λ h', _, (inter_subset_right _ _).trans⟩,
  contrapose! h2,
  rw ← h at h2,
  exact p.is_maximal.1.mono (λ φ hφ, (h1 hφ).elim (λ h, p.subset h)
    (λ h, h.elim (λ h, h2 h) (λ h, h' ⟨hφ, h⟩))),
end, by { rintro ⟨φ, rfl⟩, exact is_clopen_set_of_mem φ }⟩

instance : t2_space (T.complete_type α) :=
begin
  refine ⟨λ p q pq, _⟩,
  rw [ne.def, set_like.ext_iff, not_forall] at pq,
  obtain ⟨φ, hφ⟩ := pq,
  rw [not_iff, iff_iff_and_or_not_and_not, not_not] at hφ,
  obtain (⟨hp, hq⟩ | ⟨hp, hq⟩) := hφ,
  { refine ⟨_, _, sentence_basis.is_open ⟨φ.not, rfl⟩, sentence_basis.is_open ⟨φ, rfl⟩,
      (p.mem_or_not_mem φ).resolve_left hp, hq,
      set.disjoint_iff.2 (λ x h, (x.not_mem_iff φ).1 h.1 h.2)⟩ },
  { refine ⟨_, _, sentence_basis.is_open ⟨φ, rfl⟩, sentence_basis.is_open ⟨φ.not, rfl⟩,
      hp, (q.mem_or_not_mem φ).resolve_left hq,
      set.disjoint_iff.2 (λ x h, (x.not_mem_iff φ).1 h.2 h.1)⟩ }
end

instance : totally_separated_space (T.complete_type α) :=
begin
  refine totally_separated_space_of_t1_of_basis_clopen _,
  simp_rw [is_clopen_iff_exists_sentence],
  exact sentence_basis,
end

instance : compact_space (T.complete_type α) :=
begin
  casesI is_empty_or_nonempty (T.complete_type α) with he hn,
  { exact finite.compact_space },
  rw nonempty_iff at hn,
  rw [← is_compact_univ_iff, is_compact_iff_finite_subfamily_closed],
  by_contra con,
  simp only [univ_inter, not_forall, not_exists, exists_prop] at con,
  obtain ⟨ι, C, hC1, hC2, hC3⟩ := con,
  obtain ⟨T' : ι → L[[α]].Theory, hT'⟩ := @classical.axiom_of_choice _ _ (λ i j, {p | j ⊆ ↑p} = C i)
    (λ (i : ι), is_closed_iff_exists_theory.1 (hC1 i)),
  simp only [← function.funext_iff] at hT',
  subst hT',
  rw [Inter_set_of_subset, set_of_subset_eq_empty_iff] at hC2,
  refine hC2 _,
  casesI is_empty_or_nonempty ι with h _,
  { rw [Union_eq_empty.2 h.elim, union_empty,
      is_satisfiable_on_Theory_iff (Lhom_with_constants_injective L α)],
    exact hn, },
  rw [union_Union, is_satisfiable_Union_iff_is_satisfiable_Union_finset],
  intros s,
  casesI is_empty_or_nonempty (↑s : set ι) with h _,
  { rw [is_empty_coe_sort, finset.coe_eq_empty] at h,
    simp only [h, Union_false, Union_empty],
    exact is_satisfiable_empty _, },
  simp_rw [← finset.mem_coe, bUnion_eq_Union, ← union_Union],
  have hs := hC3 s,
  simp_rw [← finset.mem_coe, bInter_eq_Inter, Inter_set_of_subset,
    set_of_subset_eq_empty_iff, not_not] at hs,
  exact hs,
end

def variable_projection {β : Type*} (f : α → β) (p : T.complete_type β) : T.complete_type α :=
begin
  refine ⟨{ φ : L[[α]].sentence | (Lhom_with_constants_map L f).on_sentence φ ∈ p }, _, _, _⟩,
  {

  },
end

section omitting_types

variable [countable L.symbols]

lemma models_residual :
  { p : T.complete_type ℕ | ∃ (M : T.Model) (f : ℕ ≃ M), p = T.type_of f }
  ∈ residual (T.complete_type ℕ) :=
begin
  sorry
end

theorem omitting_types {n : ℕ} (X : set (T.complete_type (fin n))) :
  (∃ (M : T.Model), countable M ∧
    X = set.range (T.type_of : (fin n → M) → (T.complete_type (fin n)))) ↔
  X ∈ residual (T.complete_type (fin n)) :=
begin
  split,
  { rintro ⟨M, h, rfl⟩,

    sorry,

  },
  { intro h,
    have h' : { p : T.complete_type ℕ | ¬ ∃ (f : fin n → ℕ),   }

  }
end

end omitting_types

end complete_type
end Theory
end language
end first_order
