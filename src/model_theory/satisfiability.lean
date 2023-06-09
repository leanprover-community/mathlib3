/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import model_theory.ultraproducts
import model_theory.bundled
import model_theory.skolem

/-!
# First-Order Satisfiability

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
This file deals with the satisfiability of first-order theories, as well as equivalence over them.

## Main Definitions
* `first_order.language.Theory.is_satisfiable`: `T.is_satisfiable` indicates that `T` has a nonempty
model.
* `first_order.language.Theory.is_finitely_satisfiable`: `T.is_finitely_satisfiable` indicates that
every finite subset of `T` is satisfiable.
* `first_order.language.Theory.is_complete`: `T.is_complete` indicates that `T` is satisfiable and
models each sentence or its negation.
* `first_order.language.Theory.semantically_equivalent`: `T.semantically_equivalent φ ψ` indicates
that `φ` and `ψ` are equivalent formulas or sentences in models of `T`.
* `cardinal.categorical`: A theory is `κ`-categorical if all models of size `κ` are isomorphic.

## Main Results
* The Compactness Theorem, `first_order.language.Theory.is_satisfiable_iff_is_finitely_satisfiable`,
shows that a theory is satisfiable iff it is finitely satisfiable.
* `first_order.language.complete_theory.is_complete`: The complete theory of a structure is
complete.
* `first_order.language.Theory.exists_large_model_of_infinite_model` shows that any theory with an
infinite model has arbitrarily large models.
* `first_order.language.Theory.exists_elementary_embedding_card_eq`: The Upward Löwenheim–Skolem
Theorem: If `κ` is a cardinal greater than the cardinalities of `L` and an infinite `L`-structure
`M`, then `M` has an elementary extension of cardinality `κ`.

## Implementation Details
* Satisfiability of an `L.Theory` `T` is defined in the minimal universe containing all the symbols
of `L`. By Löwenheim-Skolem, this is equivalent to satisfiability in any universe.

-/

universes u v w w'

open cardinal category_theory
open_locale cardinal first_order

namespace first_order
namespace language

variables {L : language.{u v}} {T : L.Theory} {α : Type w} {n : ℕ}

namespace Theory

variable (T)

/-- A theory is satisfiable if a structure models it. -/
def is_satisfiable : Prop := nonempty (Model.{u v (max u v)} T)

/-- A theory is finitely satisfiable if all of its finite subtheories are satisfiable. -/
def is_finitely_satisfiable : Prop :=
∀ (T0 : finset L.sentence), (T0 : L.Theory) ⊆ T → (T0 : L.Theory).is_satisfiable

variables {T} {T' : L.Theory}

lemma model.is_satisfiable (M : Type w) [n : nonempty M]
  [S : L.Structure M] [M ⊨ T] : T.is_satisfiable :=
⟨((⊥ : substructure _ (Model.of T M)).elementary_skolem₁_reduct.to_Model T).shrink⟩

lemma is_satisfiable.mono (h : T'.is_satisfiable) (hs : T ⊆ T') :
  T.is_satisfiable :=
⟨(Theory.model.mono (Model.is_model h.some) hs).bundled⟩

lemma is_satisfiable_empty (L : language.{u v}) :
  is_satisfiable (∅ : L.Theory) :=
⟨default⟩

lemma is_satisfiable_of_is_satisfiable_on_Theory {L' : language.{w w'}} (φ : L →ᴸ L')
  (h : (φ.on_Theory T).is_satisfiable) :
  T.is_satisfiable :=
model.is_satisfiable (h.some.reduct φ)

lemma is_satisfiable_on_Theory_iff {L' : language.{w w'}} {φ : L →ᴸ L'}
  (h : φ.injective) :
  (φ.on_Theory T).is_satisfiable ↔ T.is_satisfiable :=
begin
  classical,
  refine ⟨is_satisfiable_of_is_satisfiable_on_Theory φ,
    λ h', _⟩,
  haveI : inhabited (h'.some) := classical.inhabited_of_nonempty',
  exact model.is_satisfiable (h'.some.default_expansion h),
end

lemma is_satisfiable.is_finitely_satisfiable (h : T.is_satisfiable) :
  T.is_finitely_satisfiable :=
λ _, h.mono

/-- The Compactness Theorem of first-order logic: A theory is satisfiable if and only if it is
finitely satisfiable. -/
theorem is_satisfiable_iff_is_finitely_satisfiable {T : L.Theory} :
  T.is_satisfiable ↔ T.is_finitely_satisfiable :=
⟨Theory.is_satisfiable.is_finitely_satisfiable, λ h, begin
  classical,
  set M : Π (T0 : finset T), Type (max u v) :=
    λ T0, (h (T0.map (function.embedding.subtype (λ x, x ∈ T)))
      T0.map_subtype_subset).some with hM,
  let M' := filter.product ↑(ultrafilter.of (filter.at_top : filter (finset T))) M,
  haveI h' : M' ⊨ T,
  { refine ⟨λ φ hφ, _⟩,
    rw ultraproduct.sentence_realize,
    refine filter.eventually.filter_mono (ultrafilter.of_le _)
      (filter.eventually_at_top.2 ⟨{⟨φ, hφ⟩},
      λ s h', Theory.realize_sentence_of_mem (s.map (function.embedding.subtype (λ x, x ∈ T))) _⟩),
    simp only [finset.coe_map, function.embedding.coe_subtype, set.mem_image, finset.mem_coe,
      subtype.exists, subtype.coe_mk, exists_and_distrib_right, exists_eq_right],
    exact ⟨hφ, h' (finset.mem_singleton_self _)⟩ },
  exact ⟨Model.of T M'⟩,
end⟩

theorem is_satisfiable_directed_union_iff {ι : Type*} [nonempty ι]
  {T : ι → L.Theory} (h : directed (⊆) T) :
  Theory.is_satisfiable (⋃ i, T i) ↔ ∀ i, (T i).is_satisfiable :=
begin
  refine ⟨λ h' i, h'.mono (set.subset_Union _ _), λ h', _⟩,
  rw [is_satisfiable_iff_is_finitely_satisfiable, is_finitely_satisfiable],
  intros T0 hT0,
  obtain ⟨i, hi⟩ := h.exists_mem_subset_of_finset_subset_bUnion hT0,
  exact (h' i).mono hi,
end

theorem is_satisfiable_union_distinct_constants_theory_of_card_le (T : L.Theory) (s : set α)
  (M : Type w') [nonempty M] [L.Structure M] [M ⊨ T]
  (h : cardinal.lift.{w'} (# s) ≤ cardinal.lift.{w} (# M)) :
  ((L.Lhom_with_constants α).on_Theory T ∪ L.distinct_constants_theory s).is_satisfiable :=
begin
  haveI : inhabited M := classical.inhabited_of_nonempty infer_instance,
  rw [cardinal.lift_mk_le'] at h,
  letI : (constants_on α).Structure M :=
    constants_on.Structure (function.extend coe h.some default),
  haveI : M ⊨ (L.Lhom_with_constants α).on_Theory T ∪ L.distinct_constants_theory s,
  { refine ((Lhom.on_Theory_model _ _).2 infer_instance).union _,
    rw [model_distinct_constants_theory],
    refine λ a as b bs ab, _,
    rw [← subtype.coe_mk a as, ← subtype.coe_mk b bs, ← subtype.ext_iff],
    exact h.some.injective
      ((subtype.coe_injective.extend_apply h.some default ⟨a, as⟩).symm.trans
      (ab.trans (subtype.coe_injective.extend_apply h.some default ⟨b, bs⟩))), },
  exact model.is_satisfiable M,
end

theorem is_satisfiable_union_distinct_constants_theory_of_infinite (T : L.Theory) (s : set α)
  (M : Type w') [L.Structure M] [M ⊨ T] [infinite M] :
  ((L.Lhom_with_constants α).on_Theory T ∪ L.distinct_constants_theory s).is_satisfiable :=
begin
  classical,
  rw [distinct_constants_theory_eq_Union, set.union_Union, is_satisfiable_directed_union_iff],
  { exact λ t, is_satisfiable_union_distinct_constants_theory_of_card_le T _ M ((lift_le_aleph_0.2
      ((finset_card_lt_aleph_0 _).le)).trans (aleph_0_le_lift.2 (aleph_0_le_mk M))) },
  { refine (monotone_const.union (monotone_distinct_constants_theory.comp _)).directed_le,
    simp only [finset.coe_map, function.embedding.coe_subtype],
    exact set.monotone_image.comp (λ _ _, finset.coe_subset.2) }
end

/-- Any theory with an infinite model has arbitrarily large models. -/
lemma exists_large_model_of_infinite_model (T : L.Theory) (κ : cardinal.{w})
  (M : Type w') [L.Structure M] [M ⊨ T] [infinite M] :
  ∃ (N : Model.{_ _ (max u v w)} T), cardinal.lift.{max u v w} κ ≤ # N :=
begin
  obtain ⟨N⟩ :=
    is_satisfiable_union_distinct_constants_theory_of_infinite T (set.univ : set κ.out) M,
  refine ⟨(N.is_model.mono (set.subset_union_left _ _)).bundled.reduct _, _⟩,
  haveI : N ⊨ distinct_constants_theory _ _ := N.is_model.mono (set.subset_union_right _ _),
  simp only [Model.reduct_carrier, coe_of, Model.carrier_eq_coe],
  refine trans (lift_le.2 (le_of_eq (cardinal.mk_out κ).symm)) _,
  rw [← mk_univ],
  refine (card_le_of_model_distinct_constants_theory L set.univ N).trans (lift_le.1 _),
  rw lift_lift,
end

lemma is_satisfiable_Union_iff_is_satisfiable_Union_finset {ι : Type*} (T : ι → L.Theory) :
  is_satisfiable (⋃ i, T i) ↔ ∀ (s : finset ι), is_satisfiable (⋃ (i ∈ s), T i) :=
begin
  classical,
  refine ⟨λ h s, h.mono (set.Union_mono (λ _, set.Union_subset_iff.2 (λ _, refl _))), λ h, _⟩,
  rw is_satisfiable_iff_is_finitely_satisfiable,
  intros s hs,
  rw set.Union_eq_Union_finset at hs,
  obtain ⟨t, ht⟩ := directed.exists_mem_subset_of_finset_subset_bUnion _ hs,
  { exact (h t).mono ht },
  { exact (monotone.directed_le (λ t1 t2 h, set.Union_mono (λ _, set.Union_mono'
    (λ h1, ⟨h h1, refl _⟩)))) },
end

end Theory

variables (L)

/-- A version of The Downward Löwenheim–Skolem theorem where the structure `N` elementarily embeds
into `M`, but is not by type a substructure of `M`, and thus can be chosen to belong to the universe
of the cardinal `κ`.
 -/
lemma exists_elementary_embedding_card_eq_of_le (M : Type w') [L.Structure M] [nonempty M]
  (κ : cardinal.{w})
  (h1 : ℵ₀ ≤ κ)
  (h2 : lift.{w} L.card ≤ cardinal.lift.{max u v} κ)
  (h3 : lift.{w'} κ ≤ cardinal.lift.{w} (# M)) :
  ∃ (N : bundled L.Structure), nonempty (N ↪ₑ[L] M) ∧ # N = κ :=
begin
  obtain ⟨S, _, hS⟩ := exists_elementary_substructure_card_eq L ∅ κ h1 (by simp) h2 h3,
  haveI : small.{w} S,
  { rw [← lift_inj.{_ (w + 1)}, lift_lift, lift_lift] at hS,
    exact small_iff_lift_mk_lt_univ.2 (lt_of_eq_of_lt hS κ.lift_lt_univ') },
  refine ⟨(equiv_shrink S).bundled_induced L,
    ⟨S.subtype.comp (equiv.bundled_induced_equiv L _).symm.to_elementary_embedding⟩,
    lift_inj.1 (trans _ hS)⟩,
  simp only [equiv.bundled_induced_α, lift_mk_shrink'],
end

/-- The Upward Löwenheim–Skolem Theorem: If `κ` is a cardinal greater than the cardinalities of `L`
and an infinite `L`-structure `M`, then `M` has an elementary extension of cardinality `κ`. -/
theorem exists_elementary_embedding_card_eq_of_ge (M : Type w') [L.Structure M] [iM : infinite M]
  (κ : cardinal.{w})
  (h1 : cardinal.lift.{w} L.card ≤ cardinal.lift.{max u v} κ)
  (h2 : cardinal.lift.{w} (# M) ≤ cardinal.lift.{w'} κ) :
  ∃ (N : bundled L.Structure), nonempty (M ↪ₑ[L] N) ∧ # N = κ :=
begin
  obtain ⟨N0, hN0⟩ := (L.elementary_diagram M).exists_large_model_of_infinite_model κ M,
  let f0 := elementary_embedding.of_models_elementary_diagram L M N0,
  rw [← lift_le.{(max w w') (max u v)}, lift_lift, lift_lift] at h2,
  obtain ⟨N, ⟨NN0⟩, hN⟩ := exists_elementary_embedding_card_eq_of_le (L[[M]]) N0 κ
    (aleph_0_le_lift.1 ((aleph_0_le_lift.2 (aleph_0_le_mk M)).trans h2)) _ (hN0.trans _),
  { letI := (Lhom_with_constants L M).reduct N,
    haveI h : N ⊨ L.elementary_diagram M :=
      (NN0.Theory_model_iff (L.elementary_diagram M)).2 infer_instance,
    refine ⟨bundled.of N, ⟨_⟩, hN⟩,
    apply elementary_embedding.of_models_elementary_diagram L M N, },
  { simp only [card_with_constants, lift_add, lift_lift],
    rw [add_comm, add_eq_max (aleph_0_le_lift.2 (infinite_iff.1 iM)), max_le_iff],
    rw [← lift_le.{_ w'}, lift_lift, lift_lift] at h1,
    exact ⟨h2, h1⟩, },
  { rw [← lift_umax', lift_id] },
end

/-- The Löwenheim–Skolem Theorem: If `κ` is a cardinal greater than the cardinalities of `L`
and an infinite `L`-structure `M`, then there is an elementary embedding in the appropriate
direction between then `M` and a structure of cardinality `κ`. -/
theorem exists_elementary_embedding_card_eq (M : Type w') [L.Structure M] [iM : infinite M]
  (κ : cardinal.{w})
  (h1 : ℵ₀ ≤ κ)
  (h2 : lift.{w} L.card ≤ cardinal.lift.{max u v} κ) :
  ∃ (N : bundled L.Structure), (nonempty (N ↪ₑ[L] M) ∨ nonempty (M ↪ₑ[L] N)) ∧ # N = κ :=
begin
  cases le_or_gt (lift.{w'} κ) (cardinal.lift.{w} (# M)),
  { obtain ⟨N, hN1, hN2⟩ := exists_elementary_embedding_card_eq_of_le L M κ h1 h2 h,
    exact ⟨N, or.inl hN1, hN2⟩ },
  { obtain ⟨N, hN1, hN2⟩ := exists_elementary_embedding_card_eq_of_ge L M κ h2 (le_of_lt h),
    exact ⟨N, or.inr hN1, hN2⟩ }
end

/-- A consequence of the Löwenheim–Skolem Theorem: If `κ` is a cardinal greater than the
cardinalities of `L` and an infinite `L`-structure `M`, then there is a structure of cardinality `κ`
elementarily equivalent to `M`. -/
lemma exists_elementarily_equivalent_card_eq (M : Type w') [L.Structure M] [infinite M]
  (κ : cardinal.{w})
  (h1 : ℵ₀ ≤ κ)
  (h2 : lift.{w} L.card ≤ cardinal.lift.{max u v} κ) :
  ∃ (N : category_theory.bundled L.Structure), M ≅[L] N ∧ # N = κ :=
begin
  obtain ⟨N, (NM | MN), hNκ⟩ := exists_elementary_embedding_card_eq L M κ h1 h2,
  { exact ⟨N, NM.some.elementarily_equivalent.symm, hNκ⟩ },
  { exact ⟨N, MN.some.elementarily_equivalent, hNκ⟩ }
end

variable {L}

namespace Theory

theorem exists_model_card_eq
  (h : ∃ (M : Model.{u v (max u v)} T), infinite M)
  (κ : cardinal.{w})
  (h1 : ℵ₀ ≤ κ)
  (h2 : cardinal.lift.{w} L.card ≤ cardinal.lift.{max u v} κ) :
  ∃ (N : Model.{u v w} T), # N = κ :=
begin
  casesI h with M MI,
  obtain ⟨N, hN, rfl⟩ := exists_elementarily_equivalent_card_eq L M κ h1 h2,
  haveI : nonempty N := hN.nonempty,
  exact ⟨hN.Theory_model.bundled, rfl⟩,
end

variable (T)

/-- A theory models a (bounded) formula when any of its nonempty models realizes that formula on all
  inputs.-/
def models_bounded_formula (φ : L.bounded_formula α n) : Prop :=
  ∀ (M : Model.{u v (max u v)} T) (v : α → M) (xs : fin n → M), φ.realize v xs

-- input using \|= or \vDash, but not using \models
infix (name := models_bounded_formula) ` ⊨ `:51 := models_bounded_formula

variable {T}

lemma models_formula_iff {φ : L.formula α} :
  T ⊨ φ ↔ ∀ (M : Model.{u v (max u v)} T) (v : α → M), φ.realize v :=
forall_congr (λ M, forall_congr (λ v, unique.forall_iff))

lemma models_sentence_iff {φ : L.sentence} :
  T ⊨ φ ↔ ∀ (M : Model.{u v (max u v)} T), M ⊨ φ :=
models_formula_iff.trans (forall_congr (λ M, unique.forall_iff))

lemma models_sentence_of_mem {φ : L.sentence} (h : φ ∈ T) :
  T ⊨ φ :=
models_sentence_iff.2 (λ _, realize_sentence_of_mem T h)

lemma models_iff_not_satisfiable (φ : L.sentence) :
  T ⊨ φ ↔ ¬ is_satisfiable (T ∪ {φ.not}) :=
begin
  rw [models_sentence_iff, is_satisfiable],
  refine ⟨λ h1 h2, (sentence.realize_not _).1 (realize_sentence_of_mem (T ∪ {formula.not φ})
    (set.subset_union_right _ _ (set.mem_singleton _)))
    (h1 (h2.some.subtheory_Model (set.subset_union_left _ _))), λ h M, _⟩,
  contrapose! h,
  rw ← sentence.realize_not at h,
  refine ⟨{ carrier := M,
    is_model := ⟨λ ψ hψ, hψ.elim (realize_sentence_of_mem _) (λ h', _)⟩, }⟩,
  rw set.mem_singleton_iff.1 h',
  exact h,
end

lemma models_bounded_formula.realize_sentence {φ : L.sentence} (h : T ⊨ φ)
  (M : Type*) [L.Structure M] [M ⊨ T] [nonempty M] :
  M ⊨ φ :=
begin
  rw models_iff_not_satisfiable at h,
  contrapose! h,
  haveI : M ⊨ (T ∪ {formula.not φ}),
  { simp only [set.union_singleton, model_iff, set.mem_insert_iff, forall_eq_or_imp,
      sentence.realize_not],
    rw ← model_iff,
    exact ⟨h, infer_instance⟩ },
  exact model.is_satisfiable M,
end

/-- A theory is complete when it is satisfiable and models each sentence or its negation. -/
def is_complete (T : L.Theory) : Prop :=
T.is_satisfiable ∧ ∀ (φ : L.sentence), (T ⊨ φ) ∨ (T ⊨ φ.not)

namespace is_complete

lemma models_not_iff (h : T.is_complete) (φ : L.sentence)  :
  T ⊨ φ.not ↔ ¬ T ⊨ φ :=
begin
  cases h.2 φ with hφ hφn,
  { simp only [hφ, not_true, iff_false],
    rw [models_sentence_iff, not_forall],
    refine ⟨h.1.some, _⟩,
    simp only [sentence.realize_not, not_not],
    exact models_sentence_iff.1 hφ _ },
  { simp only [hφn, true_iff],
    intro hφ,
    rw models_sentence_iff at *,
    exact hφn h.1.some (hφ _) }
end

lemma realize_sentence_iff (h : T.is_complete) (φ : L.sentence)
  (M : Type*) [L.Structure M] [M ⊨ T] [nonempty M] :
  M ⊨ φ ↔ T ⊨ φ :=
begin
  cases h.2 φ with hφ hφn,
  { exact iff_of_true (hφ.realize_sentence M) hφ },
  { exact iff_of_false ((sentence.realize_not M).1 (hφn.realize_sentence M))
      ((h.models_not_iff φ).1 hφn), }
end

end is_complete

/-- A theory is maximal when it is satisfiable and contains each sentence or its negation.
  Maximal theories are complete. -/
def is_maximal (T : L.Theory) : Prop :=
T.is_satisfiable ∧ ∀ (φ : L.sentence), φ ∈ T ∨ φ.not ∈ T

lemma is_maximal.is_complete (h : T.is_maximal) : T.is_complete :=
h.imp_right (forall_imp (λ _, or.imp models_sentence_of_mem models_sentence_of_mem))

lemma is_maximal.mem_or_not_mem (h : T.is_maximal) (φ : L.sentence) :
  φ ∈ T ∨ φ.not ∈ T :=
h.2 φ

lemma is_maximal.mem_of_models (h : T.is_maximal) {φ : L.sentence}
  (hφ : T ⊨ φ) :
  φ ∈ T :=
begin
  refine (h.mem_or_not_mem φ).resolve_right (λ con, _),
  rw [models_iff_not_satisfiable, set.union_singleton, set.insert_eq_of_mem con] at hφ,
  exact hφ h.1,
end

lemma is_maximal.mem_iff_models (h : T.is_maximal) (φ : L.sentence) :
  φ ∈ T ↔ T ⊨ φ :=
⟨models_sentence_of_mem, h.mem_of_models⟩

/-- Two (bounded) formulas are semantically equivalent over a theory `T` when they have the same
interpretation in every model of `T`. (This is also known as logical equivalence, which also has a
proof-theoretic definition.) -/
def semantically_equivalent (T : L.Theory) (φ ψ : L.bounded_formula α n) : Prop :=
T ⊨ φ.iff ψ

@[refl] lemma semantically_equivalent.refl (φ : L.bounded_formula α n) :
  T.semantically_equivalent φ φ :=
λ M v xs, by rw bounded_formula.realize_iff

instance : is_refl (L.bounded_formula α n) T.semantically_equivalent :=
⟨semantically_equivalent.refl⟩

@[symm] lemma semantically_equivalent.symm {φ ψ : L.bounded_formula α n}
  (h : T.semantically_equivalent φ ψ) :
  T.semantically_equivalent ψ φ :=
λ M v xs, begin
  rw [bounded_formula.realize_iff, iff.comm, ← bounded_formula.realize_iff],
  exact h M v xs,
end

@[trans] lemma semantically_equivalent.trans {φ ψ θ : L.bounded_formula α n}
  (h1 : T.semantically_equivalent φ ψ) (h2 : T.semantically_equivalent ψ θ) :
  T.semantically_equivalent φ θ :=
λ M v xs, begin
  have h1' := h1 M v xs,
  have h2' := h2 M v xs,
  rw [bounded_formula.realize_iff] at *,
  exact ⟨h2'.1 ∘ h1'.1, h1'.2 ∘ h2'.2⟩,
end

lemma semantically_equivalent.realize_bd_iff {φ ψ : L.bounded_formula α n}
  {M : Type (max u v)} [ne : nonempty M] [str : L.Structure M] [hM : T.model M]
  (h : T.semantically_equivalent φ ψ) {v : α → M} {xs : (fin n → M)} :
  φ.realize v xs ↔ ψ.realize v xs :=
bounded_formula.realize_iff.1 (h (Model.of T M) v xs)

lemma semantically_equivalent.realize_iff {φ ψ : L.formula α}
  {M : Type (max u v)} [ne : nonempty M] [str : L.Structure M] (hM : T.model M)
  (h : T.semantically_equivalent φ ψ) {v : α → M} :
  φ.realize v ↔ ψ.realize v :=
h.realize_bd_iff

/-- Semantic equivalence forms an equivalence relation on formulas. -/
def semantically_equivalent_setoid (T : L.Theory) : setoid (L.bounded_formula α n) :=
{ r := semantically_equivalent T,
  iseqv := ⟨λ _, refl _, λ a b h, h.symm, λ _ _ _ h1 h2, h1.trans h2⟩ }

protected lemma semantically_equivalent.all {φ ψ : L.bounded_formula α (n + 1)}
  (h : T.semantically_equivalent φ ψ) : T.semantically_equivalent φ.all ψ.all :=
begin
  simp_rw [semantically_equivalent, models_bounded_formula, bounded_formula.realize_iff,
    bounded_formula.realize_all],
  exact λ M v xs, forall_congr (λ a, h.realize_bd_iff),
end

protected lemma semantically_equivalent.ex {φ ψ : L.bounded_formula α (n + 1)}
  (h : T.semantically_equivalent φ ψ) : T.semantically_equivalent φ.ex ψ.ex :=
begin
  simp_rw [semantically_equivalent, models_bounded_formula, bounded_formula.realize_iff,
    bounded_formula.realize_ex],
  exact λ M v xs, exists_congr (λ a, h.realize_bd_iff),
end

protected lemma semantically_equivalent.not {φ ψ : L.bounded_formula α n}
  (h : T.semantically_equivalent φ ψ) : T.semantically_equivalent φ.not ψ.not :=
begin
  simp_rw [semantically_equivalent, models_bounded_formula, bounded_formula.realize_iff,
    bounded_formula.realize_not],
  exact λ M v xs, not_congr h.realize_bd_iff,
end

protected lemma semantically_equivalent.imp {φ ψ φ' ψ' : L.bounded_formula α n}
  (h : T.semantically_equivalent φ ψ) (h' : T.semantically_equivalent φ' ψ') :
  T.semantically_equivalent (φ.imp φ') (ψ.imp ψ') :=
begin
  simp_rw [semantically_equivalent, models_bounded_formula, bounded_formula.realize_iff,
    bounded_formula.realize_imp],
  exact λ M v xs, imp_congr h.realize_bd_iff h'.realize_bd_iff,
end

end Theory

namespace complete_theory

variables (L) (M : Type w) [L.Structure M]

lemma is_satisfiable [nonempty M] : (L.complete_theory M).is_satisfiable :=
Theory.model.is_satisfiable M

lemma mem_or_not_mem (φ : L.sentence) :
  φ ∈ L.complete_theory M ∨ φ.not ∈ L.complete_theory M :=
by simp_rw [complete_theory, set.mem_set_of_eq, sentence.realize, formula.realize_not, or_not]

lemma is_maximal [nonempty M] : (L.complete_theory M).is_maximal :=
⟨is_satisfiable L M, mem_or_not_mem L M⟩

lemma is_complete [nonempty M] : (L.complete_theory M).is_complete :=
(complete_theory.is_maximal L M).is_complete

end complete_theory

namespace bounded_formula
variables (φ ψ : L.bounded_formula α n)

lemma semantically_equivalent_not_not :
  T.semantically_equivalent φ φ.not.not :=
λ M v xs, by simp

lemma imp_semantically_equivalent_not_sup :
  T.semantically_equivalent (φ.imp ψ) (φ.not ⊔ ψ) :=
λ M v xs, by simp [imp_iff_not_or]

lemma sup_semantically_equivalent_not_inf_not :
  T.semantically_equivalent (φ ⊔ ψ) (φ.not ⊓ ψ.not).not :=
λ M v xs, by simp [imp_iff_not_or]

lemma inf_semantically_equivalent_not_sup_not :
  T.semantically_equivalent (φ ⊓ ψ) (φ.not ⊔ ψ.not).not :=
λ M v xs, by simp [and_iff_not_or_not]

lemma all_semantically_equivalent_not_ex_not (φ : L.bounded_formula α (n + 1)) :
  T.semantically_equivalent φ.all φ.not.ex.not :=
λ M v xs, by simp

lemma ex_semantically_equivalent_not_all_not (φ : L.bounded_formula α (n + 1)) :
  T.semantically_equivalent φ.ex φ.not.all.not :=
λ M v xs, by simp

lemma semantically_equivalent_all_lift_at :
  T.semantically_equivalent φ (φ.lift_at 1 n).all :=
λ M v xs, by { resetI, rw [realize_iff, realize_all_lift_at_one_self] }

end bounded_formula

namespace formula
variables (φ ψ : L.formula α)

lemma semantically_equivalent_not_not :
  T.semantically_equivalent φ φ.not.not :=
φ.semantically_equivalent_not_not

lemma imp_semantically_equivalent_not_sup :
  T.semantically_equivalent (φ.imp ψ) (φ.not ⊔ ψ) :=
φ.imp_semantically_equivalent_not_sup ψ

lemma sup_semantically_equivalent_not_inf_not :
  T.semantically_equivalent (φ ⊔ ψ) (φ.not ⊓ ψ.not).not :=
φ.sup_semantically_equivalent_not_inf_not ψ

lemma inf_semantically_equivalent_not_sup_not :
  T.semantically_equivalent (φ ⊓ ψ) (φ.not ⊔ ψ.not).not :=
φ.inf_semantically_equivalent_not_sup_not ψ
end formula

namespace bounded_formula

lemma is_qf.induction_on_sup_not {P : L.bounded_formula α n → Prop} {φ : L.bounded_formula α n}
  (h : is_qf φ)
  (hf : P (⊥ : L.bounded_formula α n))
  (ha : ∀ (ψ : L.bounded_formula α n), is_atomic ψ → P ψ)
  (hsup : ∀ {φ₁ φ₂} (h₁ : P φ₁) (h₂ : P φ₂), P (φ₁ ⊔ φ₂))
  (hnot : ∀ {φ} (h : P φ), P φ.not)
  (hse : ∀ {φ₁ φ₂ : L.bounded_formula α n}
    (h : Theory.semantically_equivalent ∅ φ₁ φ₂), P φ₁ ↔ P φ₂) :
  P φ :=
is_qf.rec_on h hf ha (λ φ₁ φ₂ _ _ h1 h2,
  (hse (φ₁.imp_semantically_equivalent_not_sup φ₂)).2 (hsup (hnot h1) h2))

lemma is_qf.induction_on_inf_not {P : L.bounded_formula α n → Prop} {φ : L.bounded_formula α n}
  (h : is_qf φ)
  (hf : P (⊥ : L.bounded_formula α n))
  (ha : ∀ (ψ : L.bounded_formula α n), is_atomic ψ → P ψ)
  (hinf : ∀ {φ₁ φ₂} (h₁ : P φ₁) (h₂ : P φ₂), P (φ₁ ⊓ φ₂))
  (hnot : ∀ {φ} (h : P φ), P φ.not)
  (hse : ∀ {φ₁ φ₂ : L.bounded_formula α n}
    (h : Theory.semantically_equivalent ∅ φ₁ φ₂), P φ₁ ↔ P φ₂) :
  P φ :=
h.induction_on_sup_not hf ha (λ φ₁ φ₂ h1 h2,
  ((hse (φ₁.sup_semantically_equivalent_not_inf_not φ₂)).2 (hnot (hinf (hnot h1) (hnot h2)))))
  (λ _, hnot) (λ _ _, hse)

lemma semantically_equivalent_to_prenex (φ : L.bounded_formula α n) :
  (∅ : L.Theory).semantically_equivalent φ φ.to_prenex :=
λ M v xs, by rw [realize_iff, realize_to_prenex]

lemma induction_on_all_ex {P : Π {m}, L.bounded_formula α m → Prop} (φ : L.bounded_formula α n)
  (hqf : ∀ {m} {ψ : L.bounded_formula α m}, is_qf ψ → P ψ)
  (hall : ∀ {m} {ψ  : L.bounded_formula α (m + 1)} (h : P ψ), P ψ.all)
  (hex : ∀ {m} {φ : L.bounded_formula α (m + 1)} (h : P φ), P φ.ex)
  (hse : ∀ {m} {φ₁ φ₂ : L.bounded_formula α m}
    (h : Theory.semantically_equivalent ∅ φ₁ φ₂), P φ₁ ↔ P φ₂) :
  P φ :=
begin
  suffices h' : ∀ {m} {φ : L.bounded_formula α m}, φ.is_prenex → P φ,
  { exact (hse φ.semantically_equivalent_to_prenex).2 (h' φ.to_prenex_is_prenex) },
  intros m φ hφ,
  induction hφ with _ _ hφ _ _ _ hφ _ _ _ hφ,
  { exact hqf hφ },
  { exact hall hφ, },
  { exact hex hφ, },
end

lemma induction_on_exists_not {P : Π {m}, L.bounded_formula α m → Prop} (φ : L.bounded_formula α n)
  (hqf : ∀ {m} {ψ : L.bounded_formula α m}, is_qf ψ → P ψ)
  (hnot : ∀ {m} {φ : L.bounded_formula α m} (h : P φ), P φ.not)
  (hex : ∀ {m} {φ : L.bounded_formula α (m + 1)} (h : P φ), P φ.ex)
  (hse : ∀ {m} {φ₁ φ₂ : L.bounded_formula α m}
    (h : Theory.semantically_equivalent ∅ φ₁ φ₂), P φ₁ ↔ P φ₂) :
  P φ :=
φ.induction_on_all_ex
  (λ _ _, hqf)
  (λ _ φ hφ, (hse φ.all_semantically_equivalent_not_ex_not).2 (hnot (hex (hnot hφ))))
  (λ _ _, hex) (λ _ _ _, hse)

end bounded_formula
end language
end first_order

namespace cardinal
open first_order first_order.language

variables {L : language.{u v}} (κ : cardinal.{w}) (T : L.Theory)

/-- A theory is `κ`-categorical if all models of size `κ` are isomorphic. -/
def categorical : Prop :=
∀ (M N : T.Model), # M = κ → # N = κ → nonempty (M ≃[L] N)

/-- The Łoś–Vaught Test : a criterion for categorical theories to be complete. -/
lemma categorical.is_complete (h : κ.categorical T)
  (h1 : ℵ₀ ≤ κ)
  (h2 : cardinal.lift.{w} L.card ≤ cardinal.lift.{max u v} κ)
  (hS : T.is_satisfiable)
  (hT : ∀ (M : Theory.Model.{u v max u v} T), infinite M) :
  T.is_complete :=
⟨hS, λ φ, begin
  obtain ⟨N, hN⟩ := Theory.exists_model_card_eq ⟨hS.some, hT hS.some⟩ κ h1 h2,
  rw [Theory.models_sentence_iff, Theory.models_sentence_iff],
  by_contra con,
  push_neg at con,
  obtain ⟨⟨MF, hMF⟩, MT, hMT⟩ := con,
  rw [sentence.realize_not, not_not] at hMT,
  refine hMF _,
  haveI := hT MT,
  haveI := hT MF,
  obtain ⟨NT, MNT, hNT⟩ := exists_elementarily_equivalent_card_eq L MT κ h1 h2,
  obtain ⟨NF, MNF, hNF⟩ := exists_elementarily_equivalent_card_eq L MF κ h1 h2,
  obtain ⟨TF⟩ := h (MNT.to_Model T) (MNF.to_Model T) hNT hNF,
  exact ((MNT.realize_sentence φ).trans
    ((TF.realize_sentence φ).trans (MNF.realize_sentence φ).symm)).1 hMT,
end⟩

theorem empty_Theory_categorical (T : language.empty.Theory) :
  κ.categorical T :=
λ M N hM hN, by rw [empty.nonempty_equiv_iff, hM, hN]

theorem empty_infinite_Theory_is_complete :
  language.empty.infinite_theory.is_complete :=
(empty_Theory_categorical ℵ₀ _).is_complete ℵ₀ _ le_rfl (by simp)
  ⟨Theory.model.bundled ((model_infinite_theory_iff language.empty).2 nat.infinite)⟩
  (λ M, (model_infinite_theory_iff language.empty).1 M.is_model)

end cardinal
