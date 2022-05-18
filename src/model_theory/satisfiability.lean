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

## Implementation Details
* Satisfiability of an `L.Theory` `T` is defined in the minimal universe containing all the symbols
of `L`. By Löwenheim-Skolem, this is equivalent to satisfiability in any universe.

-/

universes u v w w'

open cardinal
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
      ((function.extend_apply subtype.coe_injective h.some default ⟨a, as⟩).symm.trans
      (ab.trans (function.extend_apply subtype.coe_injective h.some default ⟨b, bs⟩))), },
  exact model.is_satisfiable M,
end

theorem is_satisfiable_union_distinct_constants_theory_of_infinite (T : L.Theory) (s : set α)
  (M : Type w') [L.Structure M] [M ⊨ T] [infinite M] :
  ((L.Lhom_with_constants α).on_Theory T ∪ L.distinct_constants_theory s).is_satisfiable :=
begin
  classical,
  rw [distinct_constants_theory_eq_Union, set.union_Union, is_satisfiable_directed_union_iff],
  { exact λ t, is_satisfiable_union_distinct_constants_theory_of_card_le T _ M ((lift_le_omega.2
      (le_of_lt (finset_card_lt_omega _))).trans (omega_le_lift.2 (omega_le_mk M))), },
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

variable (T)

/-- A theory models a (bounded) formula when any of its nonempty models realizes that formula on all
  inputs.-/
def models_bounded_formula (φ : L.bounded_formula α n) : Prop :=
  ∀ (M : Model.{u v (max u v)} T) (v : α → M) (xs : fin n → M), φ.realize v xs

infix ` ⊨ `:51 := models_bounded_formula -- input using \|= or \vDash, but not using \models

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

/-- A theory is complete when it is satisfiable and models each sentence or its negation. -/
def is_complete (T : L.Theory) : Prop :=
T.is_satisfiable ∧ ∀ (φ : L.sentence), (T ⊨ φ) ∨ (T ⊨ φ.not)

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

lemma is_complete [nonempty M] : (L.complete_theory M).is_complete :=
⟨is_satisfiable L M,
  λ φ, ((mem_or_not_mem L M φ).imp Theory.models_sentence_of_mem Theory.models_sentence_of_mem)⟩

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

theorem empty_Theory_categorical (T : language.empty.Theory) :
  κ.categorical T :=
λ M N hM hN, by rw [empty.nonempty_equiv_iff, hM, hN]

end cardinal
