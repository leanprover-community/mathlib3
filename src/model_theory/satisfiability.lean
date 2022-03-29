/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import model_theory.ultraproducts

/-!
# First-Order Satisfiability
This file deals with the satisfiability of first-order theories, as well as equivalence over them.

## Main Definitions
* `first_order.language.Theory.is_satisfiable`: `T.is_satisfiable` indicates that `T` has a nonempty
model.
* `first_order.language.Theory.is_finitely_satisfiable`: `T.is_finitely_satisfiable` indicates that
every finite subset of `T` is satisfiable.
* `first_order.language.Theory.semantically_equivalent`: `T.semantically_equivalent φ ψ` indicates
that `φ` and `ψ` are equivalent formulas or sentences in models of `T`.

## Main Results
* The Compactness Theorem, `first_order.language.Theory.is_satisfiable_iff_is_finitely_satisfiable`,
shows that a theory is satisfiable iff it is finitely satisfiable.

## Implementation Details
* Satisfiability of an `L.Theory` `T` is defined in the minimal universe containing all the symbols
of `L`. By Löwenheim-Skolem, this is equivalent to satisfiability in any universe, but this is not
yet proven in mathlib.

-/

universes u v w

namespace first_order
namespace language

variables {L : language.{u v}} {T : L.Theory} {α : Type*} {n : ℕ}

namespace Theory

variable (T)

/-- A theory is satisfiable if a structure models it. -/
def is_satisfiable : Prop :=
∃ (M : Type (max u v)) [nonempty M] [str : L.Structure M], @Theory.model L M str T

/-- A theory is finitely satisfiable if all of its finite subtheories are satisfiable. -/
def is_finitely_satisfiable : Prop :=
∀ (T0 : finset L.sentence), (T0 : L.Theory) ⊆ T → (T0 : L.Theory).is_satisfiable

variables {T} {T' : L.Theory}

/-- Given that a theory is satisfiable, selects a model using choice. -/
def is_satisfiable.some_model (h : T.is_satisfiable) : Type* := classical.some h

instance is_satisfiable.nonempty_some_model (h : T.is_satisfiable) :
  nonempty (h.some_model) :=
classical.some (classical.some_spec h)

noncomputable instance is_satisfiable.inhabited_some_model (h : T.is_satisfiable) :
  inhabited (h.some_model) := classical.inhabited_of_nonempty'

noncomputable instance is_satisfiable.some_model_structure (h : T.is_satisfiable) :
  L.Structure (h.some_model) :=
classical.some (classical.some_spec (classical.some_spec h))

instance is_satisfiable.some_model_models (h : T.is_satisfiable) :
  h.some_model ⊨ T :=
classical.some_spec (classical.some_spec (classical.some_spec h))

lemma model.is_satisfiable (M : Type (max u v)) [n : nonempty M]
  [S : L.Structure M] (h : T.model M) : T.is_satisfiable :=
⟨M, n, S, h⟩

lemma is_satisfiable.mono (h : T'.is_satisfiable) (hs : T ⊆ T') :
  T.is_satisfiable :=
⟨h.some_model, h.nonempty_some_model, h.some_model_structure,
  h.some_model_models.mono hs⟩

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
      T0.map_subtype_subset).some_model with hM,
  letI : Π (T0 : finset T), L.Structure (M T0) := λ T0, is_satisfiable.some_model_structure _,
  haveI : (filter.at_top : filter (finset T)).ne_bot := filter.at_top_ne_bot,
  refine ⟨(↑(ultrafilter.of filter.at_top) : filter _).product M, infer_instance,
    ultraproduct.Structure, ⟨_⟩⟩,
  intros φ hφ,
  rw ultraproduct.sentence_realize,
  refine filter.eventually.filter_mono (ultrafilter.of_le _) (filter.eventually_at_top.2 ⟨{⟨φ, hφ⟩},
    λ s h', Theory.realize_sentence_of_mem (s.map (function.embedding.subtype (λ x, x ∈ T))) _⟩),
  simp only [finset.coe_map, function.embedding.coe_subtype, set.mem_image, finset.mem_coe,
    subtype.exists, subtype.coe_mk, exists_and_distrib_right, exists_eq_right],
  exact ⟨hφ, h' (finset.mem_singleton_self _)⟩,
end⟩

variable (T)

/-- A theory models a (bounded) formula when any of its nonempty models realizes that formula on all
  inputs.-/
def models_bounded_formula (φ : L.bounded_formula α n) : Prop :=
  ∀ (M : Type (max u v)) [nonempty M] [str : L.Structure M] (v : α → M) (xs : fin n → M),
    @Theory.model L M str T → @bounded_formula.realize L M str α n φ v xs

infix ` ⊨ `:51 := models_bounded_formula -- input using \|= or \vDash, but not using \models

variable {T}

lemma models_formula_iff {φ : L.formula α} :
  T ⊨ φ ↔ ∀ (M : Type (max u v)) [nonempty M] [str : L.Structure M] (v : α → M),
    @Theory.model L M str T → @formula.realize L M str α φ v :=
forall_congr (λ M, forall_congr (λ ne, forall_congr (λ str, forall_congr (λ v, unique.forall_iff))))

lemma models_sentence_iff {φ : L.sentence} :
  T ⊨ φ ↔ ∀ (M : Type (max u v)) [nonempty M] [str : L.Structure M],
    @Theory.model L M str T → @sentence.realize L M str φ :=
begin
  rw [models_formula_iff],
  exact forall_congr (λ M, forall_congr (λ ne, forall_congr (λ str, unique.forall_iff)))
end

/-- Two (bounded) formulas are semantically equivalent over a theory `T` when they have the same
interpretation in every model of `T`. (This is also known as logical equivalence, which also has a
proof-theoretic definition.) -/
def semantically_equivalent (T : L.Theory) (φ ψ : L.bounded_formula α n) : Prop :=
T ⊨ φ.iff ψ

@[refl] lemma semantically_equivalent.refl (φ : L.bounded_formula α n) :
  T.semantically_equivalent φ φ :=
λ M ne str v xs hM, by rw bounded_formula.realize_iff

instance : is_refl (L.bounded_formula α n) T.semantically_equivalent :=
⟨semantically_equivalent.refl⟩

@[symm] lemma semantically_equivalent.symm {φ ψ : L.bounded_formula α n}
  (h : T.semantically_equivalent φ ψ) :
  T.semantically_equivalent ψ φ :=
λ M ne str v xs hM, begin
  haveI := ne,
  rw [bounded_formula.realize_iff, iff.comm, ← bounded_formula.realize_iff],
  exact h M v xs hM,
end

@[trans] lemma semantically_equivalent.trans {φ ψ θ : L.bounded_formula α n}
  (h1 : T.semantically_equivalent φ ψ) (h2 : T.semantically_equivalent ψ θ) :
  T.semantically_equivalent φ θ :=
λ M ne str v xs hM, begin
  haveI := ne,
  have h1' := h1 M v xs hM,
  have h2' := h2 M v xs hM,
  rw [bounded_formula.realize_iff] at *,
  exact ⟨h2'.1 ∘ h1'.1, h1'.2 ∘ h2'.2⟩,
end

lemma semantically_equivalent.realize_bd_iff {φ ψ : L.bounded_formula α n}
  {M : Type (max u v)} [ne : nonempty M] [str : L.Structure M] (hM : T.model M)
  (h : T.semantically_equivalent φ ψ) {v : α → M} {xs : (fin n → M)} :
  φ.realize v xs ↔ ψ.realize v xs :=
bounded_formula.realize_iff.1 (h M v xs hM)

lemma semantically_equivalent.some_model_realize_bd_iff {φ ψ : L.bounded_formula α n}
  (hsat : T.is_satisfiable) (h : T.semantically_equivalent φ ψ)
  {v : α → (hsat.some_model)} {xs : (fin n → (hsat.some_model))} :
  φ.realize v xs ↔ ψ.realize v xs :=
h.realize_bd_iff hsat.some_model_models

lemma semantically_equivalent.realize_iff {φ ψ : L.formula α}
  {M : Type (max u v)} [ne : nonempty M] [str : L.Structure M] (hM : T.model M)
  (h : T.semantically_equivalent φ ψ) {v : α → M} :
  φ.realize v ↔ ψ.realize v :=
h.realize_bd_iff hM

lemma semantically_equivalent.some_model_realize_iff {φ ψ : L.formula α}
  (hsat : T.is_satisfiable) (h : T.semantically_equivalent φ ψ) {v : α → (hsat.some_model)} :
  φ.realize v ↔ ψ.realize v :=
h.realize_iff hsat.some_model_models

/-- Semantic equivalence forms an equivalence relation on formulas. -/
def semantically_equivalent_setoid (T : L.Theory) : setoid (L.bounded_formula α n) :=
{ r := semantically_equivalent T,
  iseqv := ⟨λ _, refl _, λ a b h, h.symm, λ _ _ _ h1 h2, h1.trans h2⟩ }

protected lemma semantically_equivalent.all {φ ψ : L.bounded_formula α (n + 1)}
  (h : T.semantically_equivalent φ ψ) : T.semantically_equivalent φ.all ψ.all :=
begin
  rw [semantically_equivalent, models_bounded_formula],
  introsI M ne str v xs hM,
  simp [h.realize_bd_iff hM],
end

protected lemma semantically_equivalent.ex {φ ψ : L.bounded_formula α (n + 1)}
  (h : T.semantically_equivalent φ ψ) : T.semantically_equivalent φ.ex ψ.ex :=
begin
  rw [semantically_equivalent, models_bounded_formula],
  introsI M ne str v xs hM,
  simp [h.realize_bd_iff hM],
end

protected lemma semantically_equivalent.not {φ ψ : L.bounded_formula α n}
  (h : T.semantically_equivalent φ ψ) : T.semantically_equivalent φ.not ψ.not :=
begin
  rw [semantically_equivalent, models_bounded_formula],
  introsI M ne str v xs hM,
  simp [h.realize_bd_iff hM],
end

protected lemma semantically_equivalent.imp {φ ψ φ' ψ' : L.bounded_formula α n}
  (h : T.semantically_equivalent φ ψ) (h' : T.semantically_equivalent φ' ψ') :
  T.semantically_equivalent (φ.imp φ') (ψ.imp ψ') :=
begin
  rw [semantically_equivalent, models_bounded_formula],
  introsI M ne str v xs hM,
  simp [h.realize_bd_iff hM, h'.realize_bd_iff hM],
end

end Theory

namespace bounded_formula
variables (φ ψ : L.bounded_formula α n)

lemma semantically_equivalent_not_not :
  T.semantically_equivalent φ φ.not.not :=
λ M ne str v xs hM, by simp

lemma imp_semantically_equivalent_not_sup :
  T.semantically_equivalent (φ.imp ψ) (φ.not ⊔ ψ) :=
λ M ne str v xs hM, by simp [imp_iff_not_or]

lemma sup_semantically_equivalent_not_inf_not :
  T.semantically_equivalent (φ ⊔ ψ) (φ.not ⊓ ψ.not).not :=
λ M ne str v xs hM, by simp [imp_iff_not_or]

lemma inf_semantically_equivalent_not_sup_not :
  T.semantically_equivalent (φ ⊓ ψ) (φ.not ⊔ ψ.not).not :=
λ M ne str v xs hM, by simp [and_iff_not_or_not]

lemma all_semantically_equivalent_not_ex_not (φ : L.bounded_formula α (n + 1)) :
  T.semantically_equivalent φ.all φ.not.ex.not :=
λ M ne str v xs hM, by simp

lemma ex_semantically_equivalent_not_all_not (φ : L.bounded_formula α (n + 1)) :
  T.semantically_equivalent φ.ex φ.not.all.not :=
λ M ne str v xs hM, by simp

lemma semantically_equivalent_all_lift_at :
  T.semantically_equivalent φ (φ.lift_at 1 n).all :=
λ M ne str v xs hM, by { resetI, rw [realize_iff, realize_all_lift_at_one_self] }

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
λ M nM str v xs hM, begin
  resetI,
  simp,
end

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
