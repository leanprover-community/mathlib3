/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import data.set_like.basic
import data.fintype.basic
import model_theory.terms_and_formulas

/-!
# Definable Sets
This file defines what it means for a set over a first-order structure to be definable.

## Main Definitions
* A `first_order.language.definable_set` is defined so that `L.definable_set M α` is the boolean
  algebra of subsets of `α → M` defined by formulas.

## Main Results
* `L.definable_set M α` forms a `boolean_algebra.

-/

universes u v w

namespace first_order
namespace language

variables {L : language.{u v}} {M : Type w} [L.Structure M] {A : set M}
open_locale first_order
open Structure

/-! ### Definability -/

section definability

variables (L) {α : Type} [fintype α] (A)

/-- A subset of a finite Cartesian product of a structure is definable over a set `A` when
  membership in the set is given by a first-order formula with parameters from `A`. -/
structure is_definable (s : set (α → M)) : Prop :=
(exists_formula : ∃ (φ : (L.with_params A).formula α), s = set_of (realize_formula M φ))

variables {L} {A} {B : set M} {s : set (α → M)}

lemma is_empty_definable_iff :
  L.is_definable ∅ s ↔ ∃ (φ : L.formula α), s = set_of (realize_formula M φ) :=
begin
  split,
  { rintro ⟨φ, rfl⟩,
    sorry, },
  { rintro ⟨φ, rfl⟩,
    sorry }
end

lemma is_definable.mono (hAs : L.is_definable A s) (hAB : A ⊆ B) :
  L.is_definable B s :=
begin
  obtain ⟨φ, rfl⟩ := hAs,
  refine ⟨⟨_, _⟩⟩,
end

@[simp]
lemma is_definable_empty : L.is_definable A (∅ : set (α → M)) :=
⟨⟨⊥, by {ext, simp} ⟩⟩

@[simp]
lemma is_definable_univ : L.is_definable A (set.univ : set (α → M)) :=
⟨⟨⊤, by {ext, simp} ⟩⟩

@[simp]
lemma is_definable.inter {f g : set (α → M)} (hf : L.is_definable A f) (hg : L.is_definable A g) :
  L.is_definable A (f ∩ g) :=
⟨begin
  rcases hf.exists_formula with ⟨φ, rfl⟩,
  rcases hg.exists_formula with ⟨θ, rfl⟩,
  refine ⟨φ ⊓ θ, _⟩,
  ext,
  simp,
end⟩

@[simp]
lemma is_definable.union {f g : set (α → M)} (hf : L.is_definable A f) (hg : L.is_definable A g) :
  L.is_definable A (f ∪ g) :=
⟨begin
  rcases hf.exists_formula with ⟨φ, hφ⟩,
  rcases hg.exists_formula with ⟨θ, hθ⟩,
  refine ⟨φ ⊔ θ, _⟩,
  ext,
  simp only [hφ, hθ, set.sup_eq_union, realize_not, realize_bounded_formula,
    bounded_formula.has_sup_sup, set.mem_union_eq, set.mem_set_of_eq],
  tauto,
end⟩

@[simp]
lemma is_definable.compl {s : set (α → M)} (hf : L.is_definable A s) :
  L.is_definable A sᶜ :=
⟨begin
  rcases hf.exists_formula with ⟨φ, hφ⟩,
  refine ⟨bd_not φ, _⟩,
  rw hφ,
  refl,
end⟩

@[simp]
lemma is_definable.sdiff {s t : set (α → M)} (hs : L.is_definable A s)
  (ht : L.is_definable A t) :
  L.is_definable A (s \ t) :=
hs.inter ht.compl

variables (L) (A) (α)

/-- Definable sets are subsets of finite Cartesian products of a structure such that membership is
  given by a first-order formula. -/
def definable_set := subtype (λ s : set (α → M), L.is_definable A s)

namespace definable_set
variables {A} {α}

instance : has_top (L.definable_set A α) := ⟨⟨⊤, is_definable_univ⟩⟩

instance : has_bot (L.definable_set A α) := ⟨⟨⊥, is_definable_empty⟩⟩

instance : inhabited (L.definable_set A α) := ⟨⊥⟩

instance : set_like (L.definable_set A α) (α → M) :=
{ coe := subtype.val,
  coe_injective' := subtype.val_injective }

@[simp]
lemma mem_top {x : α → M} : x ∈ (⊤ : L.definable_set A α) := set.mem_univ x

@[simp]
lemma coe_top : ((⊤ : L.definable_set A α) : set (α → M)) = ⊤ := rfl

@[simp]
lemma not_mem_bot {x : α → M} : ¬ x ∈ (⊥ : L.definable_set A α) := set.not_mem_empty x

@[simp]
lemma coe_bot : ((⊥ : L.definable_set A α) : set (α → M)) = ⊥ := rfl

instance : lattice (L.definable_set A α) :=
subtype.lattice (λ _ _, is_definable.union) (λ _ _, is_definable.inter)

lemma le_iff {s t : L.definable_set A α} : s ≤ t ↔ (s : set (α → M)) ≤ (t : set (α → M)) := iff.rfl

@[simp]
lemma coe_sup {s t : L.definable_set A α} : ((s ⊔ t : L.definable_set A α) : set (α → M)) = s ∪ t :=
rfl

@[simp]
lemma mem_sup {s t : L.definable_set A α} {x : α → M} : x ∈ s ⊔ t ↔ x ∈ s ∨ x ∈ t := iff.rfl

@[simp]
lemma coe_inf {s t : L.definable_set A α} : ((s ⊓ t : L.definable_set A α) : set (α → M)) = s ∩ t :=
rfl

@[simp]
lemma mem_inf {s t : L.definable_set A α} {x : α → M} : x ∈ s ⊓ t ↔ x ∈ s ∧ x ∈ t := iff.rfl

instance : bounded_order (L.definable_set A α) :=
{ bot_le := λ s x hx, false.elim hx,
  le_top := λ s x hx, set.mem_univ x,
  .. definable_set.has_top L,
  .. definable_set.has_bot L }

instance : distrib_lattice (L.definable_set A α) :=
{ le_sup_inf := begin
    intros s t u x,
    simp only [and_imp, set.mem_inter_eq, set_like.mem_coe, coe_sup, coe_inf, set.mem_union_eq,
      subtype.val_eq_coe],
    tauto,
  end,
  .. definable_set.lattice L }

/-- The complement of a definable set is also definable. -/
@[reducible] instance : has_compl (L.definable_set A α) :=
⟨λ ⟨s, hs⟩, ⟨sᶜ, hs.compl⟩⟩

@[simp]
lemma mem_compl {s : L.definable_set A α} {x : α → M} : x ∈ sᶜ ↔ ¬ x ∈ s :=
begin
  cases s with s hs,
  refl,
end

@[simp]
lemma coe_compl {s : L.definable_set A α} : ((sᶜ : L.definable_set A α) : set (α → M)) = sᶜ :=
begin
  ext,
  simp,
end

instance : boolean_algebra (L.definable_set A α) :=
{ sdiff := λ s t, s ⊓ tᶜ,
  sdiff_eq := λ s t, rfl,
  sup_inf_sdiff := λ ⟨s, hs⟩ ⟨t, ht⟩,
  begin
    apply le_antisymm;
    simp [le_iff],
  end,
  inf_inf_sdiff := λ ⟨s, hs⟩ ⟨t, ht⟩, begin
    rw eq_bot_iff,
    simp only [coe_compl, le_iff, coe_bot, coe_inf, subtype.coe_mk,
      set.le_eq_subset],
    intros x hx,
    simp only [set.mem_inter_eq, set.mem_compl_eq] at hx,
    tauto,
  end,
  inf_compl_le_bot := λ ⟨s, hs⟩, by simp [le_iff],
  top_le_sup_compl := λ ⟨s, hs⟩, by simp [le_iff],
  .. definable_set.has_compl L,
  .. definable_set.bounded_order L,
  .. definable_set.distrib_lattice L }

end definable_set
end definability

end language
end first_order
