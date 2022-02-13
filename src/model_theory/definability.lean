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
* A `first_order.language.definable_set` is defined so that `L.definable_set α A` is the boolean
  algebra of subsets of `α → M` defined by formulas.

## Main Results
* `L.definable_set α A` forms a `boolean_algebra.

-/

universes u v

namespace first_order
namespace language

variables {L : language} {M : Type*} [L.Structure M]
open_locale first_order
open Structure

/-! ### Definability -/

section definability

variables (L) {α : Type} [fintype α]

/-- A subset of a finite Cartesian product of a structure is definable when membership in
  the set is given by a first-order formula. -/
structure is_definable (A : set M) (s : set (α → M)) : Prop :=
(exists_formula : ∃ {n : ℕ} (φ : L.partitioned_formula (fin n) α) (a : fin n → M)
  (ha : ∀ i, a i ∈ A), s = set_of (realize_partitioned_formula M φ a))

variables {L} {A B : set M} {s : set (α → M)}

lemma is_empty_definable_iff :
  L.is_definable ∅ s ↔ ∃ (φ : L.formula α), s = set_of (realize_formula M φ) :=
begin
  split,
  { rintro ⟨⟨n, φ, a, ha, rfl⟩⟩,
    cases n,
    { refine ⟨φ.relabel (sum.elim fin_zero_elim id), congr rfl (funext (λ v, _))⟩,
      rw [realize_partitioned_formula, realize_formula_relabel, sum.comp_elim,
        function.comp.right_id],
      exact congr rfl (congr (congr rfl (funext fin_zero_elim)) rfl) },
    { exact (set.not_mem_empty _ (ha 0)).elim } },
  { rintro ⟨φ, rfl⟩,
    refine ⟨⟨0, φ.relabel sum.inr, fin_zero_elim, fin_zero_elim, _⟩⟩,
    ext,
    simp only [set.mem_set_of_eq, realize_formula_relabel, sum.elim_comp_inr], }
end

lemma is_definable.mono (hAs : L.is_definable A s) (hAB : A ⊆ B) :
  L.is_definable B s :=
begin
  obtain ⟨n, φ, a, ha, rfl⟩ := hAs,
  exact ⟨⟨n, φ, a, λ i, hAB (ha i), rfl⟩⟩,
end

@[simp]
lemma is_definable_empty : L.is_definable A (∅ : set (α → M)) :=
is_definable.mono (is_empty_definable_iff.2 ⟨⊥, by { ext, simp }⟩) (set.empty_subset A)

@[simp]
lemma is_definable_univ : L.is_definable A (set.univ : set (α → M)) :=
is_definable.mono (is_empty_definable_iff.2 ⟨⊤, by { ext, simp }⟩) (set.empty_subset A)

@[simp]
lemma is_definable.inter {f g : set (α → M)} (hf : L.is_definable A f) (hg : L.is_definable A g) :
  L.is_definable A (f ∩ g) :=
⟨begin
  rcases hf.exists_formula with ⟨m, φ, a, ha, rfl⟩,
  rcases hg.exists_formula with ⟨n, ψ, b, hb, rfl⟩,
  refine ⟨m + n, (φ.relabel (sum.map (fin.cast_add n) id)) ⊓
    (ψ.relabel (sum.map (fin.nat_add m) id)), fin.append rfl a b, _, _⟩,
  { intro i,
    simp_rw [fin.append],
    split_ifs,
    { exact ha _ },
    { exact hb _ } },
  { ext,
    simp only [set.mem_inter_eq, set.mem_set_of_eq, realize_formula],
    rw [realize_inf, realize_bounded_formula_relabel, realize_bounded_formula_relabel],
    simp }
end⟩

@[simp]
lemma is_definable.union {f g : set (α → M)} (hf : L.is_definable A f) (hg : L.is_definable A g) :
  L.is_definable A (f ∪ g) :=
⟨begin
  rcases hf.exists_formula with ⟨m, φ, a, ha, rfl⟩,
  rcases hg.exists_formula with ⟨n, ψ, b, hb, rfl⟩,
  refine ⟨m + n, (φ.relabel (sum.map (fin.cast_add n) id)) ⊔
    (ψ.relabel (sum.map (fin.nat_add m) id)), fin.append rfl a b, _, _⟩,
  { intro i,
    simp_rw [fin.append],
    split_ifs,
    { exact ha _ },
    { exact hb _ } },
  { ext,
    simp only [set.mem_union_eq, set.mem_set_of_eq, realize_formula],
    rw [realize_sup, realize_bounded_formula_relabel, realize_bounded_formula_relabel],
    simp }
end⟩

@[simp]
lemma is_definable.compl {s : set (α → M)} (hf : L.is_definable A s) :
  L.is_definable A sᶜ :=
⟨begin
  rcases hf.exists_formula with ⟨n, φ, a, ha, rfl⟩,
  exact ⟨n, bd_not φ, a, ha, rfl⟩
end⟩

@[simp]
lemma is_definable.sdiff {s t : set (α → M)} (hs : L.is_definable A s)
  (ht : L.is_definable A t) :
  L.is_definable A (s \ t) :=
hs.inter ht.compl

variables (L) {M} (α) (A)

/-- Definable sets are subsets of finite Cartesian products of a structure such that membership is
  given by a first-order formula. -/
def definable_set := subtype (λ s : set (α → M), L.is_definable A s)

namespace definable_set
variables {L} {M} {α} {A}

instance : has_top (L.definable_set α A) := ⟨⟨⊤, is_definable_univ⟩⟩

instance : has_bot (L.definable_set α A) := ⟨⟨⊥, is_definable_empty⟩⟩

instance : inhabited (L.definable_set α A) := ⟨⊥⟩

instance : set_like (L.definable_set α A) (α → M) :=
{ coe := subtype.val,
  coe_injective' := subtype.val_injective }

@[simp]
lemma mem_top {x : α → M} : x ∈ (⊤ : L.definable_set α A) := set.mem_univ x

@[simp]
lemma coe_top : ((⊤ : L.definable_set α A) : set (α → M)) = ⊤ := rfl

@[simp]
lemma not_mem_bot {x : α → M} : ¬ x ∈ (⊥ : L.definable_set α A) := set.not_mem_empty x

@[simp]
lemma coe_bot : ((⊥ : L.definable_set α A) : set (α → M)) = ⊥ := rfl

instance : lattice (L.definable_set α A) :=
subtype.lattice (λ _ _, is_definable.union) (λ _ _, is_definable.inter)

lemma le_iff {s t : L.definable_set α A} : s ≤ t ↔ (s : set (α → M)) ≤ (t : set (α → M)) := iff.rfl

@[simp]
lemma coe_sup {s t : L.definable_set α A} : ((s ⊔ t : L.definable_set α A) : set (α → M)) = s ∪ t :=
rfl

@[simp]
lemma mem_sup {s t : L.definable_set α A} {x : α → M} : x ∈ s ⊔ t ↔ x ∈ s ∨ x ∈ t := iff.rfl

@[simp]
lemma coe_inf {s t : L.definable_set α A} : ((s ⊓ t : L.definable_set α A) : set (α → M)) = s ∩ t :=
rfl

@[simp]
lemma mem_inf {s t : L.definable_set α A} {x : α → M} : x ∈ s ⊓ t ↔ x ∈ s ∧ x ∈ t := iff.rfl

instance : bounded_order (L.definable_set α A) :=
{ bot_le := λ s x hx, false.elim hx,
  le_top := λ s x hx, set.mem_univ x,
  .. definable_set.has_top,
  .. definable_set.has_bot }

instance : distrib_lattice (L.definable_set α A) :=
{ le_sup_inf := begin
    intros s t u x,
    simp only [and_imp, set.mem_inter_eq, set_like.mem_coe, coe_sup, coe_inf, set.mem_union_eq,
      subtype.val_eq_coe],
    tauto,
  end,
  .. definable_set.lattice }

/-- The complement of a definable set is also definable. -/
@[reducible] instance : has_compl (L.definable_set α A) :=
⟨λ ⟨s, hs⟩, ⟨sᶜ, hs.compl⟩⟩

@[simp]
lemma mem_compl {s : L.definable_set α A} {x : α → M} : x ∈ sᶜ ↔ ¬ x ∈ s :=
begin
  cases s with s hs,
  refl,
end

@[simp]
lemma coe_compl {s : L.definable_set α A} : ((sᶜ : L.definable_set α A) : set (α → M)) = sᶜ :=
begin
  ext,
  simp,
end

instance : boolean_algebra (L.definable_set α A) :=
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
  .. definable_set.has_compl,
  .. definable_set.bounded_order,
  .. definable_set.distrib_lattice }

end definable_set
end definability

end language
end first_order
