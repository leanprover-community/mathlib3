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
* `first_order.language.definable` is defined so that `L.definable A s` indicates that the
set `s` of a finite cartesian power of `M` is definable with parameters in `A`.
* `first_order.language.definable₁` is defined so that `L.definable₁ A s` indicates that
`(s : set M)` is definable with parameters in `A`.
* `first_order.language.definable₂` is defined so that `L.definable₂ A s` indicates that
`(s : set (M × M))` is definable with parameters in `A`.
* A `first_order.language.definable_set` is defined so that `L.definable_set α A` is the boolean
  algebra of subsets of `α → M` defined by formulas with parameters in `A`.

## Main Results
* `L.definable_set M α` forms a `boolean_algebra`.
* `definable.image_comp_sum` shows that definability is closed under projections.

-/

universes u v w

namespace first_order
namespace language

variables (L : language.{u v}) {M : Type w} [L.Structure M] (A : set M)
open_locale first_order
open Structure set

variables {α : Type} [fintype α] {β : Type} [fintype β]

/-- A subset of a finite Cartesian product of a structure is definable over a set `A` when
  membership in the set is given by a first-order formula with parameters from `A`. -/
structure definable (s : set (α → M)) : Prop :=
(exists_formula : ∃ (φ : L[[A]].formula α), s = set_of φ.realize)

variables {L} {A} {B : set M} {s : set (α → M)}


@[simp]
lemma definable_empty : L.definable A (∅ : set (α → M)) :=
⟨⟨⊥, by {ext, simp} ⟩⟩

@[simp]
lemma definable_univ : L.definable A (univ : set (α → M)) :=
⟨⟨⊤, by {ext, simp} ⟩⟩

@[simp]
lemma definable.inter {f g : set (α → M)} (hf : L.definable A f) (hg : L.definable A g) :
  L.definable A (f ∩ g) :=
⟨begin
  rcases hf.exists_formula with ⟨φ, rfl⟩,
  rcases hg.exists_formula with ⟨θ, rfl⟩,
  refine ⟨φ ⊓ θ, _⟩,
  ext,
  simp,
end⟩

@[simp]
lemma definable.union {f g : set (α → M)} (hf : L.definable A f) (hg : L.definable A g) :
  L.definable A (f ∪ g) :=
⟨begin
  rcases hf.exists_formula with ⟨φ, hφ⟩,
  rcases hg.exists_formula with ⟨θ, hθ⟩,
  refine ⟨φ ⊔ θ, _⟩,
  ext,
  rw [hφ, hθ, mem_set_of_eq, formula.realize_sup, mem_union_eq, mem_set_of_eq,
    mem_set_of_eq],
end⟩

lemma definable_finset_inf {ι : Type*} {f : Π (i : ι), set (α → M)}
  (hf : ∀ i, L.definable A (f i)) (s : finset ι) :
  L.definable A (s.inf f) :=
begin
  classical,
  refine finset.induction definable_univ (λ i s is h, _) s,
  rw finset.inf_insert,
  exact (hf i).inter h,
end

lemma definable_finset_sup {ι : Type*} {f : Π (i : ι), set (α → M)}
  (hf : ∀ i, L.definable A (f i)) (s : finset ι) :
  L.definable A (s.sup f) :=
begin
  classical,
  refine finset.induction definable_empty (λ i s is h, _) s,
  rw finset.sup_insert,
  exact (hf i).union h,
end

lemma definable_finset_bInter {ι : Type*} {f : Π (i : ι), set (α → M)}
  (hf : ∀ i, L.definable A (f i)) (s : finset ι) :
  L.definable A (⋂ i ∈ s, f i) :=
begin
  rw ← finset.inf_set_eq_bInter,
  exact definable_finset_inf hf s,
end

lemma definable_finset_bUnion {ι : Type*} {f : Π (i : ι), set (α → M)}
  (hf : ∀ i, L.definable A (f i)) (s : finset ι) :
  L.definable A (⋃ i ∈ s, f i) :=
begin
  rw ← finset.sup_set_eq_bUnion,
  exact definable_finset_sup hf s,
end

@[simp]
lemma definable.compl {s : set (α → M)} (hf : L.definable A s) :
  L.definable A sᶜ :=
⟨begin
  rcases hf.exists_formula with ⟨φ, hφ⟩,
  refine ⟨φ.not, _⟩,
  rw hφ,
  refl,
end⟩

@[simp]
lemma definable.sdiff {s t : set (α → M)} (hs : L.definable A s)
  (ht : L.definable A t) :
  L.definable A (s \ t) :=
hs.inter ht.compl

lemma definable.preimage_comp (f : α → β) {s : set (α → M)}
  (h : L.definable A s) :
  L.definable A ((λ g : β → M, g ∘ f) ⁻¹' s) :=
begin
  obtain ⟨φ, rfl⟩ := h.exists_formula,
  refine ⟨⟨(φ.relabel f), _⟩⟩,
  ext,
  simp only [set.preimage_set_of_eq, mem_set_of_eq, formula.realize_relabel],
end

lemma definable.image_comp_equiv {s : set (β → M)}
  (h : L.definable A s) (f : α ≃ β) :
  L.definable A ((λ g : β → M, g ∘ f) '' s) :=
begin
  refine (congr rfl _).mp (h.preimage_comp f.symm),
  rw image_eq_preimage_of_inverse,
  { intro i,
    ext b,
    simp },
  { intro i,
    ext a,
    simp }
end

variables (L) {M} (A)

/-- A 1-dimensional version of `definable`, for `set M`. -/
def definable₁ (s : set M) : Prop := L.definable A { x : fin 1 → M | x 0 ∈ s }

/-- A 2-dimensional version of `definable`, for `set (M × M)`. -/
def definable₂ (s : set (M × M)) : Prop := L.definable A { x : fin 2 → M | (x 0, x 1) ∈ s }

variables (α)

/-- Definable sets are subsets of finite Cartesian products of a structure such that membership is
  given by a first-order formula. -/
def definable_set := subtype (λ s : set (α → M), L.definable A s)

namespace definable_set
variables {A} {α}

instance : has_top (L.definable_set A α) := ⟨⟨⊤, definable_univ⟩⟩

instance : has_bot (L.definable_set A α) := ⟨⟨⊥, definable_empty⟩⟩

instance : inhabited (L.definable_set A α) := ⟨⊥⟩

instance : set_like (L.definable_set A α) (α → M) :=
{ coe := subtype.val,
  coe_injective' := subtype.val_injective }

@[simp]
lemma mem_top {x : α → M} : x ∈ (⊤ : L.definable_set A α) := mem_univ x

@[simp]
lemma coe_top : ((⊤ : L.definable_set A α) : set (α → M)) = ⊤ := rfl

@[simp]
lemma not_mem_bot {x : α → M} : ¬ x ∈ (⊥ : L.definable_set A α) := not_mem_empty x

@[simp]
lemma coe_bot : ((⊥ : L.definable_set A α) : set (α → M)) = ⊥ := rfl

instance : lattice (L.definable_set A α) :=
subtype.lattice (λ _ _, definable.union) (λ _ _, definable.inter)

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
  le_top := λ s x hx, mem_univ x,
  .. definable_set.has_top L,
  .. definable_set.has_bot L }

instance : distrib_lattice (L.definable_set A α) :=
{ le_sup_inf := begin
    intros s t u x,
    simp only [and_imp, mem_inter_eq, set_like.mem_coe, coe_sup, coe_inf, mem_union_eq,
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
      le_eq_subset],
    intros x hx,
    simp only [set.mem_inter_eq, mem_compl_eq] at hx,
    tauto,
  end,
  inf_compl_le_bot := λ ⟨s, hs⟩, by simp [le_iff],
  top_le_sup_compl := λ ⟨s, hs⟩, by simp [le_iff],
  .. definable_set.has_compl L,
  .. definable_set.bounded_order L,
  .. definable_set.distrib_lattice L }

end definable_set

end language
end first_order
