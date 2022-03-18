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
* `set.definable` is defined so that `A.definable L s` indicates that the
set `s` of a finite cartesian power of `M` is definable with parameters in `A`.
* `set.definable₁` is defined so that `A.definable₁ L s` indicates that
`(s : set M)` is definable with parameters in `A`.
* `set.definable₂` is defined so that `A.definable₂ L s` indicates that
`(s : set (M × M))` is definable with parameters in `A`.
* A `set.definable_set` is defined so that `A.definable_set L α` is the boolean
  algebra of subsets of `α → M` defined by formulas with parameters in `A`.

## Main Results
* `A.definable_set L α` forms a `boolean_algebra`.

-/

universes u v w

namespace set

variables {M : Type w} (A : set M) (L : first_order.language.{u v}) [L.Structure M]
open_locale first_order
open first_order.language first_order.language.Structure

variables {α : Type} {β : Type}

/-- A subset of a finite Cartesian product of a structure is definable over a set `A` when
  membership in the set is given by a first-order formula with parameters from `A`. -/
def definable (s : set (α → M)) : Prop :=
∃ (φ : L[[A]].formula α), s = set_of φ.realize

variables {L} {A} {B : set M} {s : set (α → M)}

@[simp]
lemma definable_empty : A.definable L (∅ : set (α → M)) :=
⟨⊥, by {ext, simp} ⟩

@[simp]
lemma definable_univ : A.definable L (univ : set (α → M)) :=
⟨⊤, by {ext, simp} ⟩

@[simp]
lemma definable.inter {f g : set (α → M)} (hf : A.definable L f) (hg : A.definable L g) :
  A.definable L (f ∩ g) :=
begin
  rcases hf with ⟨φ, rfl⟩,
  rcases hg with ⟨θ, rfl⟩,
  refine ⟨φ ⊓ θ, _⟩,
  ext,
  simp,
end

@[simp]
lemma definable.union {f g : set (α → M)} (hf : A.definable L f) (hg : A.definable L g) :
  A.definable L (f ∪ g) :=
begin
  rcases hf with ⟨φ, hφ⟩,
  rcases hg with ⟨θ, hθ⟩,
  refine ⟨φ ⊔ θ, _⟩,
  ext,
  rw [hφ, hθ, mem_set_of_eq, formula.realize_sup, mem_union_eq, mem_set_of_eq,
    mem_set_of_eq],
end

lemma definable_finset_inf {ι : Type*} {f : Π (i : ι), set (α → M)}
  (hf : ∀ i, A.definable L (f i)) (s : finset ι) :
  A.definable L (s.inf f) :=
begin
  classical,
  refine finset.induction definable_univ (λ i s is h, _) s,
  rw finset.inf_insert,
  exact (hf i).inter h,
end

lemma definable_finset_sup {ι : Type*} {f : Π (i : ι), set (α → M)}
  (hf : ∀ i, A.definable L (f i)) (s : finset ι) :
  A.definable L (s.sup f) :=
begin
  classical,
  refine finset.induction definable_empty (λ i s is h, _) s,
  rw finset.sup_insert,
  exact (hf i).union h,
end

lemma definable_finset_bInter {ι : Type*} {f : Π (i : ι), set (α → M)}
  (hf : ∀ i, A.definable L (f i)) (s : finset ι) :
  A.definable L (⋂ i ∈ s, f i) :=
begin
  rw ← finset.inf_set_eq_bInter,
  exact definable_finset_inf hf s,
end

lemma definable_finset_bUnion {ι : Type*} {f : Π (i : ι), set (α → M)}
  (hf : ∀ i, A.definable L (f i)) (s : finset ι) :
  A.definable L (⋃ i ∈ s, f i) :=
begin
  rw ← finset.sup_set_eq_bUnion,
  exact definable_finset_sup hf s,
end

@[simp]
lemma definable.compl {s : set (α → M)} (hf : A.definable L s) :
  A.definable L sᶜ :=
begin
  rcases hf with ⟨φ, hφ⟩,
  refine ⟨φ.not, _⟩,
  rw hφ,
  refl,
end

@[simp]
lemma definable.sdiff {s t : set (α → M)} (hs : A.definable L s)
  (ht : A.definable L t) :
  A.definable L (s \ t) :=
hs.inter ht.compl

lemma definable.preimage_comp (f : α → β) {s : set (α → M)}
  (h : A.definable L s) :
  A.definable L ((λ g : β → M, g ∘ f) ⁻¹' s) :=
begin
  obtain ⟨φ, rfl⟩ := h,
  refine ⟨(φ.relabel f), _⟩,
  ext,
  simp only [set.preimage_set_of_eq, mem_set_of_eq, formula.realize_relabel],
end

lemma definable.image_comp_equiv {s : set (β → M)}
  (h : A.definable L s) (f : α ≃ β) :
  A.definable L ((λ g : β → M, g ∘ f) '' s) :=
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
def definable₁ (s : set M) : Prop := A.definable L { x : fin 1 → M | x 0 ∈ s }

/-- A 2-dimensional version of `definable`, for `set (M × M)`. -/
def definable₂ (s : set (M × M)) : Prop := A.definable L { x : fin 2 → M | (x 0, x 1) ∈ s }

variable (α)

/-- Definable sets are subsets of finite Cartesian products of a structure such that membership is
  given by a first-order formula. -/
def definable_set := subtype (λ s : set (α → M), A.definable L s)

namespace definable_set
variables {L} {A} {α}

instance : has_top (A.definable_set L α) := ⟨⟨⊤, definable_univ⟩⟩

instance : has_bot (A.definable_set L α) := ⟨⟨⊥, definable_empty⟩⟩

instance : inhabited (A.definable_set L α) := ⟨⊥⟩

instance : set_like (A.definable_set L α) (α → M) :=
{ coe := subtype.val,
  coe_injective' := subtype.val_injective }

@[simp]
lemma mem_top {x : α → M} : x ∈ (⊤ : A.definable_set L α) := mem_univ x

@[simp]
lemma coe_top : ((⊤ : A.definable_set L α) : set (α → M)) = ⊤ := rfl

@[simp]
lemma not_mem_bot {x : α → M} : ¬ x ∈ (⊥ : A.definable_set L α) := not_mem_empty x

@[simp]
lemma coe_bot : ((⊥ : A.definable_set L α) : set (α → M)) = ⊥ := rfl

instance : lattice (A.definable_set L α) :=
subtype.lattice (λ _ _, definable.union) (λ _ _, definable.inter)

lemma le_iff {s t : A.definable_set L α} : s ≤ t ↔ (s : set (α → M)) ≤ (t : set (α → M)) := iff.rfl

@[simp]
lemma coe_sup {s t : A.definable_set L α} : ((s ⊔ t : A.definable_set L α) : set (α → M)) = s ∪ t :=
rfl

@[simp]
lemma mem_sup {s t : A.definable_set L α} {x : α → M} : x ∈ s ⊔ t ↔ x ∈ s ∨ x ∈ t := iff.rfl

@[simp]
lemma coe_inf {s t : A.definable_set L α} : ((s ⊓ t : A.definable_set L α) : set (α → M)) = s ∩ t :=
rfl

@[simp]
lemma mem_inf {s t : A.definable_set L α} {x : α → M} : x ∈ s ⊓ t ↔ x ∈ s ∧ x ∈ t := iff.rfl

instance : bounded_order (A.definable_set L α) :=
{ bot_le := λ s x hx, false.elim hx,
  le_top := λ s x hx, mem_univ x,
  .. definable_set.has_top,
  .. definable_set.has_bot }

instance : distrib_lattice (A.definable_set L α) :=
{ le_sup_inf := begin
    intros s t u x,
    simp only [and_imp, mem_inter_eq, set_like.mem_coe, coe_sup, coe_inf, mem_union_eq,
      subtype.val_eq_coe],
    tauto,
  end,
  .. definable_set.lattice }

/-- The complement of a definable set is also definable. -/
@[reducible] instance : has_compl (A.definable_set L α) :=
⟨λ ⟨s, hs⟩, ⟨sᶜ, hs.compl⟩⟩

@[simp]
lemma mem_compl {s : A.definable_set L α} {x : α → M} : x ∈ sᶜ ↔ ¬ x ∈ s :=
begin
  cases s with s hs,
  refl,
end

@[simp]
lemma coe_compl {s : A.definable_set L α} : ((sᶜ : A.definable_set L α) : set (α → M)) = sᶜ :=
begin
  ext,
  simp,
end

instance : boolean_algebra (A.definable_set L α) :=
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
  .. definable_set.has_compl,
  .. definable_set.bounded_order,
  .. definable_set.distrib_lattice }

end definable_set

end set
