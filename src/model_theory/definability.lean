/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import data.set_like.basic
import model_theory.semantics

/-!
# Definable Sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
This file defines what it means for a set over a first-order structure to be definable.

## Main Definitions
* `set.definable` is defined so that `A.definable L s` indicates that the
set `s` of a finite cartesian power of `M` is definable with parameters in `A`.
* `set.definable₁` is defined so that `A.definable₁ L s` indicates that
`(s : set M)` is definable with parameters in `A`.
* `set.definable₂` is defined so that `A.definable₂ L s` indicates that
`(s : set (M × M))` is definable with parameters in `A`.
* A `first_order.language.definable_set` is defined so that `L.definable_set A α` is the boolean
  algebra of subsets of `α → M` defined by formulas with parameters in `A`.

## Main Results
* `L.definable_set A α` forms a `boolean_algebra`
* `set.definable.image_comp` shows that definability is closed under projections in finite
  dimensions.

-/

universes u v w

namespace set

variables {M : Type w} (A : set M) (L : first_order.language.{u v}) [L.Structure M]
open_locale first_order
open first_order.language first_order.language.Structure

variables {α : Type*} {β : Type*}

/-- A subset of a finite Cartesian product of a structure is definable over a set `A` when
  membership in the set is given by a first-order formula with parameters from `A`. -/
def definable (s : set (α → M)) : Prop :=
∃ (φ : L[[A]].formula α), s = set_of φ.realize

variables {L} {A} {B : set M} {s : set (α → M)}

lemma definable.map_expansion {L' : first_order.language} [L'.Structure M] (h : A.definable L s)
  (φ : L →ᴸ L') [φ.is_expansion_on M] :
  A.definable L' s :=
begin
  obtain ⟨ψ, rfl⟩ := h,
  refine ⟨(φ.add_constants A).on_formula ψ, _⟩,
  ext x,
  simp only [mem_set_of_eq, Lhom.realize_on_formula],
end

lemma empty_definable_iff :
  (∅ : set M).definable L s ↔ ∃ (φ : L.formula α), s = set_of φ.realize :=
begin
  rw [definable, equiv.exists_congr_left (Lequiv.add_empty_constants L (∅ : set M)).on_formula],
  simp,
end

lemma definable_iff_empty_definable_with_params :
  A.definable L s ↔ (∅ : set M).definable (L[[A]]) s :=
empty_definable_iff.symm

lemma definable.mono (hAs : A.definable L s) (hAB : A ⊆ B) :
  B.definable L s :=
begin
  rw [definable_iff_empty_definable_with_params] at *,
  exact hAs.map_expansion (L.Lhom_with_constants_map (set.inclusion hAB)),
end

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
  rw [hφ, hθ, mem_set_of_eq, formula.realize_sup, mem_union, mem_set_of_eq,
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
    simp only [function.comp_app, equiv.apply_symm_apply], },
  { intro i,
    ext a,
    simp }
end

/-- This lemma is only intended as a helper for `definable.image_comp. -/
lemma definable.image_comp_sum_inl_fin (m : ℕ) {s : set ((α ⊕ fin m) → M)}
  (h : A.definable L s) :
  A.definable L ((λ g : (α ⊕ fin m) → M, g ∘ sum.inl) '' s) :=
begin
  obtain ⟨φ, rfl⟩ := h,
  refine ⟨(bounded_formula.relabel id φ).exs, _⟩,
  ext x,
  simp only [set.mem_image, mem_set_of_eq, bounded_formula.realize_exs,
    bounded_formula.realize_relabel, function.comp.right_id, fin.cast_add_zero, fin.cast_refl],
  split,
  { rintro ⟨y, hy, rfl⟩,
    exact ⟨y ∘ sum.inr,
      (congr (congr rfl (sum.elim_comp_inl_inr y).symm) (funext fin_zero_elim)).mp hy⟩ },
  { rintro ⟨y, hy⟩,
    exact ⟨sum.elim x y, (congr rfl (funext fin_zero_elim)).mp hy, sum.elim_comp_inl _ _⟩, },
end

/-- Shows that definability is closed under finite projections. -/
lemma definable.image_comp_embedding {s : set (β → M)} (h : A.definable L s)
  (f : α ↪ β) [finite β] :
  A.definable L ((λ g : β → M, g ∘ f) '' s) :=
begin
  classical,
  casesI nonempty_fintype β,
  refine (congr rfl (ext (λ x, _))).mp (((h.image_comp_equiv
    (equiv.set.sum_compl (range f))).image_comp_equiv (equiv.sum_congr
    (equiv.of_injective f f.injective) (fintype.equiv_fin _).symm)).image_comp_sum_inl_fin _),
  simp only [mem_preimage, mem_image, exists_exists_and_eq_and],
  refine exists_congr (λ y, and_congr_right (λ ys, eq.congr_left (funext (λ a, _)))),
  simp,
end

/-- Shows that definability is closed under finite projections. -/
lemma definable.image_comp {s : set (β → M)} (h : A.definable L s)
  (f : α → β) [finite α] [finite β] :
  A.definable L ((λ g : β → M, g ∘ f) '' s) :=
begin
  classical,
  casesI nonempty_fintype α,
  casesI nonempty_fintype β,
  have h := (((h.image_comp_equiv (equiv.set.sum_compl (range f))).image_comp_equiv
    (equiv.sum_congr (_root_.equiv.refl _)
    (fintype.equiv_fin _).symm)).image_comp_sum_inl_fin _).preimage_comp (range_splitting f),
  have h' : A.definable L ({ x : α → M |
    ∀ a, x a = x (range_splitting f (range_factorization f a))}),
  { have h' : ∀ a, A.definable L {x : α → M | x a =
      x (range_splitting f (range_factorization f a))},
    { refine λ a, ⟨(var a).equal (var (range_splitting f (range_factorization f a))), ext _⟩,
      simp, },
    refine (congr rfl (ext _)).mp (definable_finset_bInter h' finset.univ),
    simp },
  refine (congr rfl (ext (λ x, _))).mp (h.inter h'),
  simp only [equiv.coe_trans, mem_inter_iff, mem_preimage, mem_image,
    exists_exists_and_eq_and, mem_set_of_eq],
  split,
  { rintro ⟨⟨y, ys, hy⟩, hx⟩,
    refine ⟨y, ys, _⟩,
    ext a,
    rw [hx a, ← function.comp_apply x, ← hy],
    simp, },
  { rintro ⟨y, ys, rfl⟩,
    refine ⟨⟨y, ys, _⟩, λ a, _⟩,
    { ext,
      simp [set.apply_range_splitting f] },
    { rw [function.comp_apply, function.comp_apply, apply_range_splitting f,
        range_factorization_coe], }}
end

variables (L) {M} (A)

/-- A 1-dimensional version of `definable`, for `set M`. -/
def definable₁ (s : set M) : Prop := A.definable L { x : fin 1 → M | x 0 ∈ s }

/-- A 2-dimensional version of `definable`, for `set (M × M)`. -/
def definable₂ (s : set (M × M)) : Prop := A.definable L { x : fin 2 → M | (x 0, x 1) ∈ s }

end set

namespace first_order
namespace language
open set

variables (L : first_order.language.{u v}) {M : Type w} [L.Structure M] (A : set M) (α : Type*)

/-- Definable sets are subsets of finite Cartesian products of a structure such that membership is
  given by a first-order formula. -/
def definable_set := { s : set (α → M) // A.definable L s}

namespace definable_set
variables {L A α} {s t : L.definable_set A α} {x : α → M}

instance : set_like (L.definable_set A α) (α → M) :=
{ coe := subtype.val,
  coe_injective' := subtype.val_injective }

instance : has_top (L.definable_set A α) := ⟨⟨⊤, definable_univ⟩⟩
instance : has_bot (L.definable_set A α) := ⟨⟨⊥, definable_empty⟩⟩
instance : has_sup (L.definable_set A α) := ⟨λ s t, ⟨s ∪ t, s.2.union t.2⟩⟩
instance : has_inf (L.definable_set A α) := ⟨λ s t, ⟨s ∩ t, s.2.inter t.2⟩⟩
instance : has_compl (L.definable_set A α) := ⟨λ s, ⟨sᶜ, s.2.compl⟩⟩
instance : has_sdiff (L.definable_set A α) := ⟨λ s t, ⟨s \ t, s.2.sdiff t.2⟩⟩

instance : inhabited (L.definable_set A α) := ⟨⊥⟩

lemma le_iff : s ≤ t ↔ (s : set (α → M)) ≤ (t : set (α → M)) := iff.rfl

@[simp] lemma mem_top : x ∈ (⊤ : L.definable_set A α) := mem_univ x
@[simp] lemma not_mem_bot {x : α → M} : ¬ x ∈ (⊥ : L.definable_set A α) := not_mem_empty x
@[simp] lemma mem_sup : x ∈ s ⊔ t ↔ x ∈ s ∨ x ∈ t := iff.rfl
@[simp] lemma mem_inf : x ∈ s ⊓ t ↔ x ∈ s ∧ x ∈ t := iff.rfl
@[simp] lemma mem_compl : x ∈ sᶜ ↔ ¬ x ∈ s := iff.rfl
@[simp] lemma mem_sdiff : x ∈ s \ t ↔ x ∈ s ∧ ¬ x ∈ t := iff.rfl

@[simp, norm_cast] lemma coe_top : ((⊤ : L.definable_set A α) : set (α → M)) = univ := rfl
@[simp, norm_cast] lemma coe_bot : ((⊥ : L.definable_set A α) : set (α → M)) = ∅ := rfl
@[simp, norm_cast] lemma coe_sup (s t : L.definable_set A α) : (↑(s ⊔ t) : set (α → M)) = s ∪ t :=
rfl
@[simp, norm_cast] lemma coe_inf (s t : L.definable_set A α) : (↑(s ⊓ t) : set (α → M)) = s ∩ t :=
rfl
@[simp, norm_cast] lemma coe_compl (s : L.definable_set A α) : (↑(sᶜ) : set (α → M)) = sᶜ := rfl
@[simp, norm_cast] lemma coe_sdiff (s t : L.definable_set A α) : (↑(s \ t) : set (α → M)) = s \ t :=
rfl

instance : boolean_algebra (L.definable_set A α) :=
subtype.coe_injective.boolean_algebra _ coe_sup coe_inf coe_top coe_bot coe_compl coe_sdiff

end definable_set
end language
end first_order
