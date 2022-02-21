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
* `first_order.language.is_definable` is defined so that `L.is_definable A s` indicates that the
set `s` of a finite cartesian power of `M` is definable with parameters in `A`.
* `first_order.language.is_definable₁` is defined so that `L.is_definable₁ A s` indicates that
`(s : set M)` is definable with parameters in `A`.
* `first_order.language.is_definable₂` is defined so that `L.is_definable₁ A s` indicates that
`(s : set (M × M))` is definable with parameters in `A`.
* A `first_order.language.definable_set` is defined so that `L.definable_set α A` is the boolean
  algebra of subsets of `α → M` defined by formulas with parameters in `A`.

## Main Results
* `L.definable_set M α` forms a `boolean_algebra`.
* `is_definable.image_comp_sum` shows that definability is closed under projections.

-/

universes u v w

namespace first_order
namespace language

variables {L : language.{u v}} {M : Type w} [L.Structure M] {A : set M}
open_locale first_order
open Structure set

/-! ### Definability -/

section definability

variables (L) {α : Type} [fintype α] {β : Type} [fintype β] (A)

/-- A subset of a finite Cartesian product of a structure is definable over a set `A` when
  membership in the set is given by a first-order formula with parameters from `A`. -/
structure is_definable (s : set (α → M)) : Prop :=
(exists_formula : ∃ (φ : L[[A]].formula α), s = set_of φ.realize)

variables {L} {A} {B : set M} {s : set (α → M)}

lemma is_definable.map_expansion {L' : language} [L'.Structure M] (h : L.is_definable A s)
  (φ : L →ᴸ L') [φ.is_expansion_on M] :
  L'.is_definable A s :=
begin
  obtain ⟨ψ, rfl⟩ := h,
  refine ⟨⟨(φ.add_constants A).on_formula ψ, _⟩⟩,
  ext x,
  simp only [mem_set_of_eq, Lhom.realize_on_formula],
end

lemma is_empty_definable_iff :
  L.is_definable ∅ s ↔ ∃ (φ : L.formula α), s = set_of φ.realize :=
begin
  split,
  { rintro ⟨φ, rfl⟩,
    refine ⟨(L.Lhom_trim_empty_constants (∅ : set M)).on_formula φ, _⟩,
    ext x,
    simp only [mem_set_of_eq, Lhom.realize_on_formula], },
  { rintro ⟨φ, rfl⟩,
    refine ⟨⟨(L.Lhom_with_constants (∅ : set M)).on_formula φ, _⟩⟩,
    ext x,
    simp only [mem_set_of_eq, Lhom.realize_on_formula], }
end

lemma is_definable_iff_empty_definable_with_params :
  L.is_definable A s ↔ L[[A]].is_definable ∅ s :=
begin
  rw is_empty_definable_iff,
  split,
  { rintro ⟨φ, rfl⟩,
    refine ⟨φ, rfl⟩ },
  { rintro ⟨φ, rfl⟩,
    refine ⟨⟨φ, rfl⟩⟩ },
end

lemma is_definable.mono (hAs : L.is_definable A s) (hAB : A ⊆ B) :
  L.is_definable B s :=
begin
  rw [is_definable_iff_empty_definable_with_params] at *,
  exact hAs.map_expansion (L.Lhom_constants_inclusion hAB),
end

@[simp]
lemma is_definable_empty : L.is_definable A (∅ : set (α → M)) :=
⟨⟨⊥, by {ext, simp} ⟩⟩

@[simp]
lemma is_definable_univ : L.is_definable A (univ : set (α → M)) :=
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
  rw [hφ, hθ, mem_set_of_eq, formula.realize_sup, mem_union_eq, mem_set_of_eq,
    mem_set_of_eq],
end⟩

lemma is_definable_finset_inf {ι : Type*} {f : Π (i : ι), set (α → M)}
  (hf : ∀ i, L.is_definable A (f i)) (s : finset ι) :
  L.is_definable A (s.inf f) :=
begin
  classical,
  refine finset.induction is_definable_univ (λ i s is h, _) s,
  rw finset.inf_insert,
  exact (hf i).inter h,
end

lemma is_definable_finset_sup {ι : Type*} {f : Π (i : ι), set (α → M)}
  (hf : ∀ i, L.is_definable A (f i)) (s : finset ι) :
  L.is_definable A (s.sup f) :=
begin
  classical,
  refine finset.induction is_definable_empty (λ i s is h, _) s,
  rw finset.sup_insert,
  exact (hf i).union h,
end

lemma is_definable_finset_bInter {ι : Type*} {f : Π (i : ι), set (α → M)}
  (hf : ∀ i, L.is_definable A (f i)) (s : finset ι) :
  L.is_definable A (⋂ i ∈ s, f i) :=
begin
  refine (congr rfl (le_antisymm _ _)).mp (is_definable_finset_inf hf s),
  { rw [le_eq_subset, subset_Inter₂_iff],
    simp_rw [← le_eq_subset],
    exact λ _, finset.inf_le },
  { rw finset.le_inf_iff,
    exact λ i is, bInter_subset_of_mem is }
end

lemma is_definable_finset_bUnion {ι : Type*} {f : Π (i : ι), set (α → M)}
  (hf : ∀ i, L.is_definable A (f i)) (s : finset ι) :
  L.is_definable A (⋃ i ∈ s, f i) :=
begin
  refine (congr rfl (le_antisymm _ _)).mp (is_definable_finset_sup hf s),
  { rw finset.sup_le_iff,
    exact λ i is, subset_bUnion_of_mem is },
  { rw [set.le_eq_subset, Union₂_subset_iff],
    simp_rw [← le_eq_subset],
    exact λ i is, finset.le_sup is }
end

@[simp]
lemma is_definable.compl {s : set (α → M)} (hf : L.is_definable A s) :
  L.is_definable A sᶜ :=
⟨begin
  rcases hf.exists_formula with ⟨φ, hφ⟩,
  refine ⟨φ.not, _⟩,
  rw hφ,
  refl,
end⟩

@[simp]
lemma is_definable.sdiff {s t : set (α → M)} (hs : L.is_definable A s)
  (ht : L.is_definable A t) :
  L.is_definable A (s \ t) :=
hs.inter ht.compl

lemma is_definable.preimage_comp (f : α → β) {s : set (α → M)}
  (h : L.is_definable A s) :
  L.is_definable A ((λ g : β → M, g ∘ f) ⁻¹' s) :=
begin
  obtain ⟨φ, rfl⟩ := h.exists_formula,
  refine ⟨⟨(φ.relabel f), _⟩⟩,
  ext,
  simp only [set.preimage_set_of_eq, mem_set_of_eq, formula.realize_relabel],
end

lemma is_definable.image_comp_equiv {s : set (β → M)}
  (h : L.is_definable A s) (f : α ≃ β) :
  L.is_definable A ((λ g : β → M, g ∘ f) '' s) :=
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

/-- This lemma is only intended as a helper for `is_definable.image_comp_sum_inl`. -/
lemma is_definable.image_comp_sum_inl_fin (m : ℕ) {s : set ((α ⊕ (fin m)) → M)}
  (h : L.is_definable A s) :
  L.is_definable A ((λ g : (α ⊕ (fin m)) → M, g ∘ sum.inl) '' s) :=
begin
  obtain ⟨φ, rfl⟩ := h.exists_formula,
  refine ⟨⟨(bounded_formula.relabel id φ).exs, _⟩⟩,
  ext x,
  simp only [set.mem_image, mem_set_of_eq, bounded_formula.realize_exs],
  split,
  { rintro ⟨y, hy, rfl⟩,
    refine ⟨y ∘ sum.inr, _⟩,
    rw bounded_formula.realize_relabel,
    refine (congr (congr rfl _) (funext fin_zero_elim)).mp hy,
    ext x,
    cases x,
    { simp },
    { rw [function.comp.right_id, sum.elim_inr, function.comp_apply,
        ← function.comp_apply y sum.inr],
      refine congr rfl _,
      ext,
      rw fin.coe_cast_add, } },
  { rintro ⟨y, hy⟩,
    refine ⟨sum.elim x y, _, sum.elim_comp_inl _ _⟩,
    rw bounded_formula.realize_relabel at hy,
    rw formula.realize,
    refine (congr (congr rfl (congr rfl _)) (funext fin_zero_elim)).mp hy,
    ext x,
    rw function.comp_apply,
    refine congr rfl _,
    ext,
    rw fin.coe_cast_add },
end

/-- Shows that definability is closed under general projections. -/
lemma is_definable.image_comp {s : set (β → M)} (h : L.is_definable A s)
  (f : α → β) :
  L.is_definable A ((λ g : β → M, g ∘ f) '' s) :=
begin
  classical,
  have h := h.image_comp_equiv (equiv.trans (equiv.sum_congr (_root_.equiv.refl _)
    (fintype.equiv_fin _).symm) (equiv.set.sum_compl (range f))),
  have h := (h.image_comp_sum_inl_fin _).preimage_comp (range_splitting f),
  have h' : L.is_definable A ({ x : α → M |
    ∀ a, x a = x (range_splitting f (range_factorization f a))}),
  { have h' : ∀ a, L.is_definable A {x : α → M | x a =
      x (range_splitting f (range_factorization f a))},
    { refine λ a, ⟨⟨(var a).equal (var (range_splitting f (range_factorization f a))), ext _⟩⟩,
      simp, },
    refine (congr rfl (ext _)).mp (is_definable_finset_bInter h' finset.univ),
    simp },
  refine (congr rfl (ext (λ x, _))).mp (h.inter h'),
  simp only [equiv.coe_trans, mem_inter_eq, mem_preimage, mem_image,
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

/-- A 1-dimensional version of `is_definable`, for `set M`. -/
def is_definable₁ (s : set M) : Prop := L.is_definable A { x : fin 1 → M | x 0 ∈ s }

/-- A 2-dimensional version of `is_definable`, for `set (M × M)`. -/
def is_definable₂ (s : set (M × M)) : Prop := L.is_definable A { x : fin 2 → M | (x 0, x 1) ∈ s }

variables (α)

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
lemma mem_top {x : α → M} : x ∈ (⊤ : L.definable_set A α) := mem_univ x

@[simp]
lemma coe_top : ((⊤ : L.definable_set A α) : set (α → M)) = ⊤ := rfl

@[simp]
lemma not_mem_bot {x : α → M} : ¬ x ∈ (⊥ : L.definable_set A α) := not_mem_empty x

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
end definability

end language
end first_order
