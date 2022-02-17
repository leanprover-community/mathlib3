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
* A `first_order.language.is_definable` is defined so that `L.is_definable A s` indicates that the
set `s` of a finite cartesian power of `M` is definable with parameters in `A`.
* A `first_order.language.is_definable_set` is defined so that `L.is_definable A s` indicates that
`(s : set M)` is definable with parameters in `A`.
* A `first_order.language.definable_set` is defined so that `L.definable_set α A` is the boolean
  algebra of subsets of `α → M` defined by formulas with parameters in `A`.

## Main Results
* `L.definable_set α A` forms a `boolean_algebra`.

-/

namespace first_order
namespace language

variables (L : language) {M : Type*} [L.Structure M] {α β : Type} [fintype α] [fintype β]
open_locale first_order
open Structure

/-- A subset of a finite Cartesian product of a structure is definable when membership in
  the set is given by a first-order formula. -/
structure is_definable (A : set M) (s : set (α → M)) : Prop :=
(exists_formula : ∃ {n : ℕ} (φ : L.partitioned_formula (fin n) α) (a : fin n → M)
  (ha : ∀ i, a i ∈ A), s = set_of (realize_partitioned_formula M φ a))

variables {L} {A B : set M} {s : set (α → M)}

lemma is_definable_of {A : set M} {s : set (α → M)} {β : Type} [fintype β]
  (φ : L.partitioned_formula β α) (b : β → M) (hb : ∀ i, b i ∈ A)
  (h : ∀ x, x ∈ s ↔ realize_partitioned_formula M φ b x) :
  L.is_definable A s :=
⟨⟨fintype.card β, φ.relabel (sum.map (fintype.equiv_fin β) id), (b ∘ (fintype.equiv_fin β).symm),
  λ i, hb _,
begin
  ext,
  simp only [h, realize_partitioned_formula, set.mem_set_of_eq, realize_formula_relabel,
    sum.elim_comp_map, function.comp.right_id],
  rw [function.comp.assoc, equiv.symm_comp_self, function.comp.right_id],
end⟩⟩

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
begin
  rcases hf.exists_formula with ⟨m, φ, a, ha, rfl⟩,
  rcases hg.exists_formula with ⟨n, ψ, b, hb, rfl⟩,
  refine is_definable_of (φ.relabel (sum.map sum.inl id) ⊓ ψ.relabel (sum.map sum.inr id))
    (sum.elim a b) (λ i, sum.cases_on i ha hb) (λ x, _),
  simp only [set.mem_inter_eq, set.mem_set_of_eq, realize_partitioned_formula],
  rw [formula.realize_inf, realize_formula_relabel, realize_formula_relabel],
  simp,
end

@[simp]
lemma is_definable.union {f g : set (α → M)} (hf : L.is_definable f) (hg : L.is_definable g) :
  L.is_definable (f ∪ g) :=
⟨begin
  rcases hf.exists_formula with ⟨φ, hφ⟩,
  rcases hg.exists_formula with ⟨θ, hθ⟩,
  refine ⟨φ ⊔ θ, _⟩,
  ext,
  rw [hφ, hθ, set.mem_set_of_eq, formula.realize_sup, set.mem_union_eq, set.mem_set_of_eq,
    set.mem_set_of_eq],
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

lemma is_definable.preimage_comp (f : α → β) {s : set (α → M)} (h : L.is_definable A s) :
  L.is_definable A ((λ g : β → M, g ∘ f) ⁻¹' s) :=
begin
  obtain ⟨n, φ, a, ha, rfl⟩ := h.exists_formula,
  refine is_definable_of (φ.relabel (sum.map id f)) a ha (λ x, _),
  simp [realize_partitioned_formula],
end

/-- This lemma is only intended as a helper for `is_definable.image_comp_sum_inl`. -/
lemma is_definable.image_comp_sum_inl_fin (m : ℕ) {s : set ((α ⊕ (fin m)) → M)}
  (h : L.is_definable A s) :
  L.is_definable A ((λ g : (α ⊕ (fin m)) → M, g ∘ sum.inl) '' s) :=
begin
  obtain ⟨n, φ, a, ha, rfl⟩ := h.exists_formula,
  refine is_definable_of (partitioned_formula.exists_right (φ.relabel (equiv.sum_assoc (fin n) α
    (fin m)).symm)) a ha (λ x, _),
  simp only [set.mem_image, set.mem_set_of_eq, realize_partitioned_formula,
    partitioned_formula.realize_exists_right, realize_formula_relabel],
  have h' : ∀ (xs : α ⊕ fin m → M), sum.elim a xs = sum.elim (sum.elim a (xs ∘ sum.inl))
    (xs ∘ sum.inr) ∘ ((equiv.sum_assoc (fin n) α (fin m)).symm),
  { intro xs,
    ext i,
    cases i,
    { simp },
    { cases i,
      { simp },
      { simp } } },
  split,
  { rintro ⟨xs, h, rfl⟩,
    exact ⟨xs ∘ sum.inr, eq.mp (congr rfl (h' xs)) h⟩ },
  { rintro ⟨y, h⟩,
    exact ⟨sum.elim x y, eq.mpr (congr rfl (h' _)) h, sum.elim_comp_inl x y⟩ }
end

lemma is_definable.image_comp_equiv {s : set (β → M)} (h : L.is_definable A s) (f : α ≃ β) :
  L.is_definable A ((λ g : β → M, g ∘ f) '' s) :=
begin
  refine eq.mp (congr rfl _) (h.preimage_comp f.symm),
  rw set.image_eq_preimage_of_inverse,
  { intro i,
    ext b,
    simp },
  { intro i,
    ext a,
    simp }
end

/-- Shows that definability is closed under general projections. -/
lemma is_definable.image_comp_of_injective {s : set (β → M)} (h : L.is_definable A s)
  (f : α → β) (hf : function.injective f) :
  L.is_definable A ((λ g : β → M, g ∘ f) '' s) :=
begin
  classical,
  have h := h.image_comp_equiv (equiv.trans (equiv.sum_congr (_root_.equiv.refl _)
    (fintype.equiv_fin _).symm) (equiv.set.sum_compl (set.range f))),
  have h := h.image_comp_sum_inl_fin _,
  have h := h.image_comp_equiv (equiv.of_injective f hf),
  refine eq.mp (congr rfl _) h,
  ext x,
  simp only [equiv.coe_trans, set.mem_image, exists_exists_and_eq_and],
  split,
  { rintros ⟨y, hy, rfl⟩,
    refine ⟨y, hy, _⟩,
    ext b,
    simp },
  { rintros ⟨y, hy, rfl⟩,
    refine ⟨y, hy, _⟩,
    ext a,
    simp },
end

variables (L) {M} (A)

/-- A 1-dimensional version of `is_definable`, for `set M`. -/
def is_definable_set (s : set M) : Prop := L.is_definable A { x : fin 1 → M | x 0 ∈ s }

variables {L A}

lemma is_definable_set_iff {s : set M} :
  L.is_definable_set A s ↔
  ∃ {n : ℕ} (φ : L.formula (fin (n + 1))) (a : fin n → M) (ha : ∀ i, a i ∈ A),
  s = set_of (λ x, realize_formula M φ (fin.cons x a)) :=
begin
  rw [is_definable_set],
  split,
  { rintros ⟨⟨n, φ, a, ha, h⟩⟩,
    refine ⟨n, φ.relabel (sum.elim fin.succ (λ _, 0)), a, ha, _⟩,
    ext x,
    have h' := (set.ext_iff.1 h) (λ _, x),
    simp only [set.mem_set_of_eq] at h',
    simp only [h', realize_formula_relabel, set.mem_set_of_eq, iff_eq_eq, sum.comp_elim],
    refine congr rfl (funext (λ i, _)),
    cases i,
    { simp only [sum.elim_inl, function.comp_app, fin.cons_succ] },
    { simp only [sum.elim_inr, function.comp_const, fin.cons_zero] } },
  { rintros ⟨n, φ, a, ha, rfl⟩,
    refine ⟨⟨n, φ.relabel (fin.cases _ _), a, ha, _⟩⟩,
    { exact sum.inr 0 },
    { exact sum.inl },
    ext x,
    simp only [fin.val_eq_coe, set.mem_set_of_eq, realize_formula_relabel, iff_eq_eq],
    refine congr rfl (funext (fin.cases _ _)),
    { simp only [fin.cons_zero, function.comp_app, fin.cases_zero, sum.elim_inr] },
    { simp } }
end

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

end language
end first_order
