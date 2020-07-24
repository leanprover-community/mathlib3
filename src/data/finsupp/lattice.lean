/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import data.finsupp
import algebra.ordered_group

/-!
# Lattice structure on finsupps

This file provides instances of ordered structures on finsupps.

-/

open_locale classical
noncomputable theory
variables {α : Type*} {β : Type*} [has_zero β] {μ : Type*} [canonically_ordered_add_monoid μ]
variables {γ : Type*} [canonically_linear_ordered_add_monoid γ]

namespace finsupp

lemma le_def [partial_order β] {a b : α →₀ β} : a ≤ b ↔ ∀ (s : α), a s ≤ b s := by refl

instance : order_bot (α →₀ μ) :=
{ bot := 0, bot_le := by simp [finsupp.le_def, ← bot_eq_zero], .. finsupp.partial_order}

/-- Used to construct binary operations on `finsupp`s -/
def binary_op_pointwise {f : β → β → β} (h : f 0 0 = 0) (a b : α →₀ β) : α →₀ β :=
{ support := ((a.support) ∪ (b.support)).filter (λ s, f (a s) (b s) ≠ 0),
  to_fun := λ s, f (a s) (b s),
  mem_support_to_fun := by {
    simp only [mem_support_iff, ne.def, finset.mem_union, finset.mem_filter],
    intro s, apply and_iff_right_of_imp, rw ← not_and_distrib, rw not_imp_not,
    intro h1, rw h1.left, rw h1.right, apply h, }, }

lemma binary_op_pointwise_apply {f : β → β → β} (h : f 0 0 = 0) (a b : α →₀ β) (s : α) :
  (binary_op_pointwise h a b) s = f (a s) (b s) := rfl

instance [semilattice_inf β] : semilattice_inf (α →₀ β) :=
{ inf := binary_op_pointwise inf_idem,
  inf_le_left := by { intros, rw le_def, intro, apply inf_le_left, },
  inf_le_right := by { intros, rw le_def, intro, apply inf_le_right, },
  le_inf := by { intros, rw le_def at *, intro, apply le_inf (a_1 s) (a_2 s) },
  ..finsupp.partial_order, }

@[simp]
lemma inf_apply [semilattice_inf β] {a : α} {f g : α →₀ β} : (f ⊓ g) a = f a ⊓ g a := rfl

@[simp]
lemma support_inf {f g : α →₀ γ} : (f ⊓ g).support = f.support ∩ g.support :=
begin
  change (binary_op_pointwise inf_idem f g).support = f.support ∩ g.support,
  unfold binary_op_pointwise, dsimp, ext,
  simp only [mem_support_iff,  ne.def,
    finset.mem_union, finset.mem_filter, finset.mem_inter],
  split; intro h, cases h with i j, split; intro con; rw con at j; apply j; simp [zero_le],
  { split, left, exact h.left, rw inf_eq_min, unfold min, split_ifs; tauto, }
end

instance [semilattice_sup β] : semilattice_sup (α →₀ β) :=
{ sup := binary_op_pointwise sup_idem,
  le_sup_left := by { intros, rw le_def, intro, apply le_sup_left, },
  le_sup_right := by { intros, rw le_def, intro, apply le_sup_right, },
  sup_le := by { intros, rw le_def at *, intro, apply sup_le (a_1 s) (a_2 s) },
  ..finsupp.partial_order, }

@[simp]
lemma sup_apply [semilattice_sup β] {a : α} {f g : α →₀ β} : (f ⊔ g) a = f a ⊔ g a := rfl

@[simp]
lemma support_sup
  {f g : α →₀ γ} : (f ⊔ g).support = f.support ∪ g.support :=
begin
  change (binary_op_pointwise sup_idem f g).support = f.support ∪ g.support,
  unfold binary_op_pointwise, dsimp, rw finset.filter_true_of_mem,
  intros x hx, rw ← bot_eq_zero, rw sup_eq_bot_iff,
   revert hx,
  simp only [not_and, mem_support_iff, bot_eq_zero, ne.def, finset.mem_union], tauto,
end

instance lattice [lattice β] : lattice (α →₀ β) :=
{ .. finsupp.semilattice_inf, .. finsupp.semilattice_sup}

instance semilattice_inf_bot : semilattice_inf_bot (α →₀ γ) :=
{ ..finsupp.order_bot, ..finsupp.lattice}

lemma of_multiset_strict_mono : strict_mono (@finsupp.of_multiset α) :=
begin
  unfold strict_mono, intros, rw lt_iff_le_and_ne at *, split,
  { rw finsupp.le_iff, intros s hs, repeat {rw finsupp.of_multiset_apply},
    rw multiset.le_iff_count at a_1, apply a_1.left },
  { have h := a_1.right, contrapose h, simp at *,
    apply finsupp.equiv_multiset.symm.injective h }
end

lemma bot_eq_zero : (⊥ : α →₀ γ) = 0 := rfl

lemma disjoint_iff {x y : α →₀ γ} : disjoint x y ↔ disjoint x.support y.support :=
begin
  unfold disjoint, repeat {rw le_bot_iff},
  rw [finsupp.bot_eq_zero, ← finsupp.support_eq_empty, finsupp.support_inf], refl,
end

/-- The lattice of finsupps to ℕ is order isomorphic to that of multisets.  -/
def order_iso_multiset (α : Type) :
  (has_le.le : (α →₀ ℕ) → (α →₀ ℕ) → Prop) ≃o (has_le.le : (multiset α) → (multiset α) → Prop) :=
⟨finsupp.equiv_multiset, begin
  intros a b, unfold finsupp.equiv_multiset, dsimp,
  rw multiset.le_iff_count, simp only [finsupp.count_to_multiset], refl
end ⟩



end finsupp
