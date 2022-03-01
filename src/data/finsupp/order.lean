/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Aaron Anderson
-/
import data.finsupp.basic

/-!
# Pointwise order on finitely supported functions

This file lifts order structures on `α` to `ι →₀ α`.

## Main declarations

* `finsupp.order_embedding_to_fun`: The order embedding from finitely supported functions to
  functions.
* `finsupp.order_iso_multiset`: The order isomorphism between `ℕ`-valued finitely supported
  functions and multisets.
-/

noncomputable theory
open_locale classical big_operators

open finset

variables {ι α : Type*}

namespace finsupp

/-! ### Order structures -/

section has_zero
variables [has_zero α]

section has_le
variables [has_le α]
instance : has_le (ι →₀ α) := ⟨λ f g, ∀ i, f i ≤ g i⟩

lemma le_def {f g : ι →₀ α} : f ≤ g ↔ ∀ i, f i ≤ g i := iff.rfl

/-- The order on `finsupp`s over a partial order embeds into the order on functions -/
def order_embedding_to_fun : (ι →₀ α) ↪o (ι → α) :=
{ to_fun := λ f, f,
  inj' := λ f g h, finsupp.ext $ λ i, by { dsimp at h, rw h },
  map_rel_iff' := λ a b, (@le_def _ _ _ _ a b).symm }

@[simp] lemma order_embedding_to_fun_apply {f : ι →₀ α} {i : ι} :
  order_embedding_to_fun f i = f i := rfl

end has_le

section preorder
variables [preorder α]

instance : preorder (ι →₀ α) :=
{ le_refl := λ f i, le_rfl,
  le_trans := λ f g h hfg hgh i, (hfg i).trans (hgh i),
  .. finsupp.has_le }

lemma monotone_to_fun : monotone (finsupp.to_fun : (ι →₀ α) → (ι → α)) := λ f g h a, le_def.1 h a

end preorder

instance [partial_order α] : partial_order (ι →₀ α) :=
{ le_antisymm := λ f g hfg hgf, ext $ λ i, (hfg i).antisymm (hgf i),
  .. finsupp.preorder }

instance [semilattice_inf α] : semilattice_inf (ι →₀ α) :=
{ inf := zip_with (⊓) inf_idem,
  inf_le_left := λ f g i, inf_le_left,
  inf_le_right := λ f g i, inf_le_right,
  le_inf := λ f g i h1 h2 s, le_inf (h1 s) (h2 s),
  ..finsupp.partial_order, }

@[simp] lemma inf_apply [semilattice_inf α] {i : ι} {f g : ι →₀ α} : (f ⊓ g) i = f i ⊓ g i := rfl

instance [semilattice_sup α] : semilattice_sup (ι →₀ α) :=
{ sup := zip_with (⊔) sup_idem,
  le_sup_left := λ f g i, le_sup_left,
  le_sup_right := λ f g i, le_sup_right,
  sup_le := λ f g h hf hg i, sup_le (hf i) (hg i),
  ..finsupp.partial_order }

@[simp] lemma sup_apply [semilattice_sup α] {i : ι} {f g : ι →₀ α} : (f ⊔ g) i = f i ⊔ g i := rfl

instance lattice [lattice α] : lattice (ι →₀ α) :=
{ .. finsupp.semilattice_inf, .. finsupp.semilattice_sup }

end has_zero

/-! ### Algebraic order structures -/

instance [ordered_add_comm_monoid α] : ordered_add_comm_monoid (ι →₀ α) :=
{ add_le_add_left := λ a b h c s, add_le_add_left (h s) (c s),
  .. finsupp.add_comm_monoid, .. finsupp.partial_order }

instance [ordered_cancel_add_comm_monoid α] : ordered_cancel_add_comm_monoid (ι →₀ α) :=
{ le_of_add_le_add_left := λ f g i h s, le_of_add_le_add_left (h s),
  add_left_cancel := λ f g i h, ext $ λ s, add_left_cancel (ext_iff.1 h s),
  .. finsupp.ordered_add_comm_monoid }

instance [ordered_add_comm_monoid α] [contravariant_class α α (+) (≤)] :
  contravariant_class (ι →₀ α) (ι →₀ α) (+) (≤) :=
⟨λ f g h H x, le_of_add_le_add_left $ H x⟩

section canonically_ordered_add_monoid
variables [canonically_ordered_add_monoid α]

instance : order_bot (ι →₀ α) :=
{ bot := 0,
  bot_le := by simp only [le_def, coe_zero, pi.zero_apply, implies_true_iff, zero_le]}

protected lemma bot_eq_zero : (⊥ : ι →₀ α) = 0 := rfl

@[simp] lemma add_eq_zero_iff (f g : ι →₀ α) : f + g = 0 ↔ f = 0 ∧ g = 0 :=
by simp [ext_iff, forall_and_distrib]

lemma le_iff' (f g : ι →₀ α) {s : finset ι} (hf : f.support ⊆ s) : f ≤ g ↔ ∀ i ∈ s, f i ≤ g i :=
⟨λ h s hs, h s,
λ h s, if H : s ∈ f.support then h s (hf H) else (not_mem_support_iff.1 H).symm ▸ zero_le (g s)⟩

lemma le_iff (f g : ι →₀ α) : f ≤ g ↔ ∀ i ∈ f.support, f i ≤ g i := le_iff' f g $ subset.refl _

instance decidable_le [decidable_rel (@has_le.le α _)] : decidable_rel (@has_le.le (ι →₀ α) _) :=
λ f g, decidable_of_iff _ (le_iff f g).symm

@[simp] lemma single_le_iff {i : ι} {x : α} {f : ι →₀ α} : single i x ≤ f ↔ x ≤ f i :=
(le_iff' _ _ support_single_subset).trans $ by simp

variables [has_sub α] [has_ordered_sub α] {f g : ι →₀ α} {i : ι} {a b : α}

/-- This is called `tsub` for truncated subtraction, to distinguish it with subtraction in an
additive group. -/
instance tsub : has_sub (ι →₀ α) := ⟨zip_with (λ m n, m - n) (tsub_self 0)⟩

instance : has_ordered_sub (ι →₀ α) := ⟨λ n m k, forall_congr $ λ x, tsub_le_iff_right⟩

instance : canonically_ordered_add_monoid (ι →₀ α) :=
{ le_iff_exists_add := λ f g, begin
      refine ⟨λ h, ⟨g - f, _⟩, _⟩,
      { ext x,
        exact (add_tsub_cancel_of_le $ h x).symm },
      { rintro ⟨g, rfl⟩ x,
        exact self_le_add_right (f x) (g x) }
    end,
 .. finsupp.order_bot,
 .. finsupp.ordered_add_comm_monoid }

@[simp] lemma coe_tsub (f g : ι →₀ α) : ⇑(f - g) = f - g := rfl

lemma tsub_apply (f g : ι →₀ α) (a : ι) : (f - g) a = f a - g a := rfl

@[simp] lemma single_tsub : single i (a - b) = single i a - single i b :=
begin
  ext j,
  obtain rfl | h := eq_or_ne i j,
  { rw [tsub_apply, single_eq_same, single_eq_same, single_eq_same] },
  { rw [tsub_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, tsub_self] }
end

lemma support_tsub {f1 f2 : ι →₀ α} : (f1 - f2).support ⊆ f1.support :=
by simp only [subset_iff, tsub_eq_zero_iff_le, mem_support_iff, ne.def, coe_tsub, pi.sub_apply,
    not_imp_not, zero_le, implies_true_iff] {contextual := tt}

lemma subset_support_tsub {f1 f2 : ι →₀ α} : f1.support \ f2.support ⊆ (f1 - f2).support :=
by simp [subset_iff] {contextual := tt}

end canonically_ordered_add_monoid

section canonically_linear_ordered_add_monoid
variables [canonically_linear_ordered_add_monoid α] [decidable_eq ι] {f g : ι →₀ α}

@[simp] lemma support_inf : (f ⊓ g).support = f.support ∩ g.support :=
begin
  ext,
  simp only [inf_apply, mem_support_iff,  ne.def,
    finset.mem_union, finset.mem_filter, finset.mem_inter],
  simp only [inf_eq_min, ←nonpos_iff_eq_zero, min_le_iff, not_or_distrib],
end

@[simp] lemma support_sup : (f ⊔ g).support = f.support ∪ g.support :=
begin
  ext,
  simp only [finset.mem_union, mem_support_iff, sup_apply, ne.def, ←bot_eq_zero],
  rw [_root_.sup_eq_bot_iff, not_and_distrib],
end

lemma disjoint_iff : disjoint f g ↔ disjoint f.support g.support :=
begin
  rw [disjoint_iff, disjoint_iff, finsupp.bot_eq_zero, ← finsupp.support_eq_empty,
    finsupp.support_inf],
  refl,
end

end canonically_linear_ordered_add_monoid

/-! ### Some lemmas about `ℕ` -/

section nat

lemma sub_single_one_add {a : ι} {u u' : ι →₀ ℕ} (h : u a ≠ 0) :
  u - single a 1 + u' = u + u' - single a 1 :=
tsub_add_eq_add_tsub $ single_le_iff.mpr $ nat.one_le_iff_ne_zero.mpr h

lemma add_sub_single_one {a : ι} {u u' : ι →₀ ℕ} (h : u' a ≠ 0) :
  u + (u' - single a 1) = u + u' - single a 1 :=
(add_tsub_assoc_of_le (single_le_iff.mpr $ nat.one_le_iff_ne_zero.mpr h) _).symm

end nat
end finsupp
