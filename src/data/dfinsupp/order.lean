/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.dfinsupp.basic

/-!
# Pointwise order on finitely supported dependent functions

This file lifts order structures on the `α i` to `Π₀ i, α i`.

## Main declarations

* `dfinsupp.order_embedding_to_fun`: The order embedding from finitely supported dependent functions
  to functions.

## TODO

Add `is_well_order (Π₀ i, α i) (<)`.
-/

noncomputable theory
open_locale classical big_operators

open finset

variables {ι : Type*} {α : ι → Type*}

namespace dfinsupp

lemma not_mem_support_iff [Π i, has_zero (α i)] {f : Π₀ i, α i} {i : ι} : i ∉ f.support ↔ f i = 0 :=
by rw [mem_support_iff, not_ne_iff]

/-! ### Order structures -/

section has_zero
variables (α) [Π i, has_zero (α i)]

section has_le
variables [Π i, has_le (α i)]

instance : has_le (Π₀ i, α i) := ⟨λ f g, ∀ i, f i ≤ g i⟩

variables {α}

lemma le_def {f g : Π₀ i, α i} : f ≤ g ↔ ∀ i, f i ≤ g i := iff.rfl

/-- The order on `dfinsupp`s over a partial order embeds into the order on functions -/
def order_embedding_to_fun : (Π₀ i, α i) ↪o Π i, α i :=
{ to_fun := λ f, f,
  inj' := λ f g h, dfinsupp.ext $ λ i, by { dsimp at h, rw h },
  map_rel_iff' := λ a b, (@le_def _ _ _ _ a b).symm }

@[simp] lemma order_embedding_to_fun_apply {f : Π₀ i, α i} {i : ι} :
  order_embedding_to_fun f i = f i := rfl

end has_le

section preorder
variables [Π i, preorder (α i)]

instance : preorder (Π₀ i, α i) :=
{ le_refl := λ f i, le_rfl,
  le_trans := λ f g h hfg hgh i, (hfg i).trans (hgh i),
  .. dfinsupp.has_le α }

lemma coe_fn_mono : monotone (coe_fn : (Π₀ i, α i) → Π i, α i) := λ f g, le_def.1

end preorder

instance [Π i, partial_order (α i)] : partial_order (Π₀ i, α i) :=
{ le_antisymm := λ f g hfg hgf, ext $ λ i, (hfg i).antisymm (hgf i),
  .. dfinsupp.preorder α}

instance [Π i, semilattice_inf (α i)] : semilattice_inf (Π₀ i, α i) :=
{ inf := zip_with (λ _, (⊓)) (λ _, inf_idem),
  inf_le_left := λ f g i, by { rw zip_with_apply, exact inf_le_left },
  inf_le_right := λ f g i, by { rw zip_with_apply, exact inf_le_right },
  le_inf := λ f g h hf hg i, by { rw zip_with_apply, exact le_inf (hf i) (hg i) },
  ..dfinsupp.partial_order α }

@[simp] lemma inf_apply [Π i, semilattice_inf (α i)] (f g : Π₀ i, α i) (i : ι) :
  (f ⊓ g) i = f i ⊓ g i :=
zip_with_apply _ _ _ _ _

instance [Π i, semilattice_sup (α i)] : semilattice_sup (Π₀ i, α i) :=
{ sup := zip_with (λ _, (⊔)) (λ _, sup_idem),
  le_sup_left := λ f g i, by { rw zip_with_apply, exact le_sup_left },
  le_sup_right := λ f g i, by { rw zip_with_apply, exact le_sup_right },
  sup_le := λ f g h hf hg i, by { rw zip_with_apply, exact sup_le (hf i) (hg i) },
  ..dfinsupp.partial_order α }

@[simp] lemma sup_apply [Π i, semilattice_sup (α i)] (f g : Π₀ i, α i) (i : ι) :
  (f ⊔ g) i = f i ⊔ g i :=
zip_with_apply _ _ _ _ _

instance lattice [Π i, lattice (α i)] : lattice (Π₀ i, α i) :=
{ .. dfinsupp.semilattice_inf α, .. dfinsupp.semilattice_sup α }

end has_zero

/-! ### Algebraic order structures -/

instance (α : ι → Type*) [Π i, ordered_add_comm_monoid (α i)] :
  ordered_add_comm_monoid (Π₀ i, α i) :=
{ add_le_add_left := λ a b h c i,
    by { rw [add_apply, add_apply], exact add_le_add_left (h i) (c i) },
  .. dfinsupp.add_comm_monoid, .. dfinsupp.partial_order α }

instance (α : ι → Type*) [Π i, ordered_cancel_add_comm_monoid (α i)] :
  ordered_cancel_add_comm_monoid (Π₀ i, α i) :=
{ le_of_add_le_add_left := λ f g h H i, begin
    specialize H i,
    rw [add_apply, add_apply] at H,
    exact le_of_add_le_add_left H,
  end,
  add_left_cancel := λ f g h H, ext $ λ i, begin
    refine add_left_cancel _,
    exact f i,
    rw [←add_apply, ←add_apply, H],
  end,
  .. dfinsupp.ordered_add_comm_monoid α }

instance [Π i, ordered_add_comm_monoid (α i)] [Π i, contravariant_class (α i) (α i) (+) (≤)] :
  contravariant_class (Π₀ i, α i) (Π₀ i, α i) (+) (≤) :=
⟨λ f g h H i, by { specialize H i, rw [add_apply, add_apply] at H, exact le_of_add_le_add_left H }⟩

section canonically_ordered_add_monoid
variables (α) [Π i, canonically_ordered_add_monoid (α i)]

instance : order_bot (Π₀ i, α i) :=
{ bot := 0,
  bot_le := by simp only [le_def, coe_zero, pi.zero_apply, implies_true_iff, zero_le] }

variables {α}

protected lemma bot_eq_zero : (⊥ : Π₀ i, α i) = 0 := rfl

@[simp] lemma add_eq_zero_iff (f g : Π₀ i, α i) : f + g = 0 ↔ f = 0 ∧ g = 0 :=
by simp [ext_iff, forall_and_distrib]

lemma le_iff' {f g : Π₀ i, α i} {s : finset ι} (hf : f.support ⊆ s) : f ≤ g ↔ ∀ i ∈ s, f i ≤ g i :=
⟨λ h s hs, h s,
λ h s, if H : s ∈ f.support then h s (hf H) else (not_mem_support_iff.1 H).symm ▸ zero_le (g s)⟩

lemma le_iff {f g : Π₀ i, α i} : f ≤ g ↔ ∀ i ∈ f.support, f i ≤ g i := le_iff' $ subset.refl _

variables (α)

instance decidable_le [Π i, decidable_rel (@has_le.le (α i) _)] :
  decidable_rel (@has_le.le (Π₀ i, α i) _) :=
λ f g, decidable_of_iff _ le_iff.symm

variables {α}

@[simp] lemma single_le_iff {i : ι} {a : α i} {f : Π₀ i, α i} : single i a ≤ f ↔ a ≤ f i :=
(le_iff' support_single_subset).trans $ by simp

variables (α) [Π i, has_sub (α i)] [Π i, has_ordered_sub (α i)] {f g : Π₀ i, α i} {i : ι}
  {a b : α i}

/-- This is called `tsub` for truncated subtraction, to distinguish it with subtraction in an
additive group. -/
instance tsub : has_sub (Π₀ i, α i) := ⟨zip_with (λ i m n, m - n) (λ i, tsub_self 0)⟩

variables {α}

lemma tsub_apply (f g : Π₀ i, α i) (i : ι) : (f - g) i = f i - g i := zip_with_apply _ _ _ _ _

@[simp] lemma coe_tsub (f g : Π₀ i, α i) : ⇑(f - g) = f - g := by { ext i, exact tsub_apply f g i }

variables (α)

instance : has_ordered_sub (Π₀ i, α i) :=
⟨λ n m k, forall_congr $ λ i, by { rw [add_apply, tsub_apply], exact tsub_le_iff_right }⟩

instance : canonically_ordered_add_monoid (Π₀ i, α i) :=
{ le_iff_exists_add := λ f g, begin
      refine ⟨λ h, ⟨g - f, _⟩, _⟩,
      { ext i,
        rw [add_apply, tsub_apply],
        exact (add_tsub_cancel_of_le $ h i).symm },
      { rintro ⟨g, rfl⟩ i,
        rw add_apply,
        exact self_le_add_right (f i) (g i) }
    end,
 .. dfinsupp.order_bot α,
 .. dfinsupp.ordered_add_comm_monoid α }

variables {α}

@[simp] lemma single_tsub : single i (a - b) = single i a - single i b :=
begin
  ext j,
  obtain rfl | h := eq_or_ne i j,
  { rw [tsub_apply, single_eq_same, single_eq_same, single_eq_same] },
  { rw [tsub_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, tsub_self] }
end

lemma support_tsub : (f - g).support ⊆ f.support :=
by simp only [subset_iff, tsub_eq_zero_iff_le, mem_support_iff, ne.def, coe_tsub, pi.sub_apply,
    not_imp_not, zero_le, implies_true_iff] {contextual := tt}

lemma subset_support_tsub : f.support \ g.support ⊆ (f - g).support :=
by simp [subset_iff] {contextual := tt}

end canonically_ordered_add_monoid

section canonically_linear_ordered_add_monoid
variables [Π i, canonically_linear_ordered_add_monoid (α i)] [decidable_eq ι] {f g : Π₀ i, α i}

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
  rw [disjoint_iff, disjoint_iff, dfinsupp.bot_eq_zero, ← dfinsupp.support_eq_empty,
    dfinsupp.support_inf],
  refl,
end

end canonically_linear_ordered_add_monoid
end dfinsupp
