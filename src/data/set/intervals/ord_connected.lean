/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import data.set.intervals.unordered_interval
import data.set.lattice

/-!
# Order-connected sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We say that a set `s : set α` is `ord_connected` if for all `x y ∈ s` it includes the
interval `[x, y]`. If `α` is a `densely_ordered` `conditionally_complete_linear_order` with
the `order_topology`, then this condition is equivalent to `is_preconnected s`. If `α` is a
`linear_ordered_field`, then this condition is also equivalent to `convex α s`.

In this file we prove that intersection of a family of `ord_connected` sets is `ord_connected` and
that all standard intervals are `ord_connected`.
-/

open_locale interval
open order_dual (to_dual of_dual)

namespace set
section preorder
variables {α β : Type*} [preorder α] [preorder β] {s t : set α}

/--
We say that a set `s : set α` is `ord_connected` if for all `x y ∈ s` it includes the
interval `[x, y]`. If `α` is a `densely_ordered` `conditionally_complete_linear_order` with
the `order_topology`, then this condition is equivalent to `is_preconnected s`. If `α` is a
`linear_ordered_field`, then this condition is also equivalent to `convex α s`.
-/
class ord_connected (s : set α) : Prop :=
(out' ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) : Icc x y ⊆ s)

lemma ord_connected.out (h : ord_connected s) :
  ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), Icc x y ⊆ s := h.1

lemma ord_connected_def : ord_connected s ↔ ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), Icc x y ⊆ s :=
⟨λ h, h.1, λ h, ⟨h⟩⟩

/-- It suffices to prove `[x, y] ⊆ s` for `x y ∈ s`, `x ≤ y`. -/
lemma ord_connected_iff : ord_connected s ↔ ∀ (x ∈ s) (y ∈ s), x ≤ y → Icc x y ⊆ s :=
ord_connected_def.trans
⟨λ hs x hx y hy hxy, hs hx hy, λ H x hx y hy z hz, H x hx y hy (le_trans hz.1 hz.2) hz⟩

lemma ord_connected_of_Ioo {α : Type*} [partial_order α] {s : set α}
  (hs : ∀ (x ∈ s) (y ∈ s), x < y → Ioo x y ⊆ s) :
  ord_connected s :=
begin
  rw ord_connected_iff,
  intros x hx y hy hxy,
  rcases eq_or_lt_of_le hxy with rfl|hxy', { simpa },
  rw [←Ioc_insert_left hxy, ←Ioo_insert_right hxy'],
  exact insert_subset.2 ⟨hx, insert_subset.2 ⟨hy, hs x hx y hy hxy'⟩⟩,
end

lemma ord_connected.preimage_mono {f : β → α} (hs : ord_connected s) (hf : monotone f) :
  ord_connected (f ⁻¹' s) :=
⟨λ x hx y hy z hz, hs.out hx hy ⟨hf hz.1, hf hz.2⟩⟩

lemma ord_connected.preimage_anti {f : β → α} (hs : ord_connected s) (hf : antitone f) :
  ord_connected (f ⁻¹' s) :=
⟨λ x hx y hy z hz, hs.out hy hx ⟨hf hz.2, hf hz.1⟩⟩

protected lemma Icc_subset (s : set α) [hs : ord_connected s] {x y} (hx : x ∈ s) (hy : y ∈ s) :
  Icc x y ⊆ s := hs.out hx hy

lemma ord_connected.inter {s t : set α} (hs : ord_connected s) (ht : ord_connected t) :
  ord_connected (s ∩ t) :=
⟨λ x hx y hy, subset_inter (hs.out hx.1 hy.1) (ht.out hx.2 hy.2)⟩

instance ord_connected.inter' {s t : set α} [ord_connected s] [ord_connected t] :
  ord_connected (s ∩ t) :=
ord_connected.inter ‹_› ‹_›

lemma ord_connected.dual {s : set α} (hs : ord_connected s) :
  ord_connected (order_dual.of_dual ⁻¹' s) :=
⟨λ x hx y hy z hz, hs.out hy hx ⟨hz.2, hz.1⟩⟩

lemma ord_connected_dual {s : set α} : ord_connected (order_dual.of_dual ⁻¹' s) ↔ ord_connected s :=
⟨λ h, by simpa only [ord_connected_def] using h.dual, λ h, h.dual⟩

lemma ord_connected_sInter {S : set (set α)} (hS : ∀ s ∈ S, ord_connected s) :
  ord_connected (⋂₀ S) :=
⟨λ x hx y hy, subset_sInter $ λ s hs, (hS s hs).out (hx s hs) (hy s hs)⟩

lemma ord_connected_Inter {ι : Sort*} {s : ι → set α} (hs : ∀ i, ord_connected (s i)) :
  ord_connected (⋂ i, s i) :=
ord_connected_sInter $ forall_range_iff.2 hs

instance ord_connected_Inter' {ι : Sort*} {s : ι → set α} [∀ i, ord_connected (s i)] :
  ord_connected (⋂ i, s i) :=
ord_connected_Inter ‹_›

lemma ord_connected_bInter {ι : Sort*} {p : ι → Prop} {s : Π (i : ι) (hi : p i), set α}
  (hs : ∀ i hi, ord_connected (s i hi)) :
  ord_connected (⋂ i hi, s i hi) :=
ord_connected_Inter $ λ i, ord_connected_Inter $ hs i

lemma ord_connected_pi {ι : Type*} {α : ι → Type*} [Π i, preorder (α i)] {s : set ι}
  {t : Π i, set (α i)} (h : ∀ i ∈ s, ord_connected (t i)) : ord_connected (s.pi t) :=
⟨λ x hx y hy z hz i hi, (h i hi).out (hx i hi) (hy i hi) ⟨hz.1 i, hz.2 i⟩⟩

instance ord_connected_pi' {ι : Type*} {α : ι → Type*} [Π i, preorder (α i)] {s : set ι}
  {t : Π i, set (α i)} [h : ∀ i, ord_connected (t i)] : ord_connected (s.pi t) :=
ord_connected_pi $ λ i hi, h i

@[instance] lemma ord_connected_Ici {a : α} : ord_connected (Ici a) :=
⟨λ x hx y hy z hz, le_trans hx hz.1⟩

@[instance] lemma ord_connected_Iic {a : α} : ord_connected (Iic a) :=
⟨λ x hx y hy z hz, le_trans hz.2 hy⟩

@[instance] lemma ord_connected_Ioi {a : α} : ord_connected (Ioi a) :=
⟨λ x hx y hy z hz, lt_of_lt_of_le hx hz.1⟩

@[instance] lemma ord_connected_Iio {a : α} : ord_connected (Iio a) :=
⟨λ x hx y hy z hz, lt_of_le_of_lt hz.2 hy⟩

@[instance] lemma ord_connected_Icc {a b : α} : ord_connected (Icc a b) :=
ord_connected_Ici.inter ord_connected_Iic

@[instance] lemma ord_connected_Ico {a b : α} : ord_connected (Ico a b) :=
ord_connected_Ici.inter ord_connected_Iio

@[instance] lemma ord_connected_Ioc {a b : α} : ord_connected (Ioc a b) :=
ord_connected_Ioi.inter ord_connected_Iic

@[instance] lemma ord_connected_Ioo {a b : α} : ord_connected (Ioo a b) :=
ord_connected_Ioi.inter ord_connected_Iio

@[instance] lemma ord_connected_singleton {α : Type*} [partial_order α] {a : α} :
  ord_connected ({a} : set α) :=
by { rw ← Icc_self, exact ord_connected_Icc }

@[instance] lemma ord_connected_empty : ord_connected (∅ : set α) := ⟨λ x, false.elim⟩

@[instance] lemma ord_connected_univ : ord_connected (univ : set α) := ⟨λ _ _ _ _, subset_univ _⟩

/-- In a dense order `α`, the subtype from an `ord_connected` set is also densely ordered. -/
instance [densely_ordered α] {s : set α} [hs : ord_connected s] :
  densely_ordered s :=
⟨λ a b (h : (a : α) < b), let ⟨x, H⟩ := exists_between h in
    ⟨⟨x, (hs.out a.2 b.2) (Ioo_subset_Icc_self H)⟩, H⟩ ⟩

@[instance] lemma ord_connected_preimage {F : Type*} [order_hom_class F α β] (f : F) {s : set β}
  [hs : ord_connected s] : ord_connected (f ⁻¹' s) :=
⟨λ x hx y hy z hz, hs.out hx hy ⟨order_hom_class.mono _ hz.1, order_hom_class.mono _ hz.2⟩⟩

@[instance] lemma ord_connected_image {E : Type*} [order_iso_class E α β] (e : E) {s : set α}
  [hs : ord_connected s] : ord_connected (e '' s) :=
by { erw [(e : α ≃o β).image_eq_preimage], apply ord_connected_preimage }

@[instance] lemma ord_connected_range {E : Type*} [order_iso_class E α β] (e : E) :
  ord_connected (range e) :=
by simp_rw [← image_univ, ord_connected_image e]

@[simp] lemma dual_ord_connected_iff {s : set α} :
  ord_connected (of_dual ⁻¹' s) ↔ ord_connected s :=
begin
  simp_rw [ord_connected_def, to_dual.surjective.forall, dual_Icc, subtype.forall'],
  exact forall_swap
end

@[instance] lemma dual_ord_connected {s : set α} [ord_connected s] :
  ord_connected (of_dual ⁻¹' s) :=
dual_ord_connected_iff.2 ‹_›

end preorder

section linear_order
variables {α : Type*} [linear_order α] {s : set α} {x : α}

@[instance] lemma ord_connected_uIcc {a b : α} : ord_connected [a, b] := ord_connected_Icc
@[instance] lemma ord_connected_uIoc {a b : α} : ord_connected (Ι a b) := ord_connected_Ioc

lemma ord_connected.uIcc_subset (hs : ord_connected s) ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) :
  [x, y] ⊆ s :=
hs.out (min_rec' (∈ s) hx hy) (max_rec' (∈ s) hx hy)

lemma ord_connected.uIoc_subset (hs : ord_connected s) ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) :
  Ι x y ⊆ s :=
Ioc_subset_Icc_self.trans $ hs.uIcc_subset hx hy

lemma ord_connected_iff_uIcc_subset :
  ord_connected s ↔ ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), [x, y] ⊆ s :=
⟨λ h, h.uIcc_subset, λ H, ⟨λ x hx y hy, Icc_subset_uIcc.trans $ H hx hy⟩⟩

lemma ord_connected_of_uIcc_subset_left (h : ∀ y ∈ s, [x, y] ⊆ s) :
  ord_connected s :=
ord_connected_iff_uIcc_subset.2 $ λ y hy z hz,
calc [y, z] ⊆ [y, x] ∪ [x, z] : uIcc_subset_uIcc_union_uIcc
... = [x, y] ∪ [x, z] : by rw [uIcc_comm]
... ⊆ s : union_subset (h y hy) (h z hz)

lemma ord_connected_iff_uIcc_subset_left (hx : x ∈ s) :
  ord_connected s ↔ ∀ ⦃y⦄, y ∈ s → [x, y] ⊆ s :=
⟨λ hs, hs.uIcc_subset hx, ord_connected_of_uIcc_subset_left⟩

lemma ord_connected_iff_uIcc_subset_right (hx : x ∈ s) :
  ord_connected s ↔ ∀ ⦃y⦄, y ∈ s → [y, x] ⊆ s :=
by simp_rw [ord_connected_iff_uIcc_subset_left hx, uIcc_comm]

end linear_order
end set
