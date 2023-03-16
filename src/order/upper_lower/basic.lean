/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
import data.set_like.basic
import data.set.intervals.ord_connected
import data.set.intervals.order_iso

/-!
# Up-sets and down-sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines upper and lower sets in an order.

## Main declarations

* `is_upper_set`: Predicate for a set to be an upper set. This means every element greater than a
  member of the set is in the set itself.
* `is_lower_set`: Predicate for a set to be a lower set. This means every element less than a member
  of the set is in the set itself.
* `upper_set`: The type of upper sets.
* `lower_set`: The type of lower sets.
* `upper_closure`: The greatest upper set containing a set.
* `lower_closure`: The least lower set containing a set.
* `upper_set.Ici`: Principal upper set. `set.Ici` as an upper set.
* `upper_set.Ioi`: Strict principal upper set. `set.Ioi` as an upper set.
* `lower_set.Iic`: Principal lower set. `set.Iic` as an lower set.
* `lower_set.Iio`: Strict principal lower set. `set.Iio` as an lower set.

## Notation

`×ˢ` is notation for `upper_set.prod`/`lower_set.prod`.

## Notes

Upper sets are ordered by **reverse** inclusion. This convention is motivated by the fact that this
makes them order-isomorphic to lower sets and antichains, and matches the convention on `filter`.

## TODO

Lattice structure on antichains. Order equivalence between upper/lower sets and antichains.
-/

open order_dual set

variables {α β γ : Type*} {ι : Sort*} {κ : ι → Sort*}

/-! ### Unbundled upper/lower sets -/

section has_le
variables [has_le α] [has_le β] {s t : set α}

/-- An upper set in an order `α` is a set such that any element greater than one of its members is
also a member. Also called up-set, upward-closed set. -/
def is_upper_set (s : set α) : Prop := ∀ ⦃a b : α⦄, a ≤ b → a ∈ s → b ∈ s

/-- A lower set in an order `α` is a set such that any element less than one of its members is also
a member. Also called down-set, downward-closed set. -/
def is_lower_set (s : set α) : Prop := ∀ ⦃a b : α⦄, b ≤ a → a ∈ s → b ∈ s

lemma is_upper_set_empty : is_upper_set (∅ : set α) := λ _ _ _, id
lemma is_lower_set_empty : is_lower_set (∅ : set α) := λ _ _ _, id
lemma is_upper_set_univ : is_upper_set (univ : set α) := λ _ _ _, id
lemma is_lower_set_univ : is_lower_set (univ : set α) := λ _ _ _, id
lemma is_upper_set.compl (hs : is_upper_set s) : is_lower_set sᶜ := λ a b h hb ha, hb $ hs h ha
lemma is_lower_set.compl (hs : is_lower_set s) : is_upper_set sᶜ := λ a b h hb ha, hb $ hs h ha

@[simp] lemma is_upper_set_compl : is_upper_set sᶜ ↔ is_lower_set s :=
⟨λ h, by { convert h.compl, rw compl_compl }, is_lower_set.compl⟩

@[simp] lemma is_lower_set_compl : is_lower_set sᶜ ↔ is_upper_set s :=
⟨λ h, by { convert h.compl, rw compl_compl }, is_upper_set.compl⟩

lemma is_upper_set.union (hs : is_upper_set s) (ht : is_upper_set t) : is_upper_set (s ∪ t) :=
λ a b h, or.imp (hs h) (ht h)

lemma is_lower_set.union (hs : is_lower_set s) (ht : is_lower_set t) : is_lower_set (s ∪ t) :=
λ a b h, or.imp (hs h) (ht h)

lemma is_upper_set.inter (hs : is_upper_set s) (ht : is_upper_set t) : is_upper_set (s ∩ t) :=
λ a b h, and.imp (hs h) (ht h)

lemma is_lower_set.inter (hs : is_lower_set s) (ht : is_lower_set t) : is_lower_set (s ∩ t) :=
λ a b h, and.imp (hs h) (ht h)

lemma is_upper_set_Union {f : ι → set α} (hf : ∀ i, is_upper_set (f i)) : is_upper_set (⋃ i, f i) :=
λ a b h, Exists₂.imp $ forall_range_iff.2 $ λ i, hf i h

lemma is_lower_set_Union {f : ι → set α} (hf : ∀ i, is_lower_set (f i)) : is_lower_set (⋃ i, f i) :=
λ a b h, Exists₂.imp $ forall_range_iff.2 $ λ i, hf i h

lemma is_upper_set_Union₂ {f : Π i, κ i → set α} (hf : ∀ i j, is_upper_set (f i j)) :
  is_upper_set (⋃ i j, f i j) :=
is_upper_set_Union $ λ i, is_upper_set_Union $ hf i

lemma is_lower_set_Union₂ {f : Π i, κ i → set α} (hf : ∀ i j, is_lower_set (f i j)) :
  is_lower_set (⋃ i j, f i j) :=
is_lower_set_Union $ λ i, is_lower_set_Union $ hf i

lemma is_upper_set_sUnion {S : set (set α)} (hf : ∀ s ∈ S, is_upper_set s) : is_upper_set (⋃₀ S) :=
λ a b h, Exists₂.imp $ λ s hs, hf s hs h

lemma is_lower_set_sUnion {S : set (set α)} (hf : ∀ s ∈ S, is_lower_set s) : is_lower_set (⋃₀ S) :=
λ a b h, Exists₂.imp $ λ s hs, hf s hs h

lemma is_upper_set_Inter {f : ι → set α} (hf : ∀ i, is_upper_set (f i)) : is_upper_set (⋂ i, f i) :=
λ a b h, forall₂_imp $ forall_range_iff.2 $ λ i, hf i h

lemma is_lower_set_Inter {f : ι → set α} (hf : ∀ i, is_lower_set (f i)) : is_lower_set (⋂ i, f i) :=
λ a b h, forall₂_imp $ forall_range_iff.2 $ λ i, hf i h

lemma is_upper_set_Inter₂ {f : Π i, κ i → set α} (hf : ∀ i j, is_upper_set (f i j)) :
  is_upper_set (⋂ i j, f i j) :=
is_upper_set_Inter $ λ i, is_upper_set_Inter $ hf i

lemma is_lower_set_Inter₂ {f : Π i, κ i → set α} (hf : ∀ i j, is_lower_set (f i j)) :
  is_lower_set (⋂ i j, f i j) :=
is_lower_set_Inter $ λ i, is_lower_set_Inter $ hf i

lemma is_upper_set_sInter {S : set (set α)} (hf : ∀ s ∈ S, is_upper_set s) : is_upper_set (⋂₀ S) :=
λ a b h, forall₂_imp $ λ s hs, hf s hs h

lemma is_lower_set_sInter {S : set (set α)} (hf : ∀ s ∈ S, is_lower_set s) : is_lower_set (⋂₀ S) :=
λ a b h, forall₂_imp $ λ s hs, hf s hs h

@[simp] lemma is_lower_set_preimage_of_dual_iff : is_lower_set (of_dual ⁻¹' s) ↔ is_upper_set s :=
iff.rfl
@[simp] lemma is_upper_set_preimage_of_dual_iff : is_upper_set (of_dual ⁻¹' s) ↔ is_lower_set s :=
iff.rfl
@[simp] lemma is_lower_set_preimage_to_dual_iff {s : set αᵒᵈ} :
  is_lower_set (to_dual ⁻¹' s) ↔ is_upper_set s := iff.rfl
@[simp] lemma is_upper_set_preimage_to_dual_iff {s : set αᵒᵈ} :
  is_upper_set (to_dual ⁻¹' s) ↔ is_lower_set s := iff.rfl

alias is_lower_set_preimage_of_dual_iff ↔ _ is_upper_set.of_dual
alias is_upper_set_preimage_of_dual_iff ↔ _ is_lower_set.of_dual
alias is_lower_set_preimage_to_dual_iff ↔ _ is_upper_set.to_dual
alias is_upper_set_preimage_to_dual_iff ↔ _ is_lower_set.to_dual

end has_le

section preorder
variables [preorder α] [preorder β] {s : set α} {p : α → Prop} (a : α)

lemma is_upper_set_Ici : is_upper_set (Ici a) := λ _ _, ge_trans
lemma is_lower_set_Iic : is_lower_set (Iic a) := λ _ _, le_trans
lemma is_upper_set_Ioi : is_upper_set (Ioi a) := λ _ _, flip lt_of_lt_of_le
lemma is_lower_set_Iio : is_lower_set (Iio a) := λ _ _, lt_of_le_of_lt

lemma is_upper_set_iff_Ici_subset : is_upper_set s ↔ ∀ ⦃a⦄, a ∈ s → Ici a ⊆ s :=
by simp [is_upper_set, subset_def, @forall_swap (_ ∈ s)]

lemma is_lower_set_iff_Iic_subset : is_lower_set s ↔ ∀ ⦃a⦄, a ∈ s → Iic a ⊆ s :=
by simp [is_lower_set, subset_def, @forall_swap (_ ∈ s)]

alias is_upper_set_iff_Ici_subset ↔ is_upper_set.Ici_subset _
alias is_lower_set_iff_Iic_subset ↔ is_lower_set.Iic_subset _

lemma is_upper_set.ord_connected (h : is_upper_set s) : s.ord_connected :=
⟨λ a ha b _, Icc_subset_Ici_self.trans $ h.Ici_subset ha⟩

lemma is_lower_set.ord_connected (h : is_lower_set s) : s.ord_connected :=
⟨λ a _ b hb, Icc_subset_Iic_self.trans $ h.Iic_subset hb⟩

lemma is_upper_set.preimage (hs : is_upper_set s) {f : β → α} (hf : monotone f) :
  is_upper_set (f ⁻¹' s : set β) :=
λ x y hxy, hs $ hf hxy

lemma is_lower_set.preimage (hs : is_lower_set s) {f : β → α} (hf : monotone f) :
  is_lower_set (f ⁻¹' s : set β) :=
λ x y hxy, hs $ hf hxy

lemma is_upper_set.image (hs : is_upper_set s) (f : α ≃o β) : is_upper_set (f '' s : set β) :=
by { change is_upper_set ((f : α ≃ β) '' s), rw set.image_equiv_eq_preimage_symm,
  exact hs.preimage f.symm.monotone }

lemma is_lower_set.image (hs : is_lower_set s) (f : α ≃o β) : is_lower_set (f '' s : set β) :=
by { change is_lower_set ((f : α ≃ β) '' s), rw set.image_equiv_eq_preimage_symm,
  exact hs.preimage f.symm.monotone }

@[simp] lemma set.monotone_mem : monotone (∈ s) ↔ is_upper_set s := iff.rfl
@[simp] lemma set.antitone_mem : antitone (∈ s) ↔ is_lower_set s := forall_swap

@[simp] lemma is_upper_set_set_of : is_upper_set {a | p a} ↔ monotone p := iff.rfl
@[simp] lemma is_lower_set_set_of : is_lower_set {a | p a} ↔ antitone p := forall_swap

section order_top
variables [order_top α]

lemma is_lower_set.top_mem (hs : is_lower_set s) : ⊤ ∈ s ↔ s = univ :=
⟨λ h, eq_univ_of_forall $ λ a, hs le_top h, λ h, h.symm ▸ mem_univ _⟩

lemma is_upper_set.top_mem (hs : is_upper_set s) : ⊤ ∈ s ↔ s.nonempty :=
⟨λ h, ⟨_, h⟩, λ ⟨a, ha⟩, hs le_top ha⟩

lemma is_upper_set.not_top_mem (hs : is_upper_set s) : ⊤ ∉ s ↔ s = ∅ :=
hs.top_mem.not.trans not_nonempty_iff_eq_empty

end order_top

section order_bot
variables [order_bot α]

lemma is_upper_set.bot_mem (hs : is_upper_set s) : ⊥ ∈ s ↔ s = univ :=
⟨λ h, eq_univ_of_forall $ λ a, hs bot_le h, λ h, h.symm ▸ mem_univ _⟩

lemma is_lower_set.bot_mem (hs : is_lower_set s) : ⊥ ∈ s ↔ s.nonempty :=
⟨λ h, ⟨_, h⟩, λ ⟨a, ha⟩, hs bot_le ha⟩

lemma is_lower_set.not_bot_mem (hs : is_lower_set s) : ⊥ ∉ s ↔ s = ∅ :=
hs.bot_mem.not.trans not_nonempty_iff_eq_empty

end order_bot

section no_max_order
variables [no_max_order α] (a)

lemma is_upper_set.not_bdd_above (hs : is_upper_set s) : s.nonempty → ¬ bdd_above s :=
begin
  rintro ⟨a, ha⟩ ⟨b, hb⟩,
  obtain ⟨c, hc⟩ := exists_gt b,
  exact hc.not_le (hb $ hs ((hb ha).trans hc.le) ha),
end

lemma not_bdd_above_Ici : ¬ bdd_above (Ici a) := (is_upper_set_Ici _).not_bdd_above nonempty_Ici
lemma not_bdd_above_Ioi : ¬ bdd_above (Ioi a) := (is_upper_set_Ioi _).not_bdd_above nonempty_Ioi

end no_max_order

section no_min_order
variables [no_min_order α] (a)

lemma is_lower_set.not_bdd_below (hs : is_lower_set s) : s.nonempty → ¬ bdd_below s :=
begin
  rintro ⟨a, ha⟩ ⟨b, hb⟩,
  obtain ⟨c, hc⟩ := exists_lt b,
  exact hc.not_le (hb $ hs (hc.le.trans $ hb ha) ha),
end

lemma not_bdd_below_Iic : ¬ bdd_below (Iic a) := (is_lower_set_Iic _).not_bdd_below nonempty_Iic
lemma not_bdd_below_Iio : ¬ bdd_below (Iio a) := (is_lower_set_Iio _).not_bdd_below nonempty_Iio

end no_min_order
end preorder

section partial_order
variables [partial_order α] {s : set α}

lemma is_upper_set_iff_forall_lt : is_upper_set s ↔ ∀ ⦃a b : α⦄, a < b → a ∈ s → b ∈ s :=
forall_congr $ λ a, by simp [le_iff_eq_or_lt, or_imp_distrib, forall_and_distrib]

lemma is_lower_set_iff_forall_lt : is_lower_set s ↔ ∀ ⦃a b : α⦄, b < a → a ∈ s → b ∈ s :=
forall_congr $ λ a, by simp [le_iff_eq_or_lt, or_imp_distrib, forall_and_distrib]

lemma is_upper_set_iff_Ioi_subset : is_upper_set s ↔ ∀ ⦃a⦄, a ∈ s → Ioi a ⊆ s :=
by simp [is_upper_set_iff_forall_lt, subset_def, @forall_swap (_ ∈ s)]

lemma is_lower_set_iff_Iio_subset : is_lower_set s ↔ ∀ ⦃a⦄, a ∈ s → Iio a ⊆ s :=
by simp [is_lower_set_iff_forall_lt, subset_def, @forall_swap (_ ∈ s)]

alias is_upper_set_iff_Ioi_subset ↔ is_upper_set.Ioi_subset _
alias is_lower_set_iff_Iio_subset ↔ is_lower_set.Iio_subset _

end partial_order

/-! ### Bundled upper/lower sets -/

section has_le
variables [has_le α]

/-- The type of upper sets of an order. -/
structure upper_set (α : Type*) [has_le α] :=
(carrier : set α)
(upper' : is_upper_set carrier)

/-- The type of lower sets of an order. -/
structure lower_set (α : Type*) [has_le α] :=
(carrier : set α)
(lower' : is_lower_set carrier)

namespace upper_set

instance : set_like (upper_set α) α :=
{ coe := upper_set.carrier,
  coe_injective' := λ s t h, by { cases s, cases t, congr' } }

@[ext] lemma ext {s t : upper_set α} : (s : set α) = t → s = t := set_like.ext'

@[simp] lemma carrier_eq_coe (s : upper_set α) : s.carrier = s := rfl

protected lemma upper (s : upper_set α) : is_upper_set (s : set α) := s.upper'

@[simp] lemma mem_mk (carrier : set α) (upper') {a : α} : a ∈ mk carrier upper' ↔ a ∈ carrier :=
iff.rfl

end upper_set

namespace lower_set

instance : set_like (lower_set α) α :=
{ coe := lower_set.carrier,
  coe_injective' := λ s t h, by { cases s, cases t, congr' } }

@[ext] lemma ext {s t : lower_set α} : (s : set α) = t → s = t := set_like.ext'

@[simp] lemma carrier_eq_coe (s : lower_set α) : s.carrier = s := rfl

protected lemma lower (s : lower_set α) : is_lower_set (s : set α) := s.lower'

@[simp] lemma mem_mk (carrier : set α) (lower') {a : α} : a ∈ mk carrier lower' ↔ a ∈ carrier :=
iff.rfl

end lower_set

/-! #### Order -/

namespace upper_set
variables {S : set (upper_set α)} {s t : upper_set α} {a : α}

instance : has_sup (upper_set α) := ⟨λ s t, ⟨s ∩ t, s.upper.inter t.upper⟩⟩
instance : has_inf (upper_set α) := ⟨λ s t, ⟨s ∪ t, s.upper.union t.upper⟩⟩
instance : has_top (upper_set α) := ⟨⟨∅, is_upper_set_empty⟩⟩
instance : has_bot (upper_set α) := ⟨⟨univ, is_upper_set_univ⟩⟩
instance : has_Sup (upper_set α) :=
⟨λ S, ⟨⋂ s ∈ S, ↑s, is_upper_set_Inter₂ $ λ s _, s.upper⟩⟩
instance : has_Inf (upper_set α) :=
⟨λ S, ⟨⋃ s ∈ S, ↑s, is_upper_set_Union₂ $ λ s _, s.upper⟩⟩

instance : complete_distrib_lattice (upper_set α) :=
(to_dual.injective.comp $ set_like.coe_injective).complete_distrib_lattice _
  (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _, rfl) rfl rfl

instance : inhabited (upper_set α) := ⟨⊥⟩

@[simp, norm_cast] lemma coe_subset_coe : (s : set α) ⊆ t ↔ t ≤ s := iff.rfl
@[simp, norm_cast] lemma coe_top : ((⊤ : upper_set α) : set α) = ∅ := rfl
@[simp, norm_cast] lemma coe_bot : ((⊥ : upper_set α) : set α) = univ := rfl
@[simp, norm_cast] lemma coe_eq_univ : (s : set α) = univ ↔ s = ⊥ := by simp [set_like.ext'_iff]
@[simp, norm_cast] lemma coe_eq_empty : (s : set α) = ∅ ↔ s = ⊤ := by simp [set_like.ext'_iff]
@[simp, norm_cast] lemma coe_sup (s t : upper_set α) : (↑(s ⊔ t) : set α) = s ∩ t := rfl
@[simp, norm_cast] lemma coe_inf (s t : upper_set α) : (↑(s ⊓ t) : set α) = s ∪ t := rfl
@[simp, norm_cast] lemma coe_Sup (S : set (upper_set α)) : (↑(Sup S) : set α) = ⋂ s ∈ S, ↑s := rfl
@[simp, norm_cast] lemma coe_Inf (S : set (upper_set α)) : (↑(Inf S) : set α) = ⋃ s ∈ S, ↑s := rfl
@[simp, norm_cast] lemma coe_supr (f : ι → upper_set α) : (↑(⨆ i, f i) : set α) = ⋂ i, f i :=
by simp [supr]
@[simp, norm_cast] lemma coe_infi (f : ι → upper_set α) : (↑(⨅ i, f i) : set α) = ⋃ i, f i :=
by simp [infi]
@[simp, norm_cast] lemma coe_supr₂ (f : Π i, κ i → upper_set α) :
  (↑(⨆ i j, f i j) : set α) = ⋂ i j, f i j := by simp_rw coe_supr
@[simp, norm_cast] lemma coe_infi₂ (f : Π i, κ i → upper_set α) :
  (↑(⨅ i j, f i j) : set α) = ⋃ i j, f i j := by simp_rw coe_infi

@[simp] lemma not_mem_top : a ∉ (⊤ : upper_set α) := id
@[simp] lemma mem_bot : a ∈ (⊥ : upper_set α) := trivial
@[simp] lemma mem_sup_iff : a ∈ s ⊔ t ↔ a ∈ s ∧ a ∈ t := iff.rfl
@[simp] lemma mem_inf_iff : a ∈ s ⊓ t ↔ a ∈ s ∨ a ∈ t := iff.rfl
@[simp] lemma mem_Sup_iff : a ∈ Sup S ↔ ∀ s ∈ S, a ∈ s := mem_Inter₂
@[simp] lemma mem_Inf_iff  : a ∈ Inf S ↔ ∃ s ∈ S, a ∈ s := mem_Union₂
@[simp] lemma mem_supr_iff {f : ι → upper_set α} : a ∈ (⨆ i, f i) ↔ ∀ i, a ∈ f i :=
by { rw [←set_like.mem_coe, coe_supr], exact mem_Inter }
@[simp] lemma mem_infi_iff {f : ι → upper_set α} : a ∈ (⨅ i, f i) ↔ ∃ i, a ∈ f i :=
by { rw [←set_like.mem_coe, coe_infi], exact mem_Union }
@[simp] lemma mem_supr₂_iff {f : Π i, κ i → upper_set α} : a ∈ (⨆ i j, f i j) ↔ ∀ i j, a ∈ f i j :=
by simp_rw mem_supr_iff
@[simp] lemma mem_infi₂_iff {f : Π i, κ i → upper_set α} : a ∈ (⨅ i j, f i j) ↔ ∃ i j, a ∈ f i j :=
by simp_rw mem_infi_iff

@[simp, norm_cast] lemma codisjoint_coe : codisjoint (s : set α) t ↔ disjoint s t :=
by simp [disjoint_iff, codisjoint_iff, set_like.ext'_iff]

end upper_set

namespace lower_set
variables {S : set (lower_set α)} {s t : lower_set α} {a : α}

instance : has_sup (lower_set α) := ⟨λ s t, ⟨s ∪ t, λ a b h, or.imp (s.lower h) (t.lower h)⟩⟩
instance : has_inf (lower_set α) := ⟨λ s t, ⟨s ∩ t, λ a b h, and.imp (s.lower h) (t.lower h)⟩⟩
instance : has_top (lower_set α) := ⟨⟨univ, λ a b h, id⟩⟩
instance : has_bot (lower_set α) := ⟨⟨∅, λ a b h, id⟩⟩
instance : has_Sup (lower_set α) := ⟨λ S, ⟨⋃ s ∈ S, ↑s, is_lower_set_Union₂ $ λ s _, s.lower⟩⟩
instance : has_Inf (lower_set α) := ⟨λ S, ⟨⋂ s ∈ S, ↑s, is_lower_set_Inter₂ $ λ s _, s.lower⟩⟩

instance : complete_distrib_lattice (lower_set α) :=
set_like.coe_injective.complete_distrib_lattice _
  (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _, rfl) rfl rfl

instance : inhabited (lower_set α) := ⟨⊥⟩

@[simp, norm_cast] lemma coe_subset_coe : (s : set α) ⊆ t ↔ s ≤ t := iff.rfl
@[simp, norm_cast] lemma coe_top : ((⊤ : lower_set α) : set α) = univ := rfl
@[simp, norm_cast] lemma coe_bot : ((⊥ : lower_set α) : set α) = ∅ := rfl
@[simp, norm_cast] lemma coe_eq_univ : (s : set α) = univ ↔ s = ⊤ := by simp [set_like.ext'_iff]
@[simp, norm_cast] lemma coe_eq_empty : (s : set α) = ∅ ↔ s = ⊥ := by simp [set_like.ext'_iff]
@[simp, norm_cast] lemma coe_sup (s t : lower_set α) : (↑(s ⊔ t) : set α) = s ∪ t := rfl
@[simp, norm_cast] lemma coe_inf (s t : lower_set α) : (↑(s ⊓ t) : set α) = s ∩ t := rfl
@[simp, norm_cast] lemma coe_Sup (S : set (lower_set α)) : (↑(Sup S) : set α) = ⋃ s ∈ S, ↑s := rfl
@[simp, norm_cast] lemma coe_Inf (S : set (lower_set α)) : (↑(Inf S) : set α) = ⋂ s ∈ S, ↑s := rfl
@[simp, norm_cast] lemma coe_supr (f : ι → lower_set α) : (↑(⨆ i, f i) : set α) = ⋃ i, f i :=
by simp_rw [supr, coe_Sup, mem_range, Union_exists, Union_Union_eq']
@[simp, norm_cast] lemma coe_infi (f : ι → lower_set α) : (↑(⨅ i, f i) : set α) = ⋂ i, f i :=
by simp_rw [infi, coe_Inf, mem_range, Inter_exists, Inter_Inter_eq']
@[simp, norm_cast] lemma coe_supr₂ (f : Π i, κ i → lower_set α) :
  (↑(⨆ i j, f i j) : set α) = ⋃ i j, f i j := by simp_rw coe_supr
@[simp, norm_cast] lemma coe_infi₂ (f : Π i, κ i → lower_set α) :
  (↑(⨅ i j, f i j) : set α) = ⋂ i j, f i j := by simp_rw coe_infi

@[simp] lemma mem_top : a ∈ (⊤ : lower_set α) := trivial
@[simp] lemma not_mem_bot : a ∉ (⊥ : lower_set α) := id
@[simp] lemma mem_sup_iff : a ∈ s ⊔ t ↔ a ∈ s ∨ a ∈ t := iff.rfl
@[simp] lemma mem_inf_iff : a ∈ s ⊓ t ↔ a ∈ s ∧ a ∈ t := iff.rfl
@[simp] lemma mem_Sup_iff : a ∈ Sup S ↔ ∃ s ∈ S, a ∈ s := mem_Union₂
@[simp] lemma mem_Inf_iff  : a ∈ Inf S ↔ ∀ s ∈ S, a ∈ s := mem_Inter₂
@[simp] lemma mem_supr_iff {f : ι → lower_set α} : a ∈ (⨆ i, f i) ↔ ∃ i, a ∈ f i :=
by { rw [←set_like.mem_coe, coe_supr], exact mem_Union }
@[simp] lemma mem_infi_iff {f : ι → lower_set α} : a ∈ (⨅ i, f i) ↔ ∀ i, a ∈ f i :=
by { rw [←set_like.mem_coe, coe_infi], exact mem_Inter }
@[simp] lemma mem_supr₂_iff {f : Π i, κ i → lower_set α} : a ∈ (⨆ i j, f i j) ↔ ∃ i j, a ∈ f i j :=
by simp_rw mem_supr_iff
@[simp] lemma mem_infi₂_iff {f : Π i, κ i → lower_set α} : a ∈ (⨅ i j, f i j) ↔ ∀ i j, a ∈ f i j :=
by simp_rw mem_infi_iff

@[simp, norm_cast] lemma disjoint_coe : disjoint (s : set α) t ↔ disjoint s t :=
by simp [disjoint_iff, set_like.ext'_iff]

end lower_set

/-! #### Complement -/

/-- The complement of a lower set as an upper set. -/
def upper_set.compl (s : upper_set α) : lower_set α := ⟨sᶜ, s.upper.compl⟩

/-- The complement of a lower set as an upper set. -/
def lower_set.compl (s : lower_set α) : upper_set α := ⟨sᶜ, s.lower.compl⟩

namespace upper_set
variables {s t : upper_set α} {a : α}

@[simp] lemma coe_compl (s : upper_set α) : (s.compl : set α) = sᶜ := rfl
@[simp] lemma mem_compl_iff : a ∈ s.compl ↔ a ∉ s := iff.rfl
@[simp] lemma compl_compl (s : upper_set α) : s.compl.compl = s := upper_set.ext $ compl_compl _
@[simp] lemma compl_le_compl : s.compl ≤ t.compl ↔ s ≤ t := compl_subset_compl

@[simp] protected lemma compl_sup (s t : upper_set α) : (s ⊔ t).compl = s.compl ⊔ t.compl :=
lower_set.ext compl_inf
@[simp] protected lemma compl_inf (s t : upper_set α) : (s ⊓ t).compl = s.compl ⊓ t.compl :=
lower_set.ext compl_sup
@[simp] protected lemma compl_top : (⊤ : upper_set α).compl = ⊤ := lower_set.ext compl_empty
@[simp] protected lemma compl_bot : (⊥ : upper_set α).compl = ⊥  := lower_set.ext compl_univ
@[simp] protected lemma compl_Sup (S : set (upper_set α)) :
  (Sup S).compl = ⨆ s ∈ S, upper_set.compl s :=
lower_set.ext $ by simp only [coe_compl, coe_Sup, compl_Inter₂, lower_set.coe_supr₂]

@[simp] protected lemma compl_Inf (S : set (upper_set α)) :
  (Inf S).compl = ⨅ s ∈ S, upper_set.compl s :=
lower_set.ext $ by simp only [coe_compl, coe_Inf, compl_Union₂, lower_set.coe_infi₂]

@[simp] protected lemma compl_supr (f : ι → upper_set α) : (⨆ i, f i).compl = ⨆ i, (f i).compl :=
lower_set.ext $ by simp only [coe_compl, coe_supr, compl_Inter, lower_set.coe_supr]

@[simp] protected lemma compl_infi (f : ι → upper_set α) : (⨅ i, f i).compl = ⨅ i, (f i).compl :=
lower_set.ext $ by simp only [coe_compl, coe_infi, compl_Union, lower_set.coe_infi]

@[simp] lemma compl_supr₂ (f : Π i, κ i → upper_set α) :
  (⨆ i j, f i j).compl = ⨆ i j, (f i j).compl :=
by simp_rw upper_set.compl_supr

@[simp] lemma compl_infi₂ (f : Π i, κ i → upper_set α) :
  (⨅ i j, f i j).compl = ⨅ i j, (f i j).compl :=
by simp_rw upper_set.compl_infi

end upper_set

namespace lower_set
variables {s t : lower_set α} {a : α}

@[simp] lemma coe_compl (s : lower_set α) : (s.compl : set α) = sᶜ := rfl
@[simp] lemma mem_compl_iff : a ∈ s.compl ↔ a ∉ s := iff.rfl
@[simp] lemma compl_compl (s : lower_set α) : s.compl.compl = s := lower_set.ext $ compl_compl _
@[simp] lemma compl_le_compl : s.compl ≤ t.compl ↔ s ≤ t := compl_subset_compl

protected lemma compl_sup (s t : lower_set α) : (s ⊔ t).compl = s.compl ⊔ t.compl :=
upper_set.ext compl_sup
protected lemma compl_inf (s t : lower_set α) : (s ⊓ t).compl = s.compl ⊓ t.compl :=
upper_set.ext compl_inf
protected lemma compl_top : (⊤ : lower_set α).compl = ⊤ := upper_set.ext compl_univ
protected lemma compl_bot : (⊥ : lower_set α).compl = ⊥ := upper_set.ext compl_empty
protected lemma compl_Sup (S : set (lower_set α)) : (Sup S).compl = ⨆ s ∈ S, lower_set.compl s :=
upper_set.ext $ by simp only [coe_compl, coe_Sup, compl_Union₂, upper_set.coe_supr₂]

protected lemma compl_Inf (S : set (lower_set α)) : (Inf S).compl = ⨅ s ∈ S, lower_set.compl s :=
upper_set.ext $ by simp only [coe_compl, coe_Inf, compl_Inter₂, upper_set.coe_infi₂]

protected lemma compl_supr (f : ι → lower_set α) : (⨆ i, f i).compl = ⨆ i, (f i).compl :=
upper_set.ext $ by simp only [coe_compl, coe_supr, compl_Union, upper_set.coe_supr]

protected lemma compl_infi (f : ι → lower_set α) : (⨅ i, f i).compl = ⨅ i, (f i).compl :=
upper_set.ext $ by simp only [coe_compl, coe_infi, compl_Inter, upper_set.coe_infi]

@[simp] lemma compl_supr₂ (f : Π i, κ i → lower_set α) :
  (⨆ i j, f i j).compl = ⨆ i j, (f i j).compl :=
by simp_rw lower_set.compl_supr

@[simp] lemma compl_infi₂ (f : Π i, κ i → lower_set α) :
  (⨅ i j, f i j).compl = ⨅ i j, (f i j).compl :=
by simp_rw lower_set.compl_infi

end lower_set

/-- Upper sets are order-isomorphic to lower sets under complementation. -/
@[simps] def upper_set_iso_lower_set : upper_set α ≃o lower_set α :=
{ to_fun := upper_set.compl,
  inv_fun := lower_set.compl,
  left_inv := upper_set.compl_compl,
  right_inv := lower_set.compl_compl,
  map_rel_iff' := λ _ _, upper_set.compl_le_compl }

end has_le

/-! #### Map -/

section
variables [preorder α] [preorder β] [preorder γ]

namespace upper_set
variables {f : α ≃o β} {s t : upper_set α} {a : α} {b : β}

/-- An order isomorphism of preorders induces an order isomorphism of their upper sets. -/
def map (f : α ≃o β) : upper_set α ≃o upper_set β :=
{ to_fun := λ s, ⟨f '' s, s.upper.image f⟩,
  inv_fun := λ t, ⟨f ⁻¹' t, t.upper.preimage f.monotone⟩,
  left_inv := λ _, ext $ f.preimage_image _,
  right_inv := λ _, ext $ f.image_preimage _,
  map_rel_iff' := λ s t, image_subset_image_iff f.injective }

@[simp] lemma symm_map (f : α ≃o β) : (map f).symm = map f.symm :=
fun_like.ext _ _ $ λ s, ext $ set.preimage_equiv_eq_image_symm _ _

@[simp] lemma mem_map : b ∈ map f s ↔ f.symm b ∈ s :=
by { rw [←f.symm_symm, ←symm_map, f.symm_symm], refl }

@[simp] lemma map_refl : map (order_iso.refl α) = order_iso.refl _ := by { ext, simp }

@[simp] lemma map_map (g : β ≃o γ) (f : α ≃o β) : map g (map f s) = map (f.trans g) s :=
by { ext, simp }

variables (f s t)

@[simp, norm_cast] lemma coe_map : (map f s : set β) = f '' s := rfl

end upper_set

namespace lower_set
variables {f : α ≃o β} {s t : lower_set α} {a : α} {b : β}

/-- An order isomorphism of preorders induces an order isomorphism of their lower sets. -/
def map (f : α ≃o β) : lower_set α ≃o lower_set β :=
{ to_fun := λ s, ⟨f '' s, s.lower.image f⟩,
  inv_fun := λ t, ⟨f ⁻¹' t, t.lower.preimage f.monotone⟩,
  left_inv := λ _, set_like.coe_injective $ f.preimage_image _,
  right_inv := λ _, set_like.coe_injective $ f.image_preimage _,
  map_rel_iff' := λ s t, image_subset_image_iff f.injective }

@[simp] lemma symm_map (f : α ≃o β) : (map f).symm = map f.symm :=
fun_like.ext _ _ $ λ s, set_like.coe_injective $ set.preimage_equiv_eq_image_symm _ _

@[simp] lemma mem_map {f : α ≃o β} {b : β} : b ∈ map f s ↔ f.symm b ∈ s :=
by { rw [←f.symm_symm, ←symm_map, f.symm_symm], refl }

@[simp] lemma map_refl : map (order_iso.refl α) = order_iso.refl _ := by { ext, simp }

@[simp] lemma map_map (g : β ≃o γ) (f : α ≃o β) : map g (map f s) = map (f.trans g) s :=
by { ext, simp }

variables (f s t)

@[simp, norm_cast] lemma coe_map : (map f s : set β) = f '' s := rfl

end lower_set

namespace upper_set

@[simp] lemma compl_map (f : α ≃o β) (s : upper_set α) :
  (map f s).compl = lower_set.map f s.compl :=
set_like.coe_injective (set.image_compl_eq f.bijective).symm

end upper_set

namespace lower_set

@[simp] lemma compl_map (f : α ≃o β) (s : lower_set α) :
  (map f s).compl = upper_set.map f s.compl :=
set_like.coe_injective (set.image_compl_eq f.bijective).symm

end lower_set

end

/-! #### Principal sets -/

namespace upper_set
section preorder
variables [preorder α] [preorder β] {s : upper_set α} {a b : α}

/-- The smallest upper set containing a given element. -/
def Ici (a : α) : upper_set α := ⟨Ici a, is_upper_set_Ici a⟩

/-- The smallest upper set containing a given element. -/
def Ioi (a : α) : upper_set α := ⟨Ioi a, is_upper_set_Ioi a⟩

@[simp] lemma coe_Ici (a : α) : ↑(Ici a) = set.Ici a := rfl
@[simp] lemma coe_Ioi (a : α) : ↑(Ioi a) = set.Ioi a := rfl
@[simp] lemma mem_Ici_iff : b ∈ Ici a ↔ a ≤ b := iff.rfl
@[simp] lemma mem_Ioi_iff : b ∈ Ioi a ↔ a < b := iff.rfl
@[simp] lemma map_Ici (f : α ≃o β) (a : α) : map f (Ici a) = Ici (f a) := by { ext, simp }
@[simp] lemma map_Ioi (f : α ≃o β) (a : α) : map f (Ioi a) = Ioi (f a) := by { ext, simp }

lemma Ici_le_Ioi (a : α) : Ici a ≤ Ioi a := Ioi_subset_Ici_self

@[simp] lemma Ioi_top [order_top α] : Ioi (⊤ : α) = ⊤ := set_like.coe_injective Ioi_top
@[simp] lemma Ici_bot [order_bot α] : Ici (⊥ : α) = ⊥ := set_like.coe_injective Ici_bot

end preorder

@[simp] lemma Ici_sup [semilattice_sup α] (a b : α) : Ici (a ⊔ b) = Ici a ⊔ Ici b :=
ext Ici_inter_Ici.symm

section complete_lattice
variables [complete_lattice α]

@[simp] lemma Ici_Sup (S : set α) : Ici (Sup S) = ⨆ a ∈ S, Ici a :=
set_like.ext $ λ c, by simp only [mem_Ici_iff, mem_supr_iff, Sup_le_iff]

@[simp] lemma Ici_supr (f : ι → α) : Ici (⨆ i, f i) = ⨆ i, Ici (f i) :=
set_like.ext $ λ c, by simp only [mem_Ici_iff, mem_supr_iff, supr_le_iff]

@[simp] lemma Ici_supr₂ (f : Π i, κ i → α) : Ici (⨆ i j, f i j) = ⨆ i j, Ici (f i j) :=
by simp_rw Ici_supr

end complete_lattice
end upper_set

namespace lower_set
section preorder
variables [preorder α] [preorder β] {s : lower_set α} {a b : α}

/-- Principal lower set. `set.Iic` as a lower set. The smallest lower set containing a given
element. -/
def Iic (a : α) : lower_set α := ⟨Iic a, is_lower_set_Iic a⟩

/-- Strict principal lower set. `set.Iio` as a lower set. -/
def Iio (a : α) : lower_set α := ⟨Iio a, is_lower_set_Iio a⟩

@[simp] lemma coe_Iic (a : α) : ↑(Iic a) = set.Iic a := rfl
@[simp] lemma coe_Iio (a : α) : ↑(Iio a) = set.Iio a := rfl
@[simp] lemma mem_Iic_iff : b ∈ Iic a ↔ b ≤ a := iff.rfl
@[simp] lemma mem_Iio_iff : b ∈ Iio a ↔ b < a := iff.rfl
@[simp] lemma map_Iic (f : α ≃o β) (a : α) : map f (Iic a) = Iic (f a) := by { ext, simp }
@[simp] lemma map_Iio (f : α ≃o β) (a : α) : map f (Iio a) = Iio (f a) := by { ext, simp }

lemma Ioi_le_Ici (a : α) : Ioi a ≤ Ici a := Ioi_subset_Ici_self

@[simp] lemma Iic_top [order_top α] : Iic (⊤ : α) = ⊤ := set_like.coe_injective Iic_top
@[simp] lemma Iio_bot [order_bot α] : Iio (⊥ : α) = ⊥ := set_like.coe_injective Iio_bot

end preorder

@[simp] lemma Iic_inf [semilattice_inf α] (a b : α) : Iic (a ⊓ b) = Iic a ⊓ Iic b :=
set_like.coe_injective Iic_inter_Iic.symm

section complete_lattice
variables [complete_lattice α]

@[simp] lemma Iic_Inf (S : set α) : Iic (Inf S) = ⨅ a ∈ S, Iic a :=
set_like.ext $ λ c, by simp only [mem_Iic_iff, mem_infi₂_iff, le_Inf_iff]

@[simp] lemma Iic_infi (f : ι → α) : Iic (⨅ i, f i) = ⨅ i, Iic (f i) :=
set_like.ext $ λ c, by simp only [mem_Iic_iff, mem_infi_iff, le_infi_iff]

@[simp] lemma Iic_infi₂ (f : Π i, κ i → α) : Iic (⨅ i j, f i j) = ⨅ i j, Iic (f i j) :=
by simp_rw Iic_infi

end complete_lattice
end lower_set

section closure
variables [preorder α] [preorder β] {s t : set α} {x : α}

/-- The greatest upper set containing a given set. -/
def upper_closure (s : set α) : upper_set α :=
⟨{x | ∃ a ∈ s, a ≤ x}, λ x y h, Exists₂.imp $ λ a _, h.trans'⟩

/-- The least lower set containing a given set. -/
def lower_closure (s : set α) : lower_set α :=
⟨{x | ∃ a ∈ s, x ≤ a}, λ x y h, Exists₂.imp $ λ a _, h.trans⟩

@[simp] lemma mem_upper_closure : x ∈ upper_closure s ↔ ∃ a ∈ s, a ≤ x := iff.rfl
@[simp] lemma mem_lower_closure : x ∈ lower_closure s ↔ ∃ a ∈ s, x ≤ a := iff.rfl

-- We do not tag those two as `simp` to respect the abstraction.
@[norm_cast] lemma coe_upper_closure (s : set α) : ↑(upper_closure s) = ⋃ a ∈ s, Ici a :=
by { ext, simp }
@[norm_cast] lemma coe_lower_closure (s : set α) : ↑(lower_closure s) = ⋃ a ∈ s, Iic a :=
by { ext, simp }

lemma subset_upper_closure : s ⊆ upper_closure s := λ x hx, ⟨x, hx, le_rfl⟩
lemma subset_lower_closure : s ⊆ lower_closure s := λ x hx, ⟨x, hx, le_rfl⟩

lemma upper_closure_min (h : s ⊆ t) (ht : is_upper_set t) : ↑(upper_closure s) ⊆ t :=
λ a ⟨b, hb, hba⟩, ht hba $ h hb

lemma lower_closure_min (h : s ⊆ t) (ht : is_lower_set t) : ↑(lower_closure s) ⊆ t :=
λ a ⟨b, hb, hab⟩, ht hab $ h hb

protected lemma is_upper_set.upper_closure (hs : is_upper_set s) : ↑(upper_closure s) = s :=
(upper_closure_min subset.rfl hs).antisymm subset_upper_closure

protected lemma is_lower_set.lower_closure (hs : is_lower_set s) : ↑(lower_closure s) = s :=
(lower_closure_min subset.rfl hs).antisymm subset_lower_closure

@[simp] protected lemma upper_set.upper_closure (s : upper_set α) : upper_closure (s : set α) = s :=
set_like.coe_injective s.2.upper_closure

@[simp] protected lemma lower_set.lower_closure (s : lower_set α) : lower_closure (s : set α) = s :=
set_like.coe_injective s.2.lower_closure

@[simp] lemma upper_closure_image (f : α ≃o β) :
  upper_closure (f '' s) = upper_set.map f (upper_closure s) :=
begin
  rw [←f.symm_symm, ←upper_set.symm_map, f.symm_symm],
  ext,
  simp [-upper_set.symm_map, upper_set.map, order_iso.symm, ←f.le_symm_apply],
end

@[simp] lemma lower_closure_image (f : α ≃o β) :
  lower_closure (f '' s) = lower_set.map f (lower_closure s) :=
begin
  rw [←f.symm_symm, ←lower_set.symm_map, f.symm_symm],
  ext,
  simp [-lower_set.symm_map, lower_set.map, order_iso.symm, ←f.symm_apply_le],
end

@[simp] lemma upper_set.infi_Ici (s : set α) : (⨅ a ∈ s, upper_set.Ici a) = upper_closure s :=
by { ext, simp }

@[simp] lemma lower_set.supr_Iic (s : set α) : (⨆ a ∈ s, lower_set.Iic a) = lower_closure s :=
by { ext, simp }

lemma gc_upper_closure_coe :
  galois_connection (to_dual ∘ upper_closure : set α → (upper_set α)ᵒᵈ) (coe ∘ of_dual) :=
λ s t, ⟨λ h, subset_upper_closure.trans $ upper_set.coe_subset_coe.2 h,
  λ h, upper_closure_min h t.upper⟩

lemma gc_lower_closure_coe : galois_connection (lower_closure : set α → lower_set α) coe :=
λ s t, ⟨λ h, subset_lower_closure.trans $ lower_set.coe_subset_coe.2 h,
  λ h, lower_closure_min h t.lower⟩

/-- `upper_closure` forms a reversed Galois insertion with the coercion from upper sets to sets. -/
def gi_upper_closure_coe :
  galois_insertion (to_dual ∘ upper_closure : set α → (upper_set α)ᵒᵈ) (coe ∘ of_dual) :=
{ choice := λ s hs, to_dual (⟨s, λ a b hab ha, hs ⟨a, ha, hab⟩⟩ : upper_set α),
  gc := gc_upper_closure_coe,
  le_l_u := λ _, subset_upper_closure,
  choice_eq := λ s hs,
    of_dual.injective $ set_like.coe_injective $ subset_upper_closure.antisymm hs }

/-- `lower_closure` forms a Galois insertion with the coercion from lower sets to sets. -/
def gi_lower_closure_coe : galois_insertion (lower_closure : set α → lower_set α) coe :=
{ choice := λ s hs, ⟨s, λ a b hba ha, hs ⟨a, ha, hba⟩⟩,
  gc := gc_lower_closure_coe,
  le_l_u := λ _, subset_lower_closure,
  choice_eq := λ s hs, set_like.coe_injective $ subset_lower_closure.antisymm hs }

lemma upper_closure_anti : antitone (upper_closure : set α → upper_set α) :=
gc_upper_closure_coe.monotone_l

lemma lower_closure_mono : monotone (lower_closure : set α → lower_set α) :=
gc_lower_closure_coe.monotone_l

@[simp] lemma upper_closure_empty : upper_closure (∅ : set α) = ⊤ := by { ext, simp }
@[simp] lemma lower_closure_empty : lower_closure (∅ : set α) = ⊥ := by { ext, simp }

@[simp] lemma upper_closure_singleton (a : α) : upper_closure ({a} : set α) = upper_set.Ici a :=
by { ext, simp }

@[simp] lemma lower_closure_singleton (a : α) : lower_closure ({a} : set α) = lower_set.Iic a :=
by { ext, simp }

@[simp] lemma upper_closure_univ : upper_closure (univ : set α) = ⊥ :=
le_bot_iff.1 subset_upper_closure

@[simp] lemma lower_closure_univ : lower_closure (univ : set α) = ⊤ :=
top_le_iff.1 subset_lower_closure

@[simp] lemma upper_closure_eq_top_iff : upper_closure s = ⊤ ↔ s = ∅ :=
⟨λ h, subset_empty_iff.1 $ subset_upper_closure.trans (congr_arg coe h).subset,
  by { rintro rfl, exact upper_closure_empty }⟩

@[simp] lemma lower_closure_eq_bot_iff : lower_closure s = ⊥ ↔ s = ∅ :=
⟨λ h, subset_empty_iff.1 $ subset_lower_closure.trans (congr_arg coe h).subset,
  by { rintro rfl, exact lower_closure_empty }⟩

@[simp] lemma upper_closure_union (s t : set α) :
  upper_closure (s ∪ t) = upper_closure s ⊓ upper_closure t :=
by { ext, simp [or_and_distrib_right, exists_or_distrib] }

@[simp] lemma lower_closure_union (s t : set α) :
  lower_closure (s ∪ t) = lower_closure s ⊔ lower_closure t :=
by { ext, simp [or_and_distrib_right, exists_or_distrib] }

@[simp] lemma upper_closure_Union (f : ι → set α) :
  upper_closure (⋃ i, f i) = ⨅ i, upper_closure (f i) :=
by { ext, simp [←exists_and_distrib_right, @exists_comm α] }

@[simp] lemma lower_closure_Union (f : ι → set α) :
  lower_closure (⋃ i, f i) = ⨆ i, lower_closure (f i) :=
by { ext, simp [←exists_and_distrib_right, @exists_comm α] }

@[simp] lemma upper_closure_sUnion (S : set (set α)) :
  upper_closure (⋃₀ S) = ⨅ s ∈ S, upper_closure s :=
by simp_rw [sUnion_eq_bUnion, upper_closure_Union]

@[simp] lemma lower_closure_sUnion (S : set (set α)) :
  lower_closure (⋃₀ S) = ⨆ s ∈ S, lower_closure s :=
by simp_rw [sUnion_eq_bUnion, lower_closure_Union]

lemma set.ord_connected.upper_closure_inter_lower_closure (h : s.ord_connected) :
  ↑(upper_closure s) ∩ ↑(lower_closure s) = s :=
(subset_inter subset_upper_closure subset_lower_closure).antisymm' $ λ a ⟨⟨b, hb, hba⟩, c, hc, hac⟩,
  h.out hb hc ⟨hba, hac⟩

lemma ord_connected_iff_upper_closure_inter_lower_closure :
  s.ord_connected ↔ ↑(upper_closure s) ∩ ↑(lower_closure s) = s :=
begin
  refine ⟨set.ord_connected.upper_closure_inter_lower_closure, λ h, _⟩,
  rw ←h,
  exact (upper_set.upper _).ord_connected.inter (lower_set.lower _).ord_connected,
end

end closure

/-! ### Product -/

section preorder
variables [preorder α] [preorder β]

section
variables {s : set α} {t : set β} {x : α × β}

lemma is_upper_set.prod (hs : is_upper_set s) (ht : is_upper_set t) : is_upper_set (s ×ˢ t) :=
λ a b h ha, ⟨hs h.1 ha.1, ht h.2 ha.2⟩

lemma is_lower_set.prod (hs : is_lower_set s) (ht : is_lower_set t) : is_lower_set (s ×ˢ t) :=
λ a b h ha, ⟨hs h.1 ha.1, ht h.2 ha.2⟩

end

namespace upper_set
variables (s s₁ s₂ : upper_set α) (t t₁ t₂ : upper_set β) {x : α × β}

/-- The product of two upper sets as an upper set. -/
def prod : upper_set (α × β) := ⟨s ×ˢ t, s.2.prod t.2⟩

infixr (name := upper_set.prod) ` ×ˢ `:82 := prod

@[simp, norm_cast] lemma coe_prod : (↑(s ×ˢ t) : set (α × β)) = s ×ˢ t := rfl

@[simp] lemma mem_prod {s : upper_set α} {t : upper_set β} : x ∈ s ×ˢ t ↔ x.1 ∈ s ∧ x.2 ∈ t :=
iff.rfl

lemma Ici_prod (x : α × β) : Ici x = Ici x.1 ×ˢ Ici x.2 := rfl
@[simp] lemma Ici_prod_Ici (a : α) (b : β) : Ici a ×ˢ Ici b = Ici (a, b) := rfl

@[simp] lemma prod_top : s ×ˢ (⊤ : upper_set β) = ⊤ := ext prod_empty
@[simp] lemma top_prod : (⊤ : upper_set α) ×ˢ t = ⊤ := ext empty_prod
@[simp] lemma bot_prod_bot : (⊥ : upper_set α) ×ˢ (⊥ : upper_set β) = ⊥ := ext univ_prod_univ
@[simp] lemma sup_prod : (s₁ ⊔ s₂) ×ˢ t = s₁ ×ˢ t ⊔ s₂ ×ˢ t := ext inter_prod
@[simp] lemma prod_sup : s ×ˢ (t₁ ⊔ t₂) = s ×ˢ t₁ ⊔ s ×ˢ t₂ := ext prod_inter
@[simp] lemma inf_prod : (s₁ ⊓ s₂) ×ˢ t = s₁ ×ˢ t ⊓ s₂ ×ˢ t := ext union_prod
@[simp] lemma prod_inf : s ×ˢ (t₁ ⊓ t₂) = s ×ˢ t₁ ⊓ s ×ˢ t₂ := ext prod_union
lemma prod_sup_prod : s₁ ×ˢ t₁ ⊔ s₂ ×ˢ t₂ = (s₁ ⊔ s₂) ×ˢ (t₁ ⊔ t₂) := ext prod_inter_prod

variables {s s₁ s₂ t t₁ t₂}

lemma prod_mono : s₁ ≤ s₂ → t₁ ≤ t₂ → s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ := prod_mono
lemma prod_mono_left : s₁ ≤ s₂ → s₁ ×ˢ t ≤ s₂ ×ˢ t := prod_mono_left
lemma prod_mono_right : t₁ ≤ t₂ → s ×ˢ t₁ ≤ s ×ˢ t₂ := prod_mono_right

@[simp] lemma prod_self_le_prod_self : s₁ ×ˢ s₁ ≤ s₂ ×ˢ s₂ ↔ s₁ ≤ s₂ := prod_self_subset_prod_self
@[simp] lemma prod_self_lt_prod_self : s₁ ×ˢ s₁ < s₂ ×ˢ s₂ ↔ s₁ < s₂ := prod_self_ssubset_prod_self

lemma prod_le_prod_iff : s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ ↔ s₁ ≤ s₂ ∧ t₁ ≤ t₂ ∨ s₂ = ⊤ ∨ t₂ = ⊤ :=
prod_subset_prod_iff.trans $ by simp

@[simp] lemma prod_eq_top : s ×ˢ t = ⊤ ↔ s = ⊤ ∨ t = ⊤ :=
by { simp_rw set_like.ext'_iff, exact prod_eq_empty_iff }

@[simp] lemma codisjoint_prod :
  codisjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ codisjoint s₁ s₂ ∨ codisjoint t₁ t₂ :=
by simp_rw [codisjoint_iff, prod_sup_prod, prod_eq_top]

end upper_set

namespace lower_set
variables (s s₁ s₂ : lower_set α) (t t₁ t₂ : lower_set β) {x : α × β}

/-- The product of two lower sets as a lower set. -/
def prod : lower_set (α × β) := ⟨s ×ˢ t, s.2.prod t.2⟩

infixr (name := lower_set.prod) ` ×ˢ `:82 := lower_set.prod

@[simp, norm_cast] lemma coe_prod : (↑(s ×ˢ t) : set (α × β)) = s ×ˢ t := rfl

@[simp] lemma mem_prod {s : lower_set α} {t : lower_set β} : x ∈ s ×ˢ t ↔ x.1 ∈ s ∧ x.2 ∈ t :=
iff.rfl

lemma Iic_prod (x : α × β) : Iic x = Iic x.1 ×ˢ Iic x.2 := rfl
@[simp] lemma Ici_prod_Ici (a : α) (b : β) : Iic a ×ˢ Iic b = Iic (a, b) := rfl

@[simp] lemma prod_bot : s ×ˢ (⊥ : lower_set β) = ⊥ := ext prod_empty
@[simp] lemma bot_prod : (⊥ : lower_set α) ×ˢ t = ⊥ := ext empty_prod
@[simp] lemma top_prod_top : (⊤ : lower_set α) ×ˢ (⊤ : lower_set β) = ⊤ := ext univ_prod_univ
@[simp] lemma inf_prod : (s₁ ⊓ s₂) ×ˢ t = s₁ ×ˢ t ⊓ s₂ ×ˢ t := ext inter_prod
@[simp] lemma prod_inf : s ×ˢ (t₁ ⊓ t₂) = s ×ˢ t₁ ⊓ s ×ˢ t₂ := ext prod_inter
@[simp] lemma sup_prod : (s₁ ⊔ s₂) ×ˢ t = s₁ ×ˢ t ⊔ s₂ ×ˢ t := ext union_prod
@[simp] lemma prod_sup : s ×ˢ (t₁ ⊔ t₂) = s ×ˢ t₁ ⊔ s ×ˢ t₂ := ext prod_union
lemma prod_inf_prod : s₁ ×ˢ t₁ ⊓ s₂ ×ˢ t₂ = (s₁ ⊓ s₂) ×ˢ (t₁ ⊓ t₂) := ext prod_inter_prod

variables {s s₁ s₂ t t₁ t₂}

lemma prod_mono : s₁ ≤ s₂ → t₁ ≤ t₂ → s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ := prod_mono
lemma prod_mono_left : s₁ ≤ s₂ → s₁ ×ˢ t ≤ s₂ ×ˢ t := prod_mono_left
lemma prod_mono_right : t₁ ≤ t₂ → s ×ˢ t₁ ≤ s ×ˢ t₂ := prod_mono_right

@[simp] lemma prod_self_le_prod_self : s₁ ×ˢ s₁ ≤ s₂ ×ˢ s₂ ↔ s₁ ≤ s₂ := prod_self_subset_prod_self
@[simp] lemma prod_self_lt_prod_self : s₁ ×ˢ s₁ < s₂ ×ˢ s₂ ↔ s₁ < s₂ := prod_self_ssubset_prod_self

lemma prod_le_prod_iff : s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ ↔ s₁ ≤ s₂ ∧ t₁ ≤ t₂ ∨ s₁ = ⊥ ∨ t₁ = ⊥ :=
prod_subset_prod_iff.trans $ by simp

@[simp] lemma prod_eq_bot : s ×ˢ t = ⊥ ↔ s = ⊥ ∨ t = ⊥ :=
by { simp_rw set_like.ext'_iff, exact prod_eq_empty_iff }

@[simp] lemma disjoint_prod : disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ disjoint s₁ s₂ ∨ disjoint t₁ t₂ :=
by simp_rw [disjoint_iff, prod_inf_prod, prod_eq_bot]

end lower_set

@[simp] lemma upper_closure_prod (s : set α) (t : set β) :
  upper_closure (s ×ˢ t) = upper_closure s ×ˢ upper_closure t :=
by { ext, simp [prod.le_def, and_and_and_comm _ (_ ∈ t)] }

@[simp] lemma lower_closure_prod (s : set α) (t : set β) :
  lower_closure (s ×ˢ t) = lower_closure s ×ˢ lower_closure t :=
by { ext, simp [prod.le_def, and_and_and_comm _ (_ ∈ t)] }

end preorder
