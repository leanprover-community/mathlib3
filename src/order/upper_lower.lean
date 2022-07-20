/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
import data.set_like.basic
import order.hom.complete_lattice

/-!
# Up-sets and down-sets

This file defines upper and lower sets in an order.

## Main declarations

* `is_upper_set`: Predicate for a set to be an upper set. This means every element greater than a
  member of the set is in the set itself.
* `is_lower_set`: Predicate for a set to be a lower set. This means every element less than a member
  of the set is in the set itself.
* `upper_set`: The type of upper sets.
* `lower_set`: The type of lower sets.
* `upper_set.Ici`: Principal upper set. `set.Ici` as an upper set.
* `upper_set.Ioi`: Strict principal upper set. `set.Ioi` as an upper set.
* `lower_set.Iic`: Principal lower set. `set.Iic` as an lower set.
* `lower_set.Iio`: Strict principal lower set. `set.Iio` as an lower set.

## Notes

Upper sets are ordered by **reverse** inclusion. This convention is motivated by the fact that this
makes them order-isomorphic to lower sets and antichains, and matches the convention on `filter`.

## TODO

Lattice structure on antichains. Order equivalence between upper/lower sets and antichains.
-/

open order_dual set

variables {α : Type*} {ι : Sort*} {κ : ι → Sort*}

/-! ### Unbundled upper/lower sets -/

section has_le
variables [has_le α] {s t : set α}

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
variables [preorder α] (a : α)

lemma is_upper_set_Ici : is_upper_set (Ici a) := λ _ _, ge_trans
lemma is_lower_set_Iic : is_lower_set (Iic a) := λ _ _, le_trans
lemma is_upper_set_Ioi : is_upper_set (Ioi a) := λ _ _, flip lt_of_lt_of_le
lemma is_lower_set_Iio : is_lower_set (Iio a) := λ _ _, lt_of_le_of_lt

section order_top
variables [order_top α] {s : set α}

lemma is_lower_set.top_mem (hs : is_lower_set s) : ⊤ ∈ s ↔ s = univ :=
⟨λ h, eq_univ_of_forall $ λ a, hs le_top h, λ h, h.symm ▸ mem_univ _⟩

lemma is_upper_set.top_mem (hs : is_upper_set s) : ⊤ ∈ s ↔ s.nonempty :=
⟨λ h, ⟨_, h⟩, λ ⟨a, ha⟩, hs le_top ha⟩

lemma is_upper_set.not_top_mem (hs : is_upper_set s) : ⊤ ∉ s ↔ s = ∅ :=
hs.top_mem.not.trans not_nonempty_iff_eq_empty

end order_top

section order_bot
variables [order_bot α] {s : set α}

lemma is_upper_set.bot_mem (hs : is_upper_set s) : ⊥ ∈ s ↔ s = univ :=
⟨λ h, eq_univ_of_forall $ λ a, hs bot_le h, λ h, h.symm ▸ mem_univ _⟩

lemma is_lower_set.bot_mem (hs : is_lower_set s) : ⊥ ∈ s ↔ s.nonempty :=
⟨λ h, ⟨_, h⟩, λ ⟨a, ha⟩, hs bot_le ha⟩

lemma is_lower_set.not_bot_mem (hs : is_lower_set s) : ⊥ ∉ s ↔ s = ∅ :=
hs.bot_mem.not.trans not_nonempty_iff_eq_empty

end order_bot
end preorder

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

end upper_set

namespace lower_set

instance : set_like (lower_set α) α :=
{ coe := lower_set.carrier,
  coe_injective' := λ s t h, by { cases s, cases t, congr' } }

@[ext] lemma ext {s t : lower_set α} : (s : set α) = t → s = t := set_like.ext'

@[simp] lemma carrier_eq_coe (s : lower_set α) : s.carrier = s := rfl

protected lemma lower (s : lower_set α) : is_lower_set (s : set α) := s.lower'

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

@[simp] lemma coe_top : ((⊤ : upper_set α) : set α) = ∅ := rfl
@[simp] lemma coe_bot : ((⊥ : upper_set α) : set α) = univ := rfl
@[simp] lemma coe_sup (s t : upper_set α) : (↑(s ⊔ t) : set α) = s ∩ t := rfl
@[simp] lemma coe_inf (s t : upper_set α) : (↑(s ⊓ t) : set α) = s ∪ t := rfl
@[simp] lemma coe_Sup (S : set (upper_set α)) : (↑(Sup S) : set α) = ⋂ s ∈ S, ↑s := rfl
@[simp] lemma coe_Inf (S : set (upper_set α)) : (↑(Inf S) : set α) = ⋃ s ∈ S, ↑s := rfl
@[simp] lemma coe_supr (f : ι → upper_set α) : (↑(⨆ i, f i) : set α) = ⋂ i, f i := by simp [supr]
@[simp] lemma coe_infi (f : ι → upper_set α) : (↑(⨅ i, f i) : set α) = ⋃ i, f i := by simp [infi]
@[simp] lemma coe_supr₂ (f : Π i, κ i → upper_set α) : (↑(⨆ i j, f i j) : set α) = ⋂ i j, f i j :=
by simp_rw coe_supr
@[simp] lemma coe_infi₂ (f : Π i, κ i → upper_set α) : (↑(⨅ i j, f i j) : set α) = ⋃ i j, f i j :=
by simp_rw coe_infi

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

@[simp] lemma coe_top : ((⊤ : lower_set α) : set α) = univ := rfl
@[simp] lemma coe_bot : ((⊥ : lower_set α) : set α) = ∅ := rfl
@[simp] lemma coe_sup (s t : lower_set α) : (↑(s ⊔ t) : set α) = s ∪ t := rfl
@[simp] lemma coe_inf (s t : lower_set α) : (↑(s ⊓ t) : set α) = s ∩ t := rfl
@[simp] lemma coe_Sup (S : set (lower_set α)) : (↑(Sup S) : set α) = ⋃ s ∈ S, ↑s := rfl
@[simp] lemma coe_Inf (S : set (lower_set α)) : (↑(Inf S) : set α) = ⋂ s ∈ S, ↑s := rfl
@[simp] lemma coe_supr (f : ι → lower_set α) : (↑(⨆ i, f i) : set α) = ⋃ i, f i :=
by simp_rw [supr, coe_Sup, mem_range, Union_exists, Union_Union_eq']
@[simp] lemma coe_infi (f : ι → lower_set α) : (↑(⨅ i, f i) : set α) = ⋂ i, f i :=
by simp_rw [infi, coe_Inf, mem_range, Inter_exists, Inter_Inter_eq']
@[simp] lemma coe_supr₂ (f : Π i, κ i → lower_set α) : (↑(⨆ i j, f i j) : set α) = ⋃ i j, f i j :=
by simp_rw coe_supr
@[simp] lemma coe_infi₂ (f : Π i, κ i → lower_set α) : (↑(⨅ i j, f i j) : set α) = ⋂ i j, f i j :=
by simp_rw coe_infi

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

/-! #### Principal sets -/

namespace upper_set
section preorder
variables [preorder α] {a b : α}

/-- The smallest upper set containing a given element. -/
def Ici (a : α) : upper_set α := ⟨Ici a, is_upper_set_Ici a⟩

/-- The smallest upper set containing a given element. -/
def Ioi (a : α) : upper_set α := ⟨Ioi a, is_upper_set_Ioi a⟩

@[simp] lemma coe_Ici (a : α) : ↑(Ici a) = set.Ici a := rfl
@[simp] lemma coe_Ioi (a : α) : ↑(Ioi a) = set.Ioi a := rfl
@[simp] lemma mem_Ici_iff : b ∈ Ici a ↔ a ≤ b := iff.rfl
@[simp] lemma mem_Ioi_iff : b ∈ Ioi a ↔ a < b := iff.rfl

lemma Ici_le_Ioi (a : α) : Ici a ≤ Ioi a := Ioi_subset_Ici_self

@[simp] lemma Ioi_top [order_top α] : Ioi (⊤ : α) = ⊤ := set_like.coe_injective Ioi_top
@[simp] lemma Ici_bot [order_bot α] : Ici (⊥ : α) = ⊥ := set_like.coe_injective Ici_bot

end preorder

section semilattice_sup
variables [semilattice_sup α]

@[simp] lemma Ici_sup (a b : α) : Ici (a ⊔ b) = Ici a ⊔ Ici b := ext Ici_inter_Ici.symm

/-- `upper_set.Ici` as a `sup_hom`. -/
def Ici_sup_hom : sup_hom α (upper_set α) := ⟨Ici, Ici_sup⟩

@[simp] lemma Ici_sup_hom_apply (a : α) : Ici_sup_hom a = (Ici a) := rfl

end semilattice_sup

section complete_lattice
variables [complete_lattice α]

@[simp] lemma Ici_Sup (S : set α) : Ici (Sup S) = ⨆ a ∈ S, Ici a :=
set_like.ext $ λ c, by simp only [mem_Ici_iff, mem_supr_iff, Sup_le_iff]

@[simp] lemma Ici_supr (f : ι → α) : Ici (⨆ i, f i) = ⨆ i, Ici (f i) :=
set_like.ext $ λ c, by simp only [mem_Ici_iff, mem_supr_iff, supr_le_iff]

@[simp] lemma Ici_supr₂ (f : Π i, κ i → α) : Ici (⨆ i j, f i j) = ⨆ i j, Ici (f i j) :=
by simp_rw Ici_supr

/-- `upper_set.Ici` as a `Sup_hom`. -/
def Ici_Sup_hom : Sup_hom α (upper_set α) := ⟨Ici, λ s, (Ici_Sup s).trans Sup_image.symm⟩

@[simp] lemma Ici_Sup_hom_apply (a : α) : Ici_Sup_hom a = to_dual (Ici a) := rfl

end complete_lattice
end upper_set

namespace lower_set
section preorder
variables [preorder α] {a b : α}

/-- Principal lower set. `set.Iic` as a lower set. The smallest lower set containing a given
element. -/
def Iic (a : α) : lower_set α := ⟨Iic a, is_lower_set_Iic a⟩

/-- Strict principal lower set. `set.Iio` as a lower set. -/
def Iio (a : α) : lower_set α := ⟨Iio a, is_lower_set_Iio a⟩

@[simp] lemma coe_Iic (a : α) : ↑(Iic a) = set.Iic a := rfl
@[simp] lemma coe_Iio (a : α) : ↑(Iio a) = set.Iio a := rfl
@[simp] lemma mem_Iic_iff : b ∈ Iic a ↔ b ≤ a := iff.rfl
@[simp] lemma mem_Iio_iff : b ∈ Iio a ↔ b < a := iff.rfl

lemma Ioi_le_Ici (a : α) : Ioi a ≤ Ici a := Ioi_subset_Ici_self

@[simp] lemma Iic_top [order_top α] : Iic (⊤ : α) = ⊤ := set_like.coe_injective Iic_top
@[simp] lemma Iio_bot [order_bot α] : Iio (⊥ : α) = ⊥ := set_like.coe_injective Iio_bot

end preorder

section semilattice_inf
variables [semilattice_inf α]

@[simp] lemma Iic_inf (a b : α) : Iic (a ⊓ b) = Iic a ⊓ Iic b :=
set_like.coe_injective Iic_inter_Iic.symm

/-- `lower_set.Iic` as an `inf_hom`. -/
def Iic_inf_hom : inf_hom α (lower_set α) := ⟨Iic, Iic_inf⟩

@[simp] lemma coe_Iic_inf_hom : (Iic_inf_hom : α → lower_set α) = Iic := rfl
@[simp] lemma Iic_inf_hom_apply (a : α) : Iic_inf_hom a = Iic a := rfl

end semilattice_inf

section complete_lattice
variables [complete_lattice α]

@[simp] lemma Iic_Inf (S : set α) : Iic (Inf S) = ⨅ a ∈ S, Iic a :=
set_like.ext $ λ c, by simp only [mem_Iic_iff, mem_infi₂_iff, le_Inf_iff]

@[simp] lemma Iic_infi (f : ι → α) : Iic (⨅ i, f i) = ⨅ i, Iic (f i) :=
set_like.ext $ λ c, by simp only [mem_Iic_iff, mem_infi_iff, le_infi_iff]

@[simp] lemma Iic_infi₂ (f : Π i, κ i → α) : Iic (⨅ i j, f i j) = ⨅ i j, Iic (f i j) :=
by simp_rw Iic_infi

/-- `lower_set.Iic` as an `Inf_hom`. -/
def Iic_Inf_hom : Inf_hom α (lower_set α) := ⟨Iic, λ s, (Iic_Inf s).trans Inf_image.symm⟩

@[simp] lemma coe_Iic_Inf_hom : (Iic_Inf_hom : α → lower_set α) = Iic := rfl
@[simp] lemma Iic_Inf_hom_apply (a : α) : Iic_Inf_hom a = Iic a := rfl

end complete_lattice
end lower_set
