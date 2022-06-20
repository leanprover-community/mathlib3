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
* `upper_set.map`: The image of an upper set under an order isormorphism.
* `upper_set.comap`: The preimage of an upper set under an order homormorphism.
* `lower_set.map`: The image of a lower set under an order isormorphism.
* `lower_set.comap`: The preimage of a lower set under an order homormorphism.
* `upper_set.compl`: The complement of an upper set, as a lower set.
* `upper_set.map_compl`: The image of an upper set in a boolean algebra under complementation,
  as a lower set.
* `lower_set.compl`: The complement of a lower set, as an upper set.
* `lower_set.map_compl`: The image of a lower set in a boolean algebra under complementation,
  as a lower set.
* `upper_set.to_dual`: An upper set, as a lower set in the dual order.
* `upper_set.of_dual`: An upper set in the dual order, as a lower set.
* `lower_set.to_dual`: A lower set, as an upper set in the dual order.
* `lower_set.of_dual`: A lower set in the dual order, as an upper set.
* `upper_set.Ici`: Principal upper set. `set.Ici` as an upper set.
* `upper_set.Ioi`: Strict principal upper set. `set.Ioi` as an upper set.
* `lower_set.Iic`: Principal lower set. `set.Iic` as an lower set.
* `lower_set.Iio`: Strict principal lower set. `set.Iio` as an lower set.

## TODO

Lattice structure on antichains. Order equivalence between upper/lower sets and antichains.
-/
universes u v w

open order_dual set

variables {α : Type u} {β : Type v} {ι : Sort*} {κ : ι → Sort*} {F : Type w}
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

lemma is_lower_set.map [has_le α] [has_le β] [order_iso_class F α β] {s : set α}
(hs : is_lower_set s) (φ : F) :
  is_lower_set ((φ : α → β) '' s) :=
λ x y h ⟨x',hxs,hxx'⟩, ⟨equiv_like.inv φ y,
  hs ((map_inv_le_iff φ).mpr (hxx'.symm.subst h)) hxs, equiv_like.right_inv _ _⟩

lemma is_upper_set.map [has_le α] [has_le β] [order_iso_class F α β] {s : set α}
(hs : is_upper_set s) (φ : F) :
  is_upper_set ((φ : α → β) '' s) :=
λ x y h ⟨x',hxs,hxx'⟩, ⟨equiv_like.inv φ y,hs
  ((le_map_inv_iff φ).mpr (hxx'.symm.subst h)) hxs, equiv_like.right_inv _ _⟩

end has_le

section preorder
variables [preorder α] [preorder β] [order_hom_class F α β] {t : set β}

lemma is_upper_set_Ici (a : α) : is_upper_set (Ici a) := λ _ _, ge_trans
lemma is_lower_set_Iic (a : α) : is_lower_set (Iic a) := λ _ _, le_trans
lemma is_upper_set_Ioi (a : α) : is_upper_set (Ioi a) := λ _ _, flip lt_of_lt_of_le
lemma is_lower_set_Iio (a : α) : is_lower_set (Iio a) := λ _ _, lt_of_le_of_lt

lemma is_lower_set.comap (ht : is_lower_set t) (φ : F) : is_lower_set ((φ : α → β) ⁻¹' t) :=
λ x y h hx, ht (order_hom_class.mono φ h) hx

lemma is_upper_set.comap (ht : is_upper_set t) (φ : F) : is_upper_set ((φ : α → β) ⁻¹' t) :=
λ x y h hx, ht (order_hom_class.mono φ h) hx

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

instance : has_sup (upper_set α) := ⟨λ s t, ⟨s ∪ t, s.upper.union t.upper⟩⟩
instance : has_inf (upper_set α) := ⟨λ s t, ⟨s ∩ t, s.upper.inter t.upper⟩⟩
instance : has_top (upper_set α) := ⟨⟨univ, is_upper_set_univ⟩⟩
instance : has_bot (upper_set α) := ⟨⟨∅, is_upper_set_empty⟩⟩
instance : has_Sup (upper_set α) :=
⟨λ S, ⟨⋃ s ∈ S, ↑s, is_upper_set_Union₂ $ λ s _, s.upper⟩⟩
instance : has_Inf (upper_set α) :=
⟨λ S, ⟨⋂ s ∈ S, ↑s, is_upper_set_Inter₂ $ λ s _, s.upper⟩⟩

instance : complete_distrib_lattice (upper_set α) :=
set_like.coe_injective.complete_distrib_lattice _
  (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _, rfl) rfl rfl

instance : inhabited (upper_set α) := ⟨⊥⟩

@[simp] lemma coe_top : ((⊤ : upper_set α) : set α) = univ := rfl
@[simp] lemma coe_bot : ((⊥ : upper_set α) : set α) = ∅ := rfl
@[simp] lemma coe_sup (s t : upper_set α) : (↑(s ⊔ t) : set α) = s ∪ t := rfl
@[simp] lemma coe_inf (s t : upper_set α) : (↑(s ⊓ t) : set α) = s ∩ t := rfl
@[simp] lemma coe_Sup (S : set (upper_set α)) : (↑(Sup S) : set α) = ⋃ s ∈ S, ↑s := rfl
@[simp] lemma coe_Inf (S : set (upper_set α)) : (↑(Inf S) : set α) = ⋂ s ∈ S, ↑s := rfl
@[simp] lemma coe_supr (f : ι → upper_set α) : (↑(⨆ i, f i) : set α) = ⋃ i, f i := by simp [supr]
@[simp] lemma coe_infi (f : ι → upper_set α) : (↑(⨅ i, f i) : set α) = ⋂ i, f i := by simp [infi]
@[simp] lemma coe_supr₂ (f : Π i, κ i → upper_set α) : (↑(⨆ i j, f i j) : set α) = ⋃ i j, f i j :=
by simp_rw coe_supr
@[simp] lemma coe_infi₂ (f : Π i, κ i → upper_set α) : (↑(⨅ i j, f i j) : set α) = ⋂ i j, f i j :=
by simp_rw coe_infi

@[simp] lemma mem_top : a ∈ (⊤ : upper_set α) := trivial
@[simp] lemma not_mem_bot : a ∉ (⊥ : upper_set α) := id
@[simp] lemma mem_sup_iff : a ∈ s ⊔ t ↔ a ∈ s ∨ a ∈ t := iff.rfl
@[simp] lemma mem_inf_iff : a ∈ s ⊓ t ↔ a ∈ s ∧ a ∈ t := iff.rfl
@[simp] lemma mem_Sup_iff : a ∈ Sup S ↔ ∃ s ∈ S, a ∈ s := mem_Union₂
@[simp] lemma mem_Inf_iff  : a ∈ Inf S ↔ ∀ s ∈ S, a ∈ s := mem_Inter₂
@[simp] lemma mem_supr_iff {f : ι → upper_set α} : a ∈ (⨆ i, f i) ↔ ∃ i, a ∈ f i :=
by { rw [←set_like.mem_coe, coe_supr], exact mem_Union }
@[simp] lemma mem_infi_iff {f : ι → upper_set α} : a ∈ (⨅ i, f i) ↔ ∀ i, a ∈ f i :=
by { rw [←set_like.mem_coe, coe_infi], exact mem_Inter }
@[simp] lemma mem_supr₂_iff {f : Π i, κ i → upper_set α} : a ∈ (⨆ i j, f i j) ↔ ∃ i j, a ∈ f i j :=
by simp_rw mem_supr_iff
@[simp] lemma mem_infi₂_iff {f : Π i, κ i → upper_set α} : a ∈ (⨅ i j, f i j) ↔ ∀ i j, a ∈ f i j :=
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
variables {s : upper_set α} {a : α}

@[simp] lemma coe_compl (s : upper_set α) : (s.compl : set α) = sᶜ := rfl
@[simp] lemma mem_compl_iff : a ∈ s.compl ↔ a ∉ s := iff.rfl
@[simp] lemma compl_compl (s : upper_set α) : s.compl.compl = s := upper_set.ext $ compl_compl _

@[simp] protected lemma compl_sup (s t : upper_set α) : (s ⊔ t).compl = s.compl ⊓ t.compl :=
lower_set.ext compl_sup
@[simp] protected lemma compl_inf (s t : upper_set α) : (s ⊓ t).compl = s.compl ⊔ t.compl :=
lower_set.ext compl_inf
@[simp] protected lemma compl_top : (⊤ : upper_set α).compl = ⊥ := lower_set.ext compl_univ
@[simp] protected lemma compl_bot : (⊥ : upper_set α).compl = ⊤ := lower_set.ext compl_empty
@[simp] protected lemma compl_Sup (S : set (upper_set α)) :
  (Sup S).compl = ⨅ s ∈ S, upper_set.compl s :=
lower_set.ext $ by simp only [coe_compl, coe_Sup, compl_Union₂, lower_set.coe_infi₂]

@[simp] protected lemma compl_Inf (S : set (upper_set α)) :
  (Inf S).compl = ⨆ s ∈ S, upper_set.compl s :=
lower_set.ext $ by simp only [coe_compl, coe_Inf, compl_Inter₂, lower_set.coe_supr₂]

@[simp] protected lemma compl_supr (f : ι → upper_set α) : (⨆ i, f i).compl = ⨅ i, (f i).compl :=
lower_set.ext $ by simp only [coe_compl, coe_supr, compl_Union, lower_set.coe_infi]

@[simp] protected lemma compl_infi (f : ι → upper_set α) : (⨅ i, f i).compl = ⨆ i, (f i).compl :=
lower_set.ext $ by simp only [coe_compl, coe_infi, compl_Inter, lower_set.coe_supr]

@[simp] lemma compl_supr₂ (f : Π i, κ i → upper_set α) :
  (⨆ i j, f i j).compl = ⨅ i j, (f i j).compl :=
by simp_rw upper_set.compl_supr

@[simp] lemma compl_infi₂ (f : Π i, κ i → upper_set α) :
  (⨅ i j, f i j).compl =  ⨆ i j, (f i j).compl :=
by simp_rw upper_set.compl_infi

end upper_set

namespace lower_set
variables {s : lower_set α} {a : α}

@[simp] lemma coe_compl (s : lower_set α) : (s.compl : set α) = sᶜ := rfl
@[simp] lemma mem_compl_iff : a ∈ s.compl ↔ a ∉ s := iff.rfl
@[simp] lemma compl_compl (s : lower_set α) : s.compl.compl = s := lower_set.ext $ compl_compl _

protected lemma compl_sup (s t : lower_set α) : (s ⊔ t).compl = s.compl ⊓ t.compl :=
upper_set.ext compl_sup
protected lemma compl_inf (s t : lower_set α) : (s ⊓ t).compl = s.compl ⊔ t.compl :=
upper_set.ext compl_inf
protected lemma compl_top : (⊤ : lower_set α).compl = ⊥ := upper_set.ext compl_univ
protected lemma compl_bot : (⊥ : lower_set α).compl = ⊤ := upper_set.ext compl_empty
protected lemma compl_Sup (S : set (lower_set α)) : (Sup S).compl = ⨅ s ∈ S, lower_set.compl s :=
upper_set.ext $ by simp only [coe_compl, coe_Sup, compl_Union₂, upper_set.coe_infi₂]

protected lemma compl_Inf (S : set (lower_set α)) : (Inf S).compl = ⨆ s ∈ S, lower_set.compl s :=
upper_set.ext $ by simp only [coe_compl, coe_Inf, compl_Inter₂, upper_set.coe_supr₂]

protected lemma compl_supr (f : ι → lower_set α) : (⨆ i, f i).compl = ⨅ i, (f i).compl :=
upper_set.ext $ by simp only [coe_compl, coe_supr, compl_Union, upper_set.coe_infi]

protected lemma compl_infi (f : ι → lower_set α) : (⨅ i, f i).compl = ⨆ i, (f i).compl :=
upper_set.ext $ by simp only [coe_compl, coe_infi, compl_Inter, upper_set.coe_supr]

@[simp] lemma compl_supr₂ (f : Π i, κ i → lower_set α) :
  (⨆ i j, f i j).compl = ⨅ i j, (f i j).compl :=
by simp_rw lower_set.compl_supr

@[simp] lemma compl_infi₂ (f : Π i, κ i → lower_set α) :
  (⨅ i j, f i j).compl =  ⨆ i j, (f i j).compl :=
by simp_rw lower_set.compl_infi

end lower_set

/- #### Duals -/

/-- An `upper_set` as a `lower_set` in the dual order. -/
protected def upper_set.to_dual (s : upper_set α) : lower_set αᵒᵈ :=
  ⟨of_dual ⁻¹' s, s.upper.of_dual⟩

/-- An `upper_set` in the dual order as a `lower_set`. -/
protected def upper_set.of_dual (s : upper_set αᵒᵈ) : lower_set α :=
  ⟨order_dual.to_dual ⁻¹' s, s.upper.to_dual⟩

namespace upper_set

@[simp] protected lemma coe_to_dual (s : upper_set α) :
  (s.to_dual : set αᵒᵈ) = order_dual.of_dual ⁻¹' s := rfl
@[simp] protected lemma coe_of_dual (s : upper_set αᵒᵈ) :
  (s.of_dual : set α) = order_dual.to_dual ⁻¹' s := rfl

@[simp] protected lemma to_dual_bot : (⊥ : upper_set α).to_dual = ⊥ := rfl
@[simp] protected lemma to_dual_top : (⊤ : upper_set α).to_dual = ⊤ := rfl
@[simp] protected lemma of_dual_bot : (⊥ : upper_set αᵒᵈ).to_dual = ⊥ := rfl
@[simp] protected lemma of_dual_top : (⊤ : upper_set αᵒᵈ).to_dual = ⊤ := rfl

@[simp] protected lemma to_dual_inf (s t : upper_set α) :
  (s ⊓ t).to_dual = s.to_dual ⊓ t.to_dual := rfl
@[simp] protected lemma to_dual_sup (s t : upper_set α) :
  (s ⊓ t).to_dual = s.to_dual ⊓ t.to_dual := rfl
@[simp] protected lemma of_dual_inf (s t : upper_set αᵒᵈ) :
  (s ⊓ t).of_dual = s.of_dual ⊓ t.of_dual := rfl
@[simp] protected lemma of_dual_sup (s t : upper_set αᵒᵈ) :
  (s ⊔ t).of_dual = s.of_dual ⊔ t.of_dual := rfl

@[simp] protected lemma to_dual_Inf (S : set (upper_set α)) :
  (Inf S).to_dual = Inf (upper_set.to_dual '' S) := set_like.coe_injective (by simpa)
@[simp] protected lemma to_dual_Sup (S : set (upper_set α)) :
  (Sup S).to_dual = Sup (upper_set.to_dual '' S) := set_like.coe_injective (by simp)
@[simp] protected lemma of_dual_Inf (S : set (upper_set αᵒᵈ)) :
  (Inf S).of_dual = Inf (upper_set.of_dual '' S) := set_like.coe_injective (by simpa)
@[simp] protected lemma of_dual_Sup (S : set (upper_set αᵒᵈ)) :
  (Sup S).of_dual = Sup (upper_set.of_dual '' S) := set_like.coe_injective (by simp)

@[simp] protected lemma to_dual_supr (f : ι → upper_set α) :
  (⨆ i, f i).to_dual = ⨆ i, (f i).to_dual := set_like.coe_injective (by simp)
@[simp] protected lemma to_dual_infi (f : ι → upper_set α) :
  (⨅ i, f i).to_dual = ⨅ i, (f i).to_dual := set_like.coe_injective (by simpa)
@[simp] protected lemma of_dual_supr (f : ι → upper_set αᵒᵈ) :
  (⨆ i, f i).of_dual = ⨆ i, (f i).of_dual := set_like.coe_injective (by simp)
@[simp] protected lemma of_dual_infi (f : ι → upper_set αᵒᵈ) :
  (⨅ i, f i).of_dual = ⨅ i, (f i).of_dual := set_like.coe_injective (by simpa)

@[simp] protected lemma to_dual_infi₂ (f : Π i, κ i → upper_set α) :
  (⨅ i j, f i j).to_dual = (⨅ i j, (f i j).to_dual) := set_like.coe_injective (by simp)
@[simp] protected lemma to_dual_supr₂ (f : Π i, κ i → upper_set α) :
  (⨆ i j, f i j).to_dual = (⨆ i j, (f i j).to_dual) := set_like.coe_injective (by simp)
@[simp] protected lemma of_dual_infi₂ (f : Π i, κ i → upper_set αᵒᵈ) :
  (⨅ i j, f i j).of_dual = (⨅ i j, (f i j).of_dual) := set_like.coe_injective (by simp)
@[simp] protected lemma of_dual_supr₂ (f : Π i, κ i → upper_set αᵒᵈ) :
  (⨆ i j, f i j).of_dual = (⨆ i j, (f i j).of_dual) := set_like.coe_injective (by simp)

end upper_set

namespace lower_set

/-- A `lower_set` as an `upper_set` in the dual order. -/
protected def to_dual (s : lower_set α) : upper_set αᵒᵈ := ⟨of_dual ⁻¹' s, s.lower.of_dual⟩

/-- A `lower_set` in the dual order as an `upper_set`. -/
protected def of_dual (s : lower_set αᵒᵈ) : upper_set α :=
  ⟨(order_dual.to_dual : α → αᵒᵈ) ⁻¹' s, s.lower.to_dual⟩

@[simp] protected lemma coe_to_dual (s : lower_set α) :
  (s.to_dual : set αᵒᵈ) = order_dual.of_dual ⁻¹' s := rfl
@[simp] protected lemma coe_of_dual (s : lower_set αᵒᵈ) :
  (s.of_dual : set α) = order_dual.to_dual ⁻¹' s := rfl

@[simp] protected lemma to_dual_bot : (⊥ : lower_set α).to_dual = ⊥ := rfl
@[simp] protected lemma to_dual_top : (⊤ : lower_set α).to_dual = ⊤ := rfl
@[simp] protected lemma of_dual_bot : (⊥ : lower_set αᵒᵈ).to_dual = ⊥ := rfl
@[simp] protected lemma of_dual_top : (⊤ : lower_set αᵒᵈ).to_dual = ⊤ := rfl

@[simp] protected lemma to_dual_inf (s t : lower_set α) :
  (s ⊓ t).to_dual = s.to_dual ⊓ t.to_dual := rfl
@[simp] protected lemma to_dual_sup (s t : lower_set α) :
  (s ⊓ t).to_dual = s.to_dual ⊓ t.to_dual := rfl
@[simp] protected lemma of_dual_inf (s t : lower_set αᵒᵈ) :
  (s ⊓ t).of_dual = s.of_dual ⊓ t.of_dual := rfl
@[simp] protected lemma of_dual_sup (s t : lower_set αᵒᵈ) :
  (s ⊔ t).of_dual = s.of_dual ⊔ t.of_dual := rfl

@[simp] protected lemma to_dual_Inf (S : set (lower_set α)) :
  (Inf S).to_dual = Inf (lower_set.to_dual '' S) := set_like.coe_injective (by simpa)
@[simp] protected lemma to_dual_Sup (S : set (lower_set α)) :
  (Sup S).to_dual = Sup (lower_set.to_dual '' S) := set_like.coe_injective (by simp)
@[simp] protected lemma of_dual_Inf (S : set (lower_set αᵒᵈ)) :
  (Inf S).of_dual = Inf (lower_set.of_dual '' S) := set_like.coe_injective (by simpa)
@[simp] protected lemma of_dual_Sup (S : set (lower_set αᵒᵈ)) :
  (Sup S).of_dual = Sup (lower_set.of_dual '' S) := set_like.coe_injective (by simp)

@[simp] protected lemma to_dual_supr (f : ι → lower_set α) :
  (⨆ i, f i).to_dual = ⨆ i, (f i).to_dual := set_like.coe_injective (by simp)
@[simp] protected lemma to_dual_infi (f : ι → lower_set α) :
  (⨅ i, f i).to_dual = ⨅ i, (f i).to_dual := set_like.coe_injective (by simpa)
@[simp] protected lemma of_dual_supr (f : ι → lower_set αᵒᵈ) :
  (⨆ i, f i).of_dual = ⨆ i, (f i).of_dual := set_like.coe_injective (by simp)
@[simp] protected lemma of_dual_infi (f : ι → lower_set αᵒᵈ) :
  (⨅ i, f i).of_dual = ⨅ i, (f i).of_dual := set_like.coe_injective (by simpa)

@[simp] protected lemma to_dual_infi₂ (f : Π i, κ i → lower_set α) :
  (⨅ i j, f i j).to_dual = (⨅ i j, (f i j).to_dual) := set_like.coe_injective (by simp)
@[simp] protected lemma to_dual_supr₂ (f : Π i, κ i → lower_set α) :
  (⨆ i j, f i j).to_dual = (⨆ i j, (f i j).to_dual) := set_like.coe_injective (by simp)
@[simp] protected lemma of_dual_infi₂ (f : Π i, κ i → lower_set αᵒᵈ) :
  (⨅ i j, f i j).of_dual = (⨅ i j, (f i j).of_dual) := set_like.coe_injective (by simp)
@[simp] protected lemma of_dual_supr₂ (f : Π i, κ i → lower_set αᵒᵈ) :
  (⨆ i j, f i j).of_dual = (⨆ i j, (f i j).of_dual) := set_like.coe_injective (by simp)

end lower_set

@[simp] lemma upper_set.of_dual_to_dual (s : upper_set αᵒᵈ) : s.of_dual.to_dual = s := by {ext,simp}
@[simp] lemma upper_set.to_dual_of_dual (s : upper_set α) : s.to_dual.of_dual = s := by {ext,simp}
@[simp] lemma lower_set.of_dual_to_dual (s : lower_set αᵒᵈ) : s.of_dual.to_dual = s := by {ext,simp}
@[simp] lemma lower_set.to_dual_of_dual (s : lower_set α) : s.to_dual.of_dual = s := by {ext,simp}

end has_le

section map

section has_le

variables [has_le α] [has_le β] [order_iso_class F α β]

/-- The image of an `upper_set` under an `order_iso`-like function, as an `upper_set`. -/
def upper_set.map (s : upper_set α) (φ : F) : upper_set β := ⟨φ '' s, s.upper.map φ⟩

/-- The image of a `lower_set` under an `order_iso`-like function, as a `lower_set`. -/
def lower_set.map (s : lower_set α) (φ : F) : lower_set β := ⟨φ '' s, s.lower.map φ⟩

@[simp] lemma upper_set.coe_map (s : upper_set α) (φ : F) : (s.map φ : set β) = φ '' s := rfl
@[simp] lemma lower_set.coe_map (s : lower_set α) (φ : F) : (s.map φ : set β) = φ '' s := rfl

end has_le

section preorder

variables [preorder α] [preorder β] [order_hom_class F α β]

/-- The preimage of an `upper_set` under an `order_hom`-like function, as an `upper_set` -/
def upper_set.comap (t : upper_set β) (φ : F) : upper_set α := ⟨φ ⁻¹' t, t.upper.comap φ⟩

/-- The preimage of an `lower_set` under an `order_hom`-like function, as a `lower_set` -/
def lower_set.comap (t : lower_set β) (φ : F) : lower_set α := ⟨φ ⁻¹' t, t.lower.comap φ⟩

@[simp] lemma upper_set.coe_comap [order_hom_class F α β] (t : upper_set β) (φ : F) :
  ((t.comap φ : upper_set α) : set α) = φ ⁻¹' t := rfl

@[simp] lemma lower_set.coe_comap (t : lower_set β) (φ : F) :
  ((t.comap φ : lower_set α) : set α) = φ ⁻¹' t := rfl

end preorder

section boolean_algebra

variables [boolean_algebra α]

namespace upper_set

/-- The preimage of an `upper_set` under complementation, as a `lower_set`-/
protected def map_compl (s : upper_set α) : lower_set α :=
⟨has_compl.compl ⁻¹' (s : set α), λ x y h hx, s.upper (compl_le_compl h) hx⟩

@[simp] lemma coe_map_compl (s : upper_set α) : (s.map_compl : set α) = has_compl.compl ⁻¹' s := rfl

@[simp] lemma map_compl_bot : (⊥ : upper_set α).map_compl = ⊥ := rfl
@[simp] lemma map_compl_top : (⊤ : upper_set α).map_compl = ⊤ := rfl

@[simp] lemma map_compl_inf (s t : upper_set α) :
  (s ⊓ t).map_compl = s.map_compl ⊓ t.map_compl := rfl
@[simp] lemma map_compl_sup (s t : upper_set α) :
  (s ⊓ t).map_compl = s.map_compl ⊓ t.map_compl := rfl

@[simp] lemma map_compl_Inf (S : set (upper_set α)) :
  (Inf S).map_compl = Inf (map_compl '' S) :=
set_like.coe_injective (by simp [preimage_Inter])

@[simp] lemma map_compl_Sup (S : set (upper_set α)) :
  (Sup S).map_compl = Sup (map_compl '' S) :=
set_like.coe_injective (by simp)

@[simp] lemma map_compl_supr (f : ι → upper_set α) : (⨆ i, f i).map_compl = ⨆ i, (f i).map_compl :=
set_like.coe_injective (by simp)
@[simp] lemma map_compl_infi (f : ι → upper_set α) : (⨅ i, f i).map_compl = ⨅ i, (f i).map_compl :=
set_like.coe_injective (by simp [preimage_Inter])

@[simp] lemma map_compl_infi₂ (f : Π i, κ i → upper_set α) :
  (⨅ i j, f i j).map_compl = (⨅ i j, (f i j).map_compl) :=
set_like.coe_injective (by simp)
@[simp] lemma map_compl_supr₂ (f : Π i, κ i → upper_set α) :
  (⨆ i j, f i j).map_compl = (⨆ i j, (f i j).map_compl) :=
set_like.coe_injective (by simp)


end upper_set

/-- The preimage of a `lower_set` under complementation, as an `upper_set`-/
def lower_set.map_compl (s : lower_set α) : upper_set α :=
⟨compl ⁻¹' s, λ x y h hx, s.lower (compl_le_compl h) hx⟩

namespace lower_set

@[simp] lemma coe_map_compl (s : lower_set α) : (s.map_compl : set α) = has_compl.compl ⁻¹' s := rfl

@[simp] lemma map_compl_inf (s t : lower_set α) :
  (s ⊓ t).map_compl = s.map_compl ⊓ t.map_compl := rfl
@[simp] lemma map_compl_sup (s t : lower_set α) :
  (s ⊓ t).map_compl = s.map_compl ⊓ t.map_compl := rfl

@[simp] lemma map_compl_Inf (S : set (lower_set α)) :
  (Inf S).map_compl = Inf (map_compl '' S) :=
set_like.coe_injective (by simp [preimage_Inter])

@[simp] lemma map_compl_Sup (S : set (lower_set α)) :
  (Sup S).map_compl = Sup (map_compl '' S) :=
set_like.coe_injective (by simp)

@[simp] lemma map_compl_supr (f : ι → lower_set α) : (⨆ i, f i).map_compl = ⨆ i, (f i).map_compl :=
set_like.coe_injective (by simp)
@[simp] lemma map_compl_infi (f : ι → lower_set α) : (⨅ i, f i).map_compl = ⨅ i, (f i).map_compl :=
set_like.coe_injective (by simp [preimage_Inter])

@[simp] lemma map_compl_infi₂ (f : Π i, κ i → lower_set α) :
  (⨅ i j, f i j).map_compl = (⨅ i j, (f i j).map_compl) :=
set_like.coe_injective (by simp)
@[simp] lemma map_compl_supr₂ (f : Π i, κ i → lower_set α) :
  (⨆ i j, f i j).map_compl = (⨆ i j, (f i j).map_compl) :=
set_like.coe_injective (by simp)

end lower_set

@[simp] lemma upper_set.map_compl_map_compl (s : upper_set α): s.map_compl.map_compl = s :=
set_like.coe_injective (by simp [preimage_compl_eq_image_compl, compl_compl_image])

@[simp] lemma lower_set.map_compl_map_compl (s : lower_set α): s.map_compl.map_compl = s :=
set_like.coe_injective (by simp [preimage_compl_eq_image_compl, compl_compl_image])

end boolean_algebra

end map

/-! #### Principal sets -/

namespace upper_set
section preorder
variables [preorder α] [preorder β] {a b : α}

/-- The smallest upper set containing a given element. -/
def Ici (a : α) : upper_set α := ⟨Ici a, is_upper_set_Ici a⟩

/-- The smallest upper set containing a given element. -/
def Ioi (a : α) : upper_set α := ⟨Ioi a, is_upper_set_Ioi a⟩

@[simp] lemma coe_Ici (a : α) : ↑(Ici a) = set.Ici a := rfl
@[simp] lemma coe_Ioi (a : α) : ↑(Ioi a) = set.Ioi a := rfl
@[simp] lemma mem_Ici_iff : b ∈ Ici a ↔ a ≤ b := iff.rfl
@[simp] lemma mem_Ioi_iff : b ∈ Ioi a ↔ a < b := iff.rfl

lemma Ioi_le_Ici (a : α) : Ioi a ≤ Ici a := Ioi_subset_Ici_self

@[simp] lemma Ici_top [order_bot α] : Ici (⊥ : α) = ⊤ := set_like.coe_injective Ici_bot
@[simp] lemma Ioi_bot [order_top α] : Ioi (⊤ : α) = ⊥ := set_like.coe_injective Ioi_top

@[simp] lemma map_Ici [order_iso_class F α β] (a : α) (φ : F) : (Ici a).map φ = Ici (φ a) :=
set_like.coe_injective (by {rw [coe_Ici, coe_map, coe_Ici], exact (φ : α ≃o β).image_Ici _})

@[simp] lemma map_Ioi [order_iso_class F α β] (a : α) (φ : F) : (Ioi a).map φ = Ioi (φ a) :=
set_like.coe_injective (by {rw [coe_Ioi, coe_map, coe_Ioi], exact (φ : α ≃o β).image_Ioi _})

@[simp] lemma comap_Ici [order_iso_class F α β] (b : β) (φ : F) :
  ((Ici b).comap φ : upper_set α) = Ici ((φ : α ≃o β).symm b) :=
set_like.coe_injective (by {rw [coe_comap, coe_Ici, coe_Ici, ←order_iso.image_Ici,
  ←order_iso.preimage_eq_image_symm], refl})

@[simp] lemma comap_Ioi [order_iso_class F α β] (b : β) (φ : F) :
  ((Ioi b).comap φ : upper_set α) = Ioi ((φ : α ≃o β).symm b) :=
set_like.coe_injective (by {rw [coe_comap, coe_Ioi, coe_Ioi, ←order_iso.image_Ioi,
  ←order_iso.preimage_eq_image_symm], refl})

end preorder

section semilattice_sup
variables [semilattice_sup α]

@[simp] lemma Ici_sup (a b : α) : Ici (a ⊔ b) = Ici a ⊓ Ici b := ext Ici_inter_Ici.symm

/-- `upper_set.Ici` as a `sup_hom`. -/
def Ici_sup_hom : sup_hom α (upper_set α)ᵒᵈ := ⟨Ici, Ici_sup⟩

@[simp] lemma Ici_sup_hom_apply (a : α) : Ici_sup_hom a = to_dual (Ici a) := rfl

end semilattice_sup

section complete_lattice
variables [complete_lattice α]

@[simp] lemma Ici_Sup (S : set α) : Ici (Sup S) = ⨅ a ∈ S, Ici a :=
set_like.ext $ λ c, by simp only [mem_Ici_iff, mem_infi_iff, Sup_le_iff]

@[simp] lemma Ici_supr (f : ι → α) : Ici (⨆ i, f i) = ⨅ i, Ici (f i) :=
set_like.ext $ λ c, by simp only [mem_Ici_iff, mem_infi_iff, supr_le_iff]

@[simp] lemma Ici_supr₂ (f : Π i, κ i → α) : Ici (⨆ i j, f i j) = ⨅ i j, Ici (f i j) :=
by simp_rw Ici_supr

/-- `upper_set.Ici` as a `Sup_hom`. -/
def Ici_Sup_hom : Sup_hom α (upper_set α)ᵒᵈ :=
⟨Ici, λ s, (Ici_Sup s).trans Inf_image.symm⟩

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

@[simp] lemma map_Iic [preorder α] [preorder β] [order_iso_class F α β] (a : α) (φ : F) :
  (Iic a).map φ = Iic (φ a) :=
set_like.coe_injective (by {rw [coe_Iic, coe_map, coe_Iic], exact (φ : α ≃o β).image_Iic _})

@[simp] lemma map_Iio [preorder α] [preorder β] [order_iso_class F α β] (a : α) (φ : F) :
  (Iio a).map φ = Iio (φ a) :=
set_like.coe_injective (by {rw [coe_Iio, coe_map, coe_Iio], exact (φ : α ≃o β).image_Iio _})

@[simp] lemma comap_Iic [preorder α] [preorder β] [order_iso_class F α β] (b : β) (φ : F) :
  ((Iic b).comap φ : lower_set α) = Iic ((φ : α ≃o β).symm b) :=
set_like.coe_injective (by {rw [coe_comap, coe_Iic, coe_Iic, ←order_iso.image_Iic,
  ←order_iso.preimage_eq_image_symm], refl})

@[simp] lemma comap_Iio [preorder α] [preorder β] [order_iso_class F α β] (b : β) (φ : F) :
  ((Iio b).comap φ : lower_set α) = Iio ((φ : α ≃o β).symm b) :=
set_like.coe_injective (by {rw [coe_comap, coe_Iio, coe_Iio, ←order_iso.image_Iio,
  ←order_iso.preimage_eq_image_symm], refl})

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
