/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
import data.set.lattice
import data.set_like.basic

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

## TODO

Lattice structure on antichains. Order equivalence between upper/lower sets and antichains.
-/

open order_dual set

variables {ι : Sort*} {κ : ι → Sort*} {α : Type*}

/-! ### Unbundled upper/lower sets -/

section unbundled
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
@[simp] lemma is_lower_set_preimage_to_dual_iff {s : set (order_dual α)} :
  is_lower_set (to_dual ⁻¹' s) ↔ is_upper_set s := iff.rfl
@[simp] lemma is_upper_set_preimage_to_dual_iff {s : set (order_dual α)} :
  is_upper_set (to_dual ⁻¹' s) ↔ is_lower_set s := iff.rfl

alias is_lower_set_preimage_of_dual_iff ↔ _ is_upper_set.of_dual
alias is_upper_set_preimage_of_dual_iff ↔ _ is_lower_set.of_dual
alias is_lower_set_preimage_to_dual_iff ↔ _ is_upper_set.to_dual
alias is_upper_set_preimage_to_dual_iff ↔ _ is_lower_set.to_dual

end unbundled

/-! ### Bundled upper/lower sets -/

section bundled
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

instance upper_set.set_like : set_like (upper_set α) α :=
{ coe := upper_set.carrier,
  coe_injective' := λ s t h, by { cases s, cases t, congr' } }

@[ext] lemma ext {s t : upper_set α} : (s : set α) = t → s = t := set_like.ext'

protected lemma upper (s : upper_set α) : is_upper_set (s : set α) := s.upper'

end upper_set

namespace lower_set

instance : set_like (lower_set α) α :=
{ coe := lower_set.carrier,
  coe_injective' := λ s t h, by { cases s, cases t, congr' } }

@[ext] lemma ext {s t : lower_set α} : (s : set α) = t → s = t := set_like.ext'

protected lemma lower (s : lower_set α) : is_lower_set (s : set α) := s.lower'

end lower_set

/-! #### Order -/

namespace upper_set

instance : has_sup (upper_set α) := ⟨λ s t, ⟨s ∪ t, s.upper.union t.upper⟩⟩
instance : has_inf (upper_set α) := ⟨λ s t, ⟨s ∩ t, s.upper.inter t.upper⟩⟩
instance : has_top (upper_set α) := ⟨⟨univ, is_upper_set_univ⟩⟩
instance : has_bot (upper_set α) := ⟨⟨∅, is_upper_set_empty⟩⟩
instance : has_Sup (upper_set α) :=
⟨λ S, ⟨Sup (coe '' S), is_upper_set_sUnion $ ball_image_iff.2 $ λ s _, s.upper⟩⟩
instance : has_Inf (upper_set α) :=
⟨λ S, ⟨Inf (coe '' S), is_upper_set_sInter $ ball_image_iff.2 $ λ s _, s.upper⟩⟩

instance : complete_distrib_lattice (upper_set α) :=
set_like.coe_injective.complete_distrib_lattice _
  (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _, rfl) rfl rfl

instance : inhabited (upper_set α) := ⟨⊥⟩

@[simp] lemma coe_top : ((⊤ : upper_set α) : set α) = univ := rfl
@[simp] lemma coe_bot : ((⊥ : upper_set α) : set α) = ∅ := rfl
@[simp] lemma coe_sup (s t : upper_set α) : (↑(s ⊔ t) : set α) = s ∪ t := rfl
@[simp] lemma coe_inf (s t : upper_set α) : (↑(s ⊓ t) : set α) = s ∩ t := rfl
@[simp] lemma coe_Sup (S : set (upper_set α)) : (↑(Sup S) : set α) = Sup (coe '' S) := rfl
@[simp] lemma coe_Inf (S : set (upper_set α)) : (↑(Inf S) : set α) = Inf (coe '' S) := rfl
@[simp] lemma coe_supr (f : ι → upper_set α) : (↑(⨆ i, f i) : set α) = ⨆ i, f i :=
congr_arg Sup (range_comp _ _).symm
@[simp] lemma coe_infi (f : ι → upper_set α) : (↑(⨅ i, f i) : set α) = ⨅ i, f i :=
congr_arg Inf (range_comp _ _).symm
@[simp] lemma coe_supr₂ (f : Π i, κ i → upper_set α) : (↑(⨆ i j, f i j) : set α) = ⨆ i j, f i j :=
by simp_rw coe_supr
@[simp] lemma coe_infi₂ (f : Π i, κ i → upper_set α) : (↑(⨅ i j, f i j) : set α) = ⨅ i j, f i j :=
by simp_rw coe_infi

end upper_set

namespace lower_set

instance : has_sup (lower_set α) := ⟨λ s t, ⟨s ∪ t, λ a b h, or.imp (s.lower h) (t.lower h)⟩⟩
instance : has_inf (lower_set α) := ⟨λ s t, ⟨s ∩ t, λ a b h, and.imp (s.lower h) (t.lower h)⟩⟩
instance : has_top (lower_set α) := ⟨⟨univ, λ a b h, id⟩⟩
instance : has_bot (lower_set α) := ⟨⟨∅, λ a b h, id⟩⟩
instance : has_Sup (lower_set α) :=
⟨λ S, ⟨Sup (coe '' S), is_lower_set_sUnion $ ball_image_iff.2 $ λ s _, s.lower⟩⟩
instance : has_Inf (lower_set α) :=
⟨λ S, ⟨Inf (coe '' S), is_lower_set_sInter $ ball_image_iff.2 $ λ s _, s.lower⟩⟩

instance : complete_distrib_lattice (lower_set α) :=
set_like.coe_injective.complete_distrib_lattice _
  (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _, rfl) rfl rfl

instance : inhabited (lower_set α) := ⟨⊥⟩

@[simp] lemma coe_top : ((⊤ : lower_set α) : set α) = univ := rfl
@[simp] lemma coe_bot : ((⊥ : lower_set α) : set α) = ∅ := rfl
@[simp] lemma coe_sup (s t : lower_set α) : (↑(s ⊔ t) : set α) = s ∪ t := rfl
@[simp] lemma coe_inf (s t : lower_set α) : (↑(s ⊓ t) : set α) = s ∩ t := rfl
@[simp] lemma coe_Sup (S : set (lower_set α)) : (↑(Sup S) : set α) = Sup (coe '' S) := rfl
@[simp] lemma coe_Inf (S : set (lower_set α)) : (↑(Inf S) : set α) = Inf (coe '' S) := rfl
@[simp] lemma coe_supr (f : ι → lower_set α) : (↑(⨆ i, f i) : set α) = ⨆ i, f i :=
congr_arg Sup (range_comp _ _).symm
@[simp] lemma coe_infi (f : ι → lower_set α) : (↑(⨅ i, f i) : set α) = ⨅ i, f i :=
congr_arg Inf (range_comp _ _).symm
@[simp] lemma coe_supr₂ (f : Π i, κ i → lower_set α) : (↑(⨆ i j, f i j) : set α) = ⨆ i j, f i j :=
by simp_rw coe_supr
@[simp] lemma coe_infi₂ (f : Π i, κ i → lower_set α) : (↑(⨅ i j, f i j) : set α) = ⨅ i j, f i j :=
by simp_rw coe_infi

end lower_set

/-! #### Complement -/

/-- The complement of a lower set as an upper set. -/
def upper_set.compl (s : upper_set α) : lower_set α := ⟨sᶜ, s.upper.compl⟩

/-- The complement of a lower set as an upper set. -/
def lower_set.compl (s : lower_set α) : upper_set α := ⟨sᶜ, s.lower.compl⟩

namespace upper_set

@[simp] lemma coe_compl (s : upper_set α) : (s.compl : set α) = sᶜ := rfl
@[simp] lemma compl_compl (s : upper_set α) : s.compl.compl = s := upper_set.ext $ compl_compl _

protected lemma compl_sup (s t : upper_set α) : (s ⊔ t).compl = s.compl ⊓ t.compl :=
lower_set.ext compl_sup
protected lemma compl_inf (s t : upper_set α) : (s ⊓ t).compl = s.compl ⊔ t.compl :=
lower_set.ext compl_inf
protected lemma compl_top : (⊤ : upper_set α).compl = ⊥ := lower_set.ext compl_univ
protected lemma compl_bot : (⊥ : upper_set α).compl = ⊤ := lower_set.ext compl_empty
protected lemma compl_Sup (S : set (upper_set α)) : (Sup S).compl = Inf (upper_set.compl '' S) :=
lower_set.ext $ compl_Sup'.trans $
  by { congr' 1, ext, simp only [mem_image, exists_exists_and_eq_and, coe_compl] }

protected lemma compl_Inf (S : set (upper_set α)) : (Inf S).compl = Sup (upper_set.compl '' S) :=
lower_set.ext $ compl_Inf'.trans $
  by { congr' 1, ext, simp only [mem_image, exists_exists_and_eq_and, coe_compl] }

protected lemma compl_supr (f : ι → upper_set α) : (⨆ i, f i).compl = ⨅ i, (f i).compl :=
lower_set.ext $
  by simp only [coe_compl, coe_supr, supr_eq_Union, compl_Union, lower_set.coe_infi, infi_eq_Inter]

protected lemma compl_infi (f : ι → upper_set α) : (⨅ i, f i).compl = ⨆ i, (f i).compl :=
lower_set.ext $
  by simp only [coe_compl, coe_infi, infi_eq_Inter, compl_Inter, lower_set.coe_supr, supr_eq_Union]

@[simp] lemma compl_supr₂ (f : Π i, κ i → upper_set α) :
  (⨆ i j, f i j).compl = ⨅ i j, (f i j).compl :=
by simp_rw upper_set.compl_supr

@[simp] lemma compl_infi₂ (f : Π i, κ i → upper_set α) :
  (⨅ i j, f i j).compl =  ⨆ i j, (f i j).compl :=
by simp_rw upper_set.compl_infi

end upper_set

namespace lower_set

@[simp] lemma coe_compl (s : lower_set α) : (s.compl : set α) = sᶜ := rfl
@[simp] lemma compl_compl (s : lower_set α) : s.compl.compl = s := lower_set.ext $ compl_compl _

protected lemma compl_sup (s t : lower_set α) : (s ⊔ t).compl = s.compl ⊓ t.compl :=
upper_set.ext compl_sup
protected lemma compl_inf (s t : lower_set α) : (s ⊓ t).compl = s.compl ⊔ t.compl :=
upper_set.ext compl_inf
protected lemma compl_top : (⊤ : lower_set α).compl = ⊥ := upper_set.ext compl_univ
protected lemma compl_bot : (⊥ : lower_set α).compl = ⊤ := upper_set.ext compl_empty
protected lemma compl_Sup (S : set (lower_set α)) : (Sup S).compl = Inf (lower_set.compl '' S) :=
upper_set.ext $ compl_Sup'.trans $
  by { congr' 1, ext, simp only [mem_image, exists_exists_and_eq_and, coe_compl] }

protected lemma compl_Inf (S : set (lower_set α)) : (Inf S).compl = Sup (lower_set.compl '' S) :=
upper_set.ext $ compl_Inf'.trans $
  by { congr' 1, ext, simp only [mem_image, exists_exists_and_eq_and, coe_compl] }

protected lemma compl_supr (f : ι → lower_set α) : (⨆ i, f i).compl = ⨅ i, (f i).compl :=
upper_set.ext $
  by simp only [coe_compl, coe_supr, supr_eq_Union, compl_Union, upper_set.coe_infi, infi_eq_Inter]

protected lemma compl_infi (f : ι → lower_set α) : (⨅ i, f i).compl = ⨆ i, (f i).compl :=
upper_set.ext $
  by simp only [coe_compl, coe_infi, infi_eq_Inter, compl_Inter, upper_set.coe_supr, supr_eq_Union]

@[simp] lemma compl_supr₂ (f : Π i, κ i → lower_set α) :
  (⨆ i j, f i j).compl = ⨅ i j, (f i j).compl :=
by simp_rw lower_set.compl_supr

@[simp] lemma compl_infi₂ (f : Π i, κ i → lower_set α) :
  (⨅ i j, f i j).compl =  ⨆ i j, (f i j).compl :=
by simp_rw lower_set.compl_infi

end lower_set
end bundled
