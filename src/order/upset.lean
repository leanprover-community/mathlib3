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

* `is_upset`: Predicate for a set to be an upper set.
* `is_downset`: Predicate for a set to be a lower set.
* `up_set`: The type of upper sets.
* `down_set`: The type of lower sets.
-/

open set

variables {ι : Sort*} {κ : ι → Sort*} {α : Type*}

/-! ### Unbundled upper/lower sets -/

section unbundled
variables [has_le α] {s t : set α}

/-- An upper set in an order `α` is a set such that any element greater than one of its members is
also a member. -/
def is_upset (s : set α) : Prop := ∀ ⦃a b⦄, a ≤ b → a ∈ s → b ∈ s

/-- A lower set in an order `α` is a set such that any element less than one of its members is also
a member. -/
def is_downset (s : set α) : Prop := ∀ ⦃a b⦄, b ≤ a → a ∈ s → b ∈ s

lemma is_upset_empty : is_upset (∅ : set α) := λ _ _ _, id
lemma is_downset_empty : is_downset (∅ : set α) := λ _ _ _, id
lemma is_upset_univ : is_upset (univ : set α) := λ _ _ _, id
lemma is_downset_univ : is_downset (univ : set α) := λ _ _ _, id
lemma is_upset.compl (hs : is_upset s) : is_downset sᶜ := λ a b h hb ha, hb $ hs h ha
lemma is_downset.compl (hs : is_downset s) : is_upset sᶜ := λ a b h hb ha, hb $ hs h ha

lemma is_upset.union (hs : is_upset s) (ht : is_upset t) : is_upset (s ∪ t) :=
λ a b h, or.imp (hs h) (ht h)

lemma is_downset.union (hs : is_downset s) (ht : is_downset t) : is_downset (s ∪ t) :=
λ a b h, or.imp (hs h) (ht h)

lemma is_upset.inter (hs : is_upset s) (ht : is_upset t) : is_upset (s ∩ t) :=
λ a b h, and.imp (hs h) (ht h)

lemma is_downset.inter (hs : is_downset s) (ht : is_downset t) : is_downset (s ∩ t) :=
λ a b h, and.imp (hs h) (ht h)

lemma is_upset_Union {f : ι → set α} (hf : ∀ i, is_upset (f i)) : is_upset (⋃ i, f i) :=
λ a b h, Exists₂.imp $ forall_range_iff.2 $ λ i, hf i h

lemma is_downset_Union {f : ι → set α} (hf : ∀ i, is_downset (f i)) : is_downset (⋃ i, f i) :=
λ a b h, Exists₂.imp $ forall_range_iff.2 $ λ i, hf i h

lemma is_upset_Union₂ {f : Π i, κ i → set α} (hf : ∀ i j, is_upset (f i j)) :
  is_upset (⋃ i j, f i j) :=
is_upset_Union $ λ i, is_upset_Union $ hf i

lemma is_downset_Union₂ {f : Π i, κ i → set α} (hf : ∀ i j, is_downset (f i j)) :
  is_downset (⋃ i j, f i j) :=
is_downset_Union $ λ i, is_downset_Union $ hf i

lemma is_upset_sUnion {S : set (set α)} (hf : ∀ s ∈ S, is_upset s) : is_upset (⋃₀ S) :=
λ a b h, Exists₂.imp $ λ s hs, hf s hs h

lemma is_downset_sUnion {S : set (set α)} (hf : ∀ s ∈ S, is_downset s) : is_downset (⋃₀ S) :=
λ a b h, Exists₂.imp $ λ s hs, hf s hs h

lemma is_upset_Inter {f : ι → set α} (hf : ∀ i, is_upset (f i)) : is_upset (⋂ i, f i) :=
λ a b h, forall₂_imp $ forall_range_iff.2 $ λ i, hf i h

lemma is_downset_Inter {f : ι → set α} (hf : ∀ i, is_downset (f i)) : is_downset (⋂ i, f i) :=
λ a b h, forall₂_imp $ forall_range_iff.2 $ λ i, hf i h

lemma is_upset_Inter₂ {f : Π i, κ i → set α} (hf : ∀ i j, is_upset (f i j)) :
  is_upset (⋂ i j, f i j) :=
is_upset_Inter $ λ i, is_upset_Inter $ hf i

lemma is_downset_Inter₂ {f : Π i, κ i → set α} (hf : ∀ i j, is_downset (f i j)) :
  is_downset (⋂ i j, f i j) :=
is_downset_Inter $ λ i, is_downset_Inter $ hf i

lemma is_upset_sInter {S : set (set α)} (hf : ∀ s ∈ S, is_upset s) : is_upset (⋂₀ S) :=
λ a b h, forall₂_imp $ λ s hs, hf s hs h

lemma is_downset_sInter {S : set (set α)} (hf : ∀ s ∈ S, is_downset s) : is_downset (⋂₀ S) :=
λ a b h, forall₂_imp $ λ s hs, hf s hs h

end unbundled

/-! ### Bundled upper/lower sets -/

section bundled
variables [has_le α]

/-- The type of upper sets of an order. -/
structure up_set (α : Type*) [has_le α] :=
(carrier : set α)
(upset' : is_upset carrier)

/-- The type of lower sets of an order. -/
structure down_set (α : Type*) [has_le α] :=
(carrier : set α)
(downset' : is_downset carrier)

namespace up_set

instance up_set.set_like : set_like (up_set α) α :=
{ coe := up_set.carrier,
  coe_injective' := λ s t h, by { cases s, cases t, congr' } }

@[ext] lemma ext {s t : up_set α} : (s : set α) = t → s = t := set_like.ext'

lemma upset (s : up_set α) : is_upset (s : set α) := s.upset'

end up_set

namespace down_set

instance : set_like (down_set α) α :=
{ coe := down_set.carrier,
  coe_injective' := λ s t h, by { cases s, cases t, congr' } }

@[ext] lemma ext {s t : down_set α} : (s : set α) = t → s = t := set_like.ext'

lemma downset (s : down_set α) : is_downset (s : set α) := s.downset'

end down_set

/-! #### Order -/

namespace up_set

instance : has_sup (up_set α) := ⟨λ s t, ⟨s ∪ t, s.upset.union t.upset⟩⟩
instance : has_inf (up_set α) := ⟨λ s t, ⟨s ∩ t, s.upset.inter t.upset⟩⟩
instance : has_top (up_set α) := ⟨⟨univ, is_upset_univ⟩⟩
instance : has_bot (up_set α) := ⟨⟨∅, is_upset_empty⟩⟩
instance : has_Sup (up_set α) :=
⟨λ S, ⟨Sup (coe '' S), is_upset_sUnion $ ball_image_iff.2 $ λ s _, s.upset⟩⟩
instance : has_Inf (up_set α) :=
⟨λ S, ⟨Inf (coe '' S), is_upset_sInter $ ball_image_iff.2 $ λ s _, s.upset⟩⟩

instance : complete_distrib_lattice (up_set α) :=
set_like.coe_injective.complete_distrib_lattice _
  (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _, rfl) rfl rfl

instance : inhabited (up_set α) := ⟨⊥⟩

@[simp] lemma coe_top : ((⊤ : up_set α) : set α) = univ := rfl
@[simp] lemma coe_bot : ((⊥ : up_set α) : set α) = ∅ := rfl
@[simp] lemma coe_sup (s t : up_set α) : (↑(s ⊔ t) : set α) = s ∪ t := rfl
@[simp] lemma coe_inf (s t : up_set α) : (↑(s ⊓ t) : set α) = s ∩ t := rfl
@[simp] lemma coe_Sup (S : set (up_set α)) : (↑(Sup S) : set α) = Sup (coe '' S) := rfl
@[simp] lemma coe_Inf (S : set (up_set α)) : (↑(Inf S) : set α) = Inf (coe '' S) := rfl
@[simp] lemma coe_supr (f : ι → up_set α) : (↑(⨆ i, f i) : set α) = ⨆ i, f i :=
congr_arg Sup (range_comp _ _).symm
@[simp] lemma coe_infi (f : ι → up_set α) : (↑(⨅ i, f i) : set α) = ⨅ i, f i :=
congr_arg Inf (range_comp _ _).symm
@[simp] lemma coe_supr₂ (f : Π i, κ i → up_set α) : (↑(⨆ i j, f i j) : set α) = ⨆ i j, f i j :=
by simp_rw coe_supr
@[simp] lemma coe_infi₂ (f : Π i, κ i → up_set α) : (↑(⨅ i j, f i j) : set α) = ⨅ i j, f i j :=
by simp_rw coe_infi

end up_set

namespace down_set

instance : has_sup (down_set α) := ⟨λ s t, ⟨s ∪ t, λ a b h, or.imp (s.downset h) (t.downset h)⟩⟩
instance : has_inf (down_set α) := ⟨λ s t, ⟨s ∩ t, λ a b h, and.imp (s.downset h) (t.downset h)⟩⟩
instance : has_top (down_set α) := ⟨⟨univ, λ a b h, id⟩⟩
instance : has_bot (down_set α) := ⟨⟨∅, λ a b h, id⟩⟩
instance : has_Sup (down_set α) :=
⟨λ S, ⟨Sup (coe '' S), is_downset_sUnion $ ball_image_iff.2 $ λ s _, s.downset⟩⟩
instance : has_Inf (down_set α) :=
⟨λ S, ⟨Inf (coe '' S), is_downset_sInter $ ball_image_iff.2 $ λ s _, s.downset⟩⟩

instance : complete_distrib_lattice (down_set α) :=
set_like.coe_injective.complete_distrib_lattice _
  (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _, rfl) rfl rfl

instance : inhabited (down_set α) := ⟨⊥⟩

@[simp] lemma coe_top : ((⊤ : down_set α) : set α) = univ := rfl
@[simp] lemma coe_bot : ((⊥ : down_set α) : set α) = ∅ := rfl
@[simp] lemma coe_sup (s t : down_set α) : (↑(s ⊔ t) : set α) = s ∪ t := rfl
@[simp] lemma coe_inf (s t : down_set α) : (↑(s ⊓ t) : set α) = s ∩ t := rfl
@[simp] lemma coe_Sup (S : set (down_set α)) : (↑(Sup S) : set α) = Sup (coe '' S) := rfl
@[simp] lemma coe_Inf (S : set (down_set α)) : (↑(Inf S) : set α) = Inf (coe '' S) := rfl
@[simp] lemma coe_supr (f : ι → down_set α) : (↑(⨆ i, f i) : set α) = ⨆ i, f i :=
congr_arg Sup (range_comp _ _).symm
@[simp] lemma coe_infi (f : ι → down_set α) : (↑(⨅ i, f i) : set α) = ⨅ i, f i :=
congr_arg Inf (range_comp _ _).symm
@[simp] lemma coe_supr₂ (f : Π i, κ i → down_set α) : (↑(⨆ i j, f i j) : set α) = ⨆ i j, f i j :=
by simp_rw coe_supr
@[simp] lemma coe_infi₂ (f : Π i, κ i → down_set α) : (↑(⨅ i j, f i j) : set α) = ⨅ i j, f i j :=
by simp_rw coe_infi

end down_set

/-! #### Complement -/

/-- The complement of a lower set as an upper set. -/
def up_set.compl (s : up_set α) : down_set α := ⟨sᶜ, s.upset.compl⟩

/-- The complement of a lower set as an upper set. -/
def down_set.compl (s : down_set α) : up_set α := ⟨sᶜ, s.downset.compl⟩

namespace up_set

@[simp] lemma coe_compl (s : up_set α) : (s.compl : set α) = sᶜ := rfl
@[simp] lemma compl_compl (s : up_set α) : s.compl.compl = s := up_set.ext $ compl_compl _

protected lemma compl_sup (s t : up_set α) : (s ⊔ t).compl = s.compl ⊓ t.compl :=
down_set.ext compl_sup
protected lemma compl_inf (s t : up_set α) : (s ⊓ t).compl = s.compl ⊔ t.compl :=
down_set.ext compl_inf
protected lemma compl_top : (⊤ : up_set α).compl = ⊥ := down_set.ext compl_univ
protected lemma compl_bot : (⊥ : up_set α).compl = ⊤ := down_set.ext compl_empty
protected lemma compl_Sup (S : set (up_set α)) : (Sup S).compl = Inf (up_set.compl '' S) :=
down_set.ext $ compl_Sup'.trans $
  by { congr' 1, ext, simp only [mem_image, exists_exists_and_eq_and, coe_compl] }

protected lemma compl_Inf (S : set (up_set α)) : (Inf S).compl = Sup (up_set.compl '' S) :=
down_set.ext $ compl_Inf'.trans $
  by { congr' 1, ext, simp only [mem_image, exists_exists_and_eq_and, coe_compl] }

protected lemma compl_supr (f : ι → up_set α) : (⨆ i, f i).compl = ⨅ i, (f i).compl :=
down_set.ext $
  by simp only [coe_compl, coe_supr, supr_eq_Union, compl_Union, down_set.coe_infi, infi_eq_Inter]

protected lemma compl_infi (f : ι → up_set α) : (⨅ i, f i).compl = ⨆ i, (f i).compl :=
down_set.ext $
  by simp only [coe_compl, coe_infi, infi_eq_Inter, compl_Inter, down_set.coe_supr, supr_eq_Union]

@[simp] lemma compl_supr₂ (f : Π i, κ i → up_set α) :
  (⨆ i j, f i j).compl = ⨅ i j, (f i j).compl :=
by simp_rw up_set.compl_supr

@[simp] lemma compl_infi₂ (f : Π i, κ i → up_set α) :
  (⨅ i j, f i j).compl =  ⨆ i j, (f i j).compl :=
by simp_rw up_set.compl_infi

end up_set

namespace down_set

@[simp] lemma coe_compl (s : down_set α) : (s.compl : set α) = sᶜ := rfl
@[simp] lemma compl_compl (s : down_set α) : s.compl.compl = s := down_set.ext $ compl_compl _

protected lemma compl_sup (s t : down_set α) : (s ⊔ t).compl = s.compl ⊓ t.compl :=
up_set.ext compl_sup
protected lemma compl_inf (s t : down_set α) : (s ⊓ t).compl = s.compl ⊔ t.compl :=
up_set.ext compl_inf
protected lemma compl_top : (⊤ : down_set α).compl = ⊥ := up_set.ext compl_univ
protected lemma compl_bot : (⊥ : down_set α).compl = ⊤ := up_set.ext compl_empty
protected lemma compl_Sup (S : set (down_set α)) : (Sup S).compl = Inf (down_set.compl '' S) :=
up_set.ext $ compl_Sup'.trans $
  by { congr' 1, ext, simp only [mem_image, exists_exists_and_eq_and, coe_compl] }

protected lemma compl_Inf (S : set (down_set α)) : (Inf S).compl = Sup (down_set.compl '' S) :=
up_set.ext $ compl_Inf'.trans $
  by { congr' 1, ext, simp only [mem_image, exists_exists_and_eq_and, coe_compl] }

protected lemma compl_supr (f : ι → down_set α) : (⨆ i, f i).compl = ⨅ i, (f i).compl :=
up_set.ext $
  by simp only [coe_compl, coe_supr, supr_eq_Union, compl_Union, up_set.coe_infi, infi_eq_Inter]

protected lemma compl_infi (f : ι → down_set α) : (⨅ i, f i).compl = ⨆ i, (f i).compl :=
up_set.ext $
  by simp only [coe_compl, coe_infi, infi_eq_Inter, compl_Inter, up_set.coe_supr, supr_eq_Union]

@[simp] lemma compl_supr₂ (f : Π i, κ i → down_set α) :
  (⨆ i j, f i j).compl = ⨅ i j, (f i j).compl :=
by simp_rw down_set.compl_supr

@[simp] lemma compl_infi₂ (f : Π i, κ i → down_set α) :
  (⨅ i j, f i j).compl =  ⨆ i j, (f i j).compl :=
by simp_rw down_set.compl_infi

end down_set
end bundled
