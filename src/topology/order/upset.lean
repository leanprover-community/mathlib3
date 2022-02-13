/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
import data.set_like.basic
import order.ideal

/-!
# Up-sets and down-sets
-/

open set

variables {ι : Sort*} {κ : ι → Sort*} {α : Type*}

lemma forall₂_imp {ι : Sort*} {κ : ι → Sort*} {p q : Π i, κ i → Prop} (h : ∀ i j, p i j → q i j) :
  (∀ i j, p i j) → ∀ i j, q i j :=
forall_imp $ λ i, forall_imp $ h i

lemma Exists₂.imp {ι : Sort*} {κ : ι → Sort*} {p q : Π i, κ i → Prop} (h : ∀ i j, p i j → q i j) :
  (∃ i j, p i j) → ∃ i j, q i j :=
Exists.imp $ λ i, Exists.imp $ h i

section
variables [complete_boolean_algebra α] {S : set α}

lemma compl_Inf' : (Inf S)ᶜ = Sup (compl '' S) := compl_Inf.trans Sup_image.symm
lemma compl_Sup' : (Sup S)ᶜ = Inf (compl '' S) := compl_Sup.trans Inf_image.symm

end

/-- Pullback a `complete_lattice` under an injective map. -/
@[reducible] -- See note [reducible non-instances]
def function.injective.complete_lattice {α β : Type*} [has_sup α] [has_inf α] [has_Sup α]
  [has_Inf α] [has_bot α] [has_top α] [complete_lattice β]
  (f : α → β) (hf_inj : function.injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
  (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
  (map_Sup : ∀ s, f (Sup s) = Sup (f '' s)) (map_Inf : ∀ s, f (Inf s) = Inf (f '' s)) :
  complete_lattice α :=
{ Sup := Sup,
  le_Sup := λ s a ha,
    by { change f a ≤ f (Sup s), rw map_Sup, exact le_Sup (mem_image_of_mem f ha) },
  Sup_le := λ s a h,
    by { change f (Sup s) ≤ f a, rw map_Sup, refine Sup_le _, rintro _ ⟨b, hb, rfl⟩, exact h _ hb },
  Inf := Inf,
  Inf_le := λ s a ha,
    by { change f (Inf s) ≤ f a, rw map_Inf, exact Inf_le (mem_image_of_mem f ha) },
  le_Inf := λ s a h,
    by { change f a ≤ f (Inf s), rw map_Inf, refine le_Inf _, rintro _ ⟨b, hb, rfl⟩, exact h _ hb },
  top := ⊤,
  bot := ⊥,
  le_top := λ a, by { change f a ≤ f ⊤, rw map_top, exact le_top },
  bot_le := λ a, by { change f ⊥ ≤ f a, rw map_bot, exact bot_le },
  ..hf_inj.lattice f map_sup map_inf }

/-- Pullback a `complete_distrib_lattice` under an injective map. -/
@[reducible] -- See note [reducible non-instances]
def function.injective.complete_distrib_lattice {α β : Type*} [has_sup α] [has_inf α] [has_Sup α]
  [has_Inf α] [has_bot α] [has_top α] [complete_distrib_lattice β]
  (f : α → β) (hf_inj : function.injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
  (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
  (map_Sup : ∀ s, f (Sup s) = Sup (f '' s)) (map_Inf : ∀ s, f (Inf s) = Inf (f '' s)) :
  complete_distrib_lattice α :=
{ Sup := Sup,
  Inf := Inf,
  infi_sup_le_sup_Inf := λ a s,
    by { change f (⨅ b ∈ s, a ⊔ b) ≤ f (a ⊔ Inf s), rw [infi, map_Inf, map_sup, map_Inf],
      convert sup_Inf_eq.ge,
      rw [←range_comp], },
  inf_Sup_le_supr_inf := _,
  le_top := λ a, by { change f a ≤ f ⊤, rw map_top, exact le_top },
  bot_le := λ a, by { change f ⊥ ≤ f a, rw map_bot, exact bot_le },
  ..hf_inj.complete_lattice f map_sup map_inf map_top map_bot map_Sup map_Inf }

/-- An upper set in an order `α` is a set such that any element greater than one of its members is
also a member. -/
structure up_set (α) [has_le α] :=
(carrier : set α)
(mem_of_ge' {a b : α} : a ≤ b → a ∈ carrier → b ∈ carrier)

/-- A lower set in an order `α` is a set such that any element less than one of its members is also
a member. -/
structure down_set (α) [has_le α] :=
(carrier : set α)
(mem_of_le' {a b : α} : a ≤ b → b ∈ carrier → a ∈ carrier)

section has_le
variables [has_le α]

namespace up_set

instance up_set.set_like : set_like (up_set α) α :=
{ coe := up_set.carrier,
  coe_injective' := λ s t h, by { cases s, cases t, congr' } }

@[ext] lemma ext {s t : up_set α} : (s : set α) = t → s = t := set_like.ext'

lemma mem_of_ge (s : up_set α) {a b : α} (h : a ≤ b) : a ∈ s → b ∈ s := s.mem_of_ge' h

end up_set

namespace down_set

instance : set_like (down_set α) α :=
{ coe := down_set.carrier,
  coe_injective' := λ s t h, by { cases s, cases t, congr' } }

@[ext] lemma ext {s t : down_set α} : (s : set α) = t → s = t := set_like.ext'

lemma mem_of_le (s : down_set α) {a b : α} (h : a ≤ b) : b ∈ s → a ∈ s := s.mem_of_le' h

end down_set

/-! ### Complement -/

/-- The complement of a lower set as an upper set. -/
def up_set.compl (s : up_set α) : down_set α := ⟨sᶜ, λ a b h hb ha, hb $ s.mem_of_ge h ha⟩

@[simp] lemma up_set.coe_compl (s : up_set α) : (s.compl : set α) = sᶜ := rfl

/-- The complement of a lower set as an upper set. -/
def down_set.compl (s : down_set α) : up_set α := ⟨sᶜ, λ a b h hb ha, hb $ s.mem_of_le h ha⟩

@[simp] lemma down_set.coe_compl (s : down_set α) : (s.compl : set α) = sᶜ := rfl

@[simp] lemma up_set.compl_compl (s : up_set α) : s.compl.compl = s := up_set.ext $ compl_compl _
@[simp] lemma down_set.compl_compl (s : down_set α) : s.compl.compl = s :=
down_set.ext $ compl_compl _

/-! ### Order structure -/

namespace up_set

instance : has_sup (up_set α) := ⟨λ s t, ⟨s ∪ t, λ a b h, or.imp (s.mem_of_ge h) (t.mem_of_ge h)⟩⟩
instance : has_inf (up_set α) := ⟨λ s t, ⟨s ∩ t, λ a b h, and.imp (s.mem_of_ge h) (t.mem_of_ge h)⟩⟩
instance : has_top (up_set α) := ⟨⟨univ, λ a b h, id⟩⟩
instance : has_bot (up_set α) := ⟨⟨∅, λ a b h, id⟩⟩
instance : has_Sup (up_set α) :=
⟨λ S, ⟨Sup (coe '' S), λ a b h, Exists₂.imp $ ball_image_iff.2 $ λ s _, s.mem_of_ge h⟩⟩
instance : has_Inf (up_set α) :=
⟨λ S, ⟨Inf (coe '' S), λ a b h, forall₂_imp $ ball_image_iff.2 $ λ s _, s.mem_of_ge h⟩⟩

instance : complete_distrib_lattice (up_set α) :=
set_like.coe_injective.complete_distrib_lattice _
  (λ _ _, rfl) (λ _ _, rfl) rfl rfl (λ _, rfl) (λ _, rfl)

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

instance : has_sup (down_set α) := ⟨λ s t, ⟨s ∪ t, λ a b h, or.imp (s.mem_of_le h) (t.mem_of_le h)⟩⟩
instance : has_inf (down_set α) := ⟨λ s t, ⟨s ∩ t, λ a b h, and.imp (s.mem_of_le h) (t.mem_of_le h)⟩⟩
instance : has_top (down_set α) := ⟨⟨univ, λ a b h, id⟩⟩
instance : has_bot (down_set α) := ⟨⟨∅, λ a b h, id⟩⟩
instance : has_Sup (down_set α) :=
⟨λ S, ⟨Sup (coe '' S), λ a b h, Exists₂.imp $ ball_image_iff.2 $ λ s _, s.mem_of_le h⟩⟩
instance : has_Inf (down_set α) :=
⟨λ S, ⟨Inf (coe '' S), λ a b h, forall₂_imp $ ball_image_iff.2 $ λ s _, s.mem_of_le h⟩⟩

instance : complete_distrib_lattice (down_set α) :=
set_like.coe_injective.complete_distrib_lattice _
  (λ _ _, rfl) (λ _ _, rfl) rfl rfl (λ _, rfl) (λ _, rfl)

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

namespace up_set

protected lemma compl_sup (s t : up_set α) : (s ⊔ t).compl = s.compl ⊓ t.compl :=
down_set.ext compl_sup
protected lemma compl_inf (s t : up_set α) : (s ⊓ t).compl = s.compl ⊔ t.compl :=
down_set.ext compl_inf
protected lemma compl_top : (⊤ : up_set α).compl = ⊥ := down_set.ext compl_univ
protected lemma compl_bot : (⊥ : up_set α).compl = ⊤ := down_set.ext compl_empty
protected lemma compl_Sup (S : set (up_set α)) : (Sup S).compl = ⨅ s ∈ S, (s : up_set α).compl :=
down_set.ext $ compl_Sup'.trans $ by simp only [Inf_eq_sInter, sInter_image, mem_image,
  Inter_exists, bInter_and', Inter_Inter_eq_right, down_set.coe_infi₂, coe_compl, infi_eq_Inter]

protected lemma compl_Inf (S : set (up_set α)) : (Sup S).compl = Inf (up_set.compl '' S) :=
down_set.ext $ compl_Sup'.trans $ by rw [down_set.coe_Inf]

protected lemma compl_supr (f : ι → up_set α) : (⨆ i, f i).compl = ⨅ i, (f i).compl :=
down_set.ext $ by rw [coe_compl, coe_supr]

end up_set
end has_le
