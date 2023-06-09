/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yaël Dillies
-/
import order.complete_lattice
import order.directed
import logic.equiv.set

/-!
# Frames, completely distributive lattices and Boolean algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define and provide API for frames, completely distributive lattices and completely
distributive Boolean algebras.

## Typeclasses

* `order.frame`: Frame: A complete lattice whose `⊓` distributes over `⨆`.
* `order.coframe`: Coframe: A complete lattice whose `⊔` distributes over `⨅`.
* `complete_distrib_lattice`: Completely distributive lattices: A complete lattice whose `⊓` and `⊔`
  distribute over `⨆` and `⨅` respectively.
* `complete_boolean_algebra`: Completely distributive Boolean algebra: A Boolean algebra whose `⊓`
  and `⊔` distribute over `⨆` and `⨅` respectively.

A set of opens gives rise to a topological space precisely if it forms a frame. Such a frame is also
completely distributive, but not all frames are. `filter` is a coframe but not a completely
distributive lattice.

## TODO

Add instances for `prod`

## References

* [Wikipedia, *Complete Heyting algebra*](https://en.wikipedia.org/wiki/Complete_Heyting_algebra)
* [Francis Borceux, *Handbook of Categorical Algebra III*][borceux-vol3]
-/

set_option old_structure_cmd true

open function set

universes u v w
variables {α : Type u} {β : Type v} {ι : Sort w} {κ : ι → Sort*}

/-- A frame, aka complete Heyting algebra, is a complete lattice whose `⊓` distributes over `⨆`. -/
class order.frame (α : Type*) extends complete_lattice α :=
(inf_Sup_le_supr_inf (a : α) (s : set α) : a ⊓ Sup s ≤ ⨆ b ∈ s, a ⊓ b)

/-- A coframe, aka complete Brouwer algebra or complete co-Heyting algebra, is a complete lattice
whose `⊔` distributes over `⨅`. -/
class order.coframe (α : Type*) extends complete_lattice α :=
(infi_sup_le_sup_Inf (a : α) (s : set α) : (⨅ b ∈ s, a ⊔ b) ≤ a ⊔ Inf s)

open order

/-- A completely distributive lattice is a complete lattice whose `⊔` and `⊓` respectively
distribute over `⨅` and `⨆`. -/
class complete_distrib_lattice (α : Type*) extends frame α :=
(infi_sup_le_sup_Inf : ∀ a s, (⨅ b ∈ s, a ⊔ b) ≤ a ⊔ Inf s)

@[priority 100] -- See note [lower instance priority]
instance complete_distrib_lattice.to_coframe [complete_distrib_lattice α] : coframe α :=
{ .. ‹complete_distrib_lattice α› }

section frame
variables [frame α] {s t : set α} {a b : α}

instance order_dual.coframe : coframe αᵒᵈ :=
{ infi_sup_le_sup_Inf := frame.inf_Sup_le_supr_inf, ..order_dual.complete_lattice α }

lemma inf_Sup_eq : a ⊓ Sup s = ⨆ b ∈ s, a ⊓ b :=
(frame.inf_Sup_le_supr_inf _ _).antisymm supr_inf_le_inf_Sup

lemma Sup_inf_eq : Sup s ⊓ b = ⨆ a ∈ s, a ⊓ b :=
by simpa only [inf_comm] using @inf_Sup_eq α _ s b

lemma supr_inf_eq (f : ι → α) (a : α) : (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a :=
by rw [supr, Sup_inf_eq, supr_range]

lemma inf_supr_eq (a : α) (f : ι → α) : a ⊓ (⨆ i, f i) = ⨆ i, a ⊓ f i :=
by simpa only [inf_comm] using supr_inf_eq f a

lemma bsupr_inf_eq {f : Π i, κ i → α} (a : α) : (⨆ i j, f i j) ⊓ a = ⨆ i j, f i j ⊓ a :=
by simp only [supr_inf_eq]

lemma inf_bsupr_eq {f : Π i, κ i → α} (a : α) : a ⊓ (⨆ i j, f i j) = ⨆ i j, a ⊓ f i j :=
by simp only [inf_supr_eq]

lemma supr_inf_supr {ι ι' : Type*} {f : ι → α} {g : ι' → α} :
  (⨆ i, f i) ⊓ (⨆ j, g j) = ⨆ i : ι × ι', f i.1 ⊓ g i.2 :=
by simp only [inf_supr_eq, supr_inf_eq, supr_prod]

lemma bsupr_inf_bsupr {ι ι' : Type*} {f : ι → α} {g : ι' → α} {s : set ι} {t : set ι'} :
  (⨆ i ∈ s, f i) ⊓ (⨆ j ∈ t, g j) = ⨆ p ∈ s ×ˢ t, f (p : ι × ι').1 ⊓ g p.2 :=
begin
  simp only [supr_subtype', supr_inf_supr],
  exact (equiv.surjective _).supr_congr (equiv.set.prod s t).symm (λ x, rfl)
end

lemma Sup_inf_Sup : Sup s ⊓ Sup t = ⨆ p ∈ s ×ˢ t, (p : α × α).1 ⊓ p.2 :=
by simp only [Sup_eq_supr, bsupr_inf_bsupr]

lemma supr_disjoint_iff {f : ι → α} : disjoint (⨆ i, f i) a ↔ ∀ i, disjoint (f i) a :=
by simp only [disjoint_iff, supr_inf_eq, supr_eq_bot]

lemma disjoint_supr_iff {f : ι → α} : disjoint a (⨆ i, f i) ↔ ∀ i, disjoint a (f i) :=
by simpa only [disjoint.comm] using supr_disjoint_iff

lemma supr₂_disjoint_iff {f : Π i, κ i → α} :
  disjoint (⨆ i j, f i j) a ↔ ∀ i j, disjoint (f i j) a :=
by simp_rw supr_disjoint_iff

lemma disjoint_supr₂_iff {f : Π i, κ i → α} :
  disjoint a (⨆ i j, f i j) ↔ ∀ i j, disjoint a (f i j) :=
by simp_rw disjoint_supr_iff

lemma Sup_disjoint_iff {s : set α} : disjoint (Sup s) a ↔ ∀ b ∈ s, disjoint b a :=
by simp only [disjoint_iff, Sup_inf_eq, supr_eq_bot]

lemma disjoint_Sup_iff {s : set α} : disjoint a (Sup s) ↔ ∀ b ∈ s, disjoint a b :=
by simpa only [disjoint.comm] using Sup_disjoint_iff

lemma supr_inf_of_monotone {ι : Type*} [preorder ι] [is_directed ι (≤)] {f g : ι → α}
  (hf : monotone f) (hg : monotone g) :
  (⨆ i, f i ⊓ g i) = (⨆ i, f i) ⊓ (⨆ i, g i) :=
begin
  refine (le_supr_inf_supr f g).antisymm _,
  rw [supr_inf_supr],
  refine supr_mono' (λ i, _),
  rcases directed_of (≤) i.1 i.2 with ⟨j, h₁, h₂⟩,
  exact ⟨j, inf_le_inf (hf h₁) (hg h₂)⟩
end

lemma supr_inf_of_antitone {ι : Type*} [preorder ι] [is_directed ι (swap (≤))] {f g : ι → α}
  (hf : antitone f) (hg : antitone g) :
  (⨆ i, f i ⊓ g i) = (⨆ i, f i) ⊓ (⨆ i, g i) :=
@supr_inf_of_monotone α _ ιᵒᵈ _ _ f g hf.dual_left hg.dual_left

instance pi.frame {ι : Type*} {π : ι → Type*} [Π i, frame (π i)] : frame (Π i, π i) :=
{ inf_Sup_le_supr_inf := λ a s i,
    by simp only [complete_lattice.Sup, Sup_apply, supr_apply, pi.inf_apply, inf_supr_eq,
      ← supr_subtype''],
  ..pi.complete_lattice }

@[priority 100] -- see Note [lower instance priority]
instance frame.to_distrib_lattice : distrib_lattice α :=
distrib_lattice.of_inf_sup_le $ λ a b c,
  by rw [←Sup_pair, ←Sup_pair, inf_Sup_eq, ←Sup_image, image_pair]

end frame

section coframe
variables [coframe α] {s t : set α} {a b : α}

instance order_dual.frame : frame αᵒᵈ :=
{ inf_Sup_le_supr_inf := coframe.infi_sup_le_sup_Inf, ..order_dual.complete_lattice α }

lemma sup_Inf_eq : a ⊔ Inf s = ⨅ b ∈ s, a ⊔ b := @inf_Sup_eq αᵒᵈ _ _ _
lemma Inf_sup_eq : Inf s ⊔ b = ⨅ a ∈ s, a ⊔ b := @Sup_inf_eq αᵒᵈ _ _ _

lemma infi_sup_eq (f : ι → α) (a : α) : (⨅ i, f i) ⊔ a = ⨅ i, f i ⊔ a := @supr_inf_eq αᵒᵈ _ _ _ _
lemma sup_infi_eq (a : α) (f : ι → α) : a ⊔ (⨅ i, f i) = ⨅ i, a ⊔ f i := @inf_supr_eq αᵒᵈ _ _ _ _

lemma binfi_sup_eq {f : Π i, κ i → α} (a : α) : (⨅ i j, f i j) ⊔ a = ⨅ i j, f i j ⊔ a :=
@bsupr_inf_eq αᵒᵈ _ _ _ _ _

lemma sup_binfi_eq {f : Π i, κ i → α} (a : α) : a ⊔ (⨅ i j, f i j) = ⨅ i j, a ⊔ f i j :=
@inf_bsupr_eq αᵒᵈ _ _ _ _ _

lemma infi_sup_infi {ι ι' : Type*} {f : ι → α} {g : ι' → α} :
  (⨅ i, f i) ⊔ (⨅ i, g i) = ⨅ i : ι × ι', f i.1 ⊔ g i.2 :=
@supr_inf_supr αᵒᵈ _ _ _ _ _

lemma binfi_sup_binfi {ι ι' : Type*} {f : ι → α} {g : ι' → α} {s : set ι} {t : set ι'} :
  (⨅ i ∈ s, f i) ⊔ (⨅ j ∈ t, g j) = ⨅ p ∈ s ×ˢ t, f (p : ι × ι').1 ⊔ g p.2 :=
@bsupr_inf_bsupr αᵒᵈ _ _ _ _ _ _ _

theorem Inf_sup_Inf : Inf s ⊔ Inf t = (⨅ p ∈ s ×ˢ t, (p : α × α).1 ⊔ p.2) :=
@Sup_inf_Sup αᵒᵈ _ _ _

lemma infi_sup_of_monotone {ι : Type*} [preorder ι] [is_directed ι (swap (≤))] {f g : ι → α}
  (hf : monotone f) (hg : monotone g) :
  (⨅ i, f i ⊔ g i) = (⨅ i, f i) ⊔ (⨅ i, g i) :=
supr_inf_of_antitone hf.dual_right hg.dual_right

lemma infi_sup_of_antitone {ι : Type*} [preorder ι] [is_directed ι (≤)] {f g : ι → α}
  (hf : antitone f) (hg : antitone g) :
  (⨅ i, f i ⊔ g i) = (⨅ i, f i) ⊔ (⨅ i, g i) :=
supr_inf_of_monotone hf.dual_right hg.dual_right

instance pi.coframe {ι : Type*} {π : ι → Type*} [Π i, coframe (π i)] : coframe (Π i, π i) :=
{ Inf := Inf,
  infi_sup_le_sup_Inf := λ a s i,
    by simp only [←sup_infi_eq, Inf_apply, ←infi_subtype'', infi_apply, pi.sup_apply],
  ..pi.complete_lattice }

@[priority 100] -- see Note [lower instance priority]
instance coframe.to_distrib_lattice : distrib_lattice α :=
{ le_sup_inf := λ a b c, by rw [←Inf_pair, ←Inf_pair, sup_Inf_eq, ←Inf_image, image_pair],
  ..‹coframe α› }

end coframe

section complete_distrib_lattice
variables [complete_distrib_lattice α] {a b : α} {s t : set α}

instance : complete_distrib_lattice αᵒᵈ := { ..order_dual.frame, ..order_dual.coframe }

instance pi.complete_distrib_lattice {ι : Type*} {π : ι → Type*}
  [Π i, complete_distrib_lattice (π i)] : complete_distrib_lattice (Π i, π i) :=
{ ..pi.frame, ..pi.coframe }

end complete_distrib_lattice

/-- A complete Boolean algebra is a completely distributive Boolean algebra. -/
class complete_boolean_algebra α extends boolean_algebra α, complete_distrib_lattice α

instance pi.complete_boolean_algebra {ι : Type*} {π : ι → Type*}
  [∀ i, complete_boolean_algebra (π i)] : complete_boolean_algebra (Π i, π i) :=
{ .. pi.boolean_algebra, .. pi.complete_distrib_lattice }

instance Prop.complete_boolean_algebra : complete_boolean_algebra Prop :=
{ infi_sup_le_sup_Inf := λ p s, iff.mp $
    by simp only [forall_or_distrib_left, complete_lattice.Inf, infi_Prop_eq, sup_Prop_eq],
  inf_Sup_le_supr_inf := λ p s, iff.mp $
    by simp only [complete_lattice.Sup, exists_and_distrib_left, inf_Prop_eq, supr_Prop_eq],
  .. Prop.boolean_algebra, .. Prop.complete_lattice }

section complete_boolean_algebra
variables [complete_boolean_algebra α] {a b : α} {s : set α} {f : ι → α}

theorem compl_infi : (infi f)ᶜ = (⨆ i, (f i)ᶜ) :=
le_antisymm
  (compl_le_of_compl_le $ le_infi $ λ i, compl_le_of_compl_le $ le_supr (compl ∘ f) i)
  (supr_le $ λ i, compl_le_compl $ infi_le _ _)

theorem compl_supr : (supr f)ᶜ = (⨅ i, (f i)ᶜ) :=
compl_injective (by simp [compl_infi])

lemma compl_Inf : (Inf s)ᶜ = (⨆ i ∈ s, iᶜ) := by simp only [Inf_eq_infi, compl_infi]
lemma compl_Sup : (Sup s)ᶜ = (⨅ i ∈ s, iᶜ) := by simp only [Sup_eq_supr, compl_supr]
lemma compl_Inf' : (Inf s)ᶜ = Sup (compl '' s) := compl_Inf.trans Sup_image.symm
lemma compl_Sup' : (Sup s)ᶜ = Inf (compl '' s) := compl_Sup.trans Inf_image.symm

end complete_boolean_algebra

section lift

/-- Pullback an `order.frame` along an injection. -/
@[reducible] -- See note [reducible non-instances]
protected def function.injective.frame [has_sup α] [has_inf α] [has_Sup α] [has_Inf α] [has_top α]
  [has_bot α] [frame β] (f : α → β) (hf : injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
  (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_Sup : ∀ s, f (Sup s) = ⨆ a ∈ s, f a)
  (map_Inf : ∀ s, f (Inf s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) :
  frame α :=
{ inf_Sup_le_supr_inf := λ a s, begin
    change f (a ⊓ Sup s) ≤ f _,
    rw [←Sup_image, map_inf, map_Sup s, inf_bsupr_eq],
    simp_rw ←map_inf,
    exact ((map_Sup _).trans supr_image).ge,
  end,
  ..hf.complete_lattice f map_sup map_inf map_Sup map_Inf map_top map_bot }

/-- Pullback an `order.coframe` along an injection. -/
@[reducible] -- See note [reducible non-instances]
protected def function.injective.coframe [has_sup α] [has_inf α] [has_Sup α] [has_Inf α] [has_top α]
  [has_bot α] [coframe β] (f : α → β) (hf : injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
  (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_Sup : ∀ s, f (Sup s) = ⨆ a ∈ s, f a)
  (map_Inf : ∀ s, f (Inf s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) :
  coframe α :=
{ infi_sup_le_sup_Inf := λ a s, begin
    change f _ ≤ f (a ⊔ Inf s),
    rw [←Inf_image, map_sup, map_Inf s, sup_binfi_eq],
    simp_rw ←map_sup,
    exact ((map_Inf _).trans infi_image).le,
  end,
  ..hf.complete_lattice f map_sup map_inf map_Sup map_Inf map_top map_bot }

/-- Pullback a `complete_distrib_lattice` along an injection. -/
@[reducible] -- See note [reducible non-instances]
protected def function.injective.complete_distrib_lattice [has_sup α] [has_inf α] [has_Sup α]
  [has_Inf α] [has_top α] [has_bot α] [complete_distrib_lattice β]
  (f : α → β) (hf : function.injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
  (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_Sup : ∀ s, f (Sup s) = ⨆ a ∈ s, f a)
  (map_Inf : ∀ s, f (Inf s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) :
  complete_distrib_lattice α :=
{ ..hf.frame f map_sup map_inf map_Sup map_Inf map_top map_bot,
  ..hf.coframe f map_sup map_inf map_Sup map_Inf map_top map_bot }

/-- Pullback a `complete_boolean_algebra` along an injection. -/
@[reducible] -- See note [reducible non-instances]
protected def function.injective.complete_boolean_algebra [has_sup α] [has_inf α] [has_Sup α]
  [has_Inf α] [has_top α] [has_bot α] [has_compl α] [has_sdiff α] [complete_boolean_algebra β]
  (f : α → β) (hf : function.injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
  (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_Sup : ∀ s, f (Sup s) = ⨆ a ∈ s, f a)
  (map_Inf : ∀ s, f (Inf s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
  (map_compl : ∀ a, f aᶜ = (f a)ᶜ) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
  complete_boolean_algebra α :=
{ ..hf.complete_distrib_lattice f map_sup map_inf map_Sup map_Inf map_top map_bot,
  ..hf.boolean_algebra f map_sup map_inf map_top map_bot map_compl map_sdiff }

end lift

namespace punit
variables (s : set punit.{u+1}) (x y : punit.{u+1})

instance : complete_boolean_algebra punit :=
by refine_struct
{ Sup := λ _, star,
  Inf := λ _, star,
  ..punit.boolean_algebra };
    intros; trivial <|> simp only [eq_iff_true_of_subsingleton, not_true, and_false]

@[simp] lemma Sup_eq : Sup s = star := rfl
@[simp] lemma Inf_eq : Inf s = star := rfl

end punit
