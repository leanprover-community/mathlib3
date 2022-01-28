/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yaël Dillies
-/
import order.complete_lattice

/-!
# Frames, completely distributive lattices and Boolean algebras

In this file we define and provide API for frames, completely distributive lattices and completely
distributive Boolean algebras.

## Typeclasses

* `frame`: Frame: A complete lattice whose `⊓` distributes over `⨆`.
* `complete_distrib_lattice`: Completely distributive lattices: A complete lattice whose `⊓` and `⊔`
  distribute over `⨆` and `⨅` respectively.
* `complete_boolean_algebra`: Completely distributive Boolean algebra: A Boolean algebra whose `⊓`
  and `⊔` distribute over `⨆` and `⨅` respectively.

## References

* [Wikipedia, *Complete Heyting algebra*][https://en.wikipedia.org/wiki/Complete_Heyting_algebra]
-/

set_option old_structure_cmd true

universes u v w
variables {α : Type u} {β : Type v} {ι : Sort w} {κ : ι → Sort*}

/-- A frame, aka complete Heyting algebra, is a complete lattice whose `⊓` distributes over `⨆`. -/
class frame (α : Type*) extends complete_lattice α :=
(inf_Sup_le_supr_inf (a : α) (s : set α) : a ⊓ Sup s ≤ ⨆ b ∈ s, a ⊓ b)

section frame
variables [frame α] {s t : set α} {a b : α}

lemma inf_Sup_eq : a ⊓ Sup s = (⨆ b ∈ s, a ⊓ b) :=
(frame.inf_Sup_le_supr_inf _ _).antisymm supr_inf_le_inf_Sup

lemma Sup_inf_eq : Sup s ⊓ b = (⨆ a ∈ s, a ⊓ b) :=
by simpa only [inf_comm] using @inf_Sup_eq α _ s b

lemma supr_inf_eq (f : ι → α) (a : α) : (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a :=
by rw [supr, Sup_inf_eq, supr_range]

lemma inf_supr_eq (a : α) (f : ι → α) : a ⊓ (⨆ i, f i) = ⨆ i, a ⊓ f i :=
by simpa only [inf_comm] using supr_inf_eq f a

lemma bsupr_inf_eq {f : Π i, κ i → α} (a : α) : (⨆ i j, f i j) ⊓ a = ⨆ i j, f i j ⊓ a :=
by simp only [supr_inf_eq]

lemma inf_bsupr_eq {f : Π i, κ i → α} (a : α) : a ⊓ (⨆ i j, f i j) = ⨆ i j, a ⊓ f i j :=
by simp only [inf_supr_eq]

lemma Sup_inf_Sup : Sup s ⊓ Sup t = ⨆ p ∈ s ×ˢ t, (p : α × α).1 ⊓ p.2 :=
begin
  refine le_antisymm _ _,
  { simp_rw [Sup_inf_eq, supr_le_iff, inf_Sup_eq],
    rintro a ha,
    have : (⨆ p ∈ prod.mk a '' t, (p : α × α).1 ⊓ p.2) ≤ ⨆ p ∈ s ×ˢ t, ((p : α × α).1 : α) ⊓ p.2,
    { exact supr_le_supr_of_subset (set.image_prod_mk_subset_prod_right ha) },
    rwa supr_image at this },
  { simp_rw [supr_le_iff, set.mem_prod],
    exact λ a ha, inf_le_inf (le_Sup ha.1) (le_Sup ha.2) }
end

lemma supr_disjoint_iff {f : ι → α} : disjoint (⨆ i, f i) a ↔ ∀ i, disjoint (f i) a :=
by simp only [disjoint_iff, supr_inf_eq, supr_eq_bot]

lemma disjoint_supr_iff {f : ι → α} : disjoint a (⨆ i, f i) ↔ ∀ i, disjoint a (f i) :=
by simpa only [disjoint.comm] using @supr_disjoint_iff _ _ _ a f

instance pi.frame {ι : Type*} {π : ι → Type*} [Π i, frame (π i)] : frame (Π i, π i) :=
{ inf_Sup_le_supr_inf := λ a s i,
    by simp only [complete_lattice.Sup, Sup_apply, supr_apply, pi.inf_apply, inf_supr_eq,
      ← supr_subtype''],
  .. pi.complete_lattice }

end frame

/-- A complete distributive lattice is a bit stronger than the name might
  suggest; perhaps completely distributive lattice is more descriptive,
  as this class includes a requirement that the lattice join
  distribute over *arbitrary* infima, and similarly for the dual. -/
class complete_distrib_lattice α extends frame α :=
(infi_sup_le_sup_Inf : ∀ a s, (⨅ b ∈ s, a ⊔ b) ≤ a ⊔ Inf s)

section complete_distrib_lattice
variables [complete_distrib_lattice α] {a b : α} {s t : set α}

instance : complete_distrib_lattice (order_dual α) :=
{ infi_sup_le_sup_Inf := complete_distrib_lattice.inf_Sup_le_supr_inf,
  inf_Sup_le_supr_inf := complete_distrib_lattice.infi_sup_le_sup_Inf,
  .. order_dual.complete_lattice α }

theorem sup_Inf_eq : a ⊔ Inf s = (⨅ b ∈ s, a ⊔ b) :=
sup_Inf_le_infi_sup.antisymm (complete_distrib_lattice.infi_sup_le_sup_Inf _ _)

theorem Inf_sup_eq : Inf s ⊔ b = (⨅ a ∈ s, a ⊔ b) :=
by simpa only [sup_comm] using @sup_Inf_eq α _ b s

theorem infi_sup_eq (f : ι → α) (a : α) : (⨅ i, f i) ⊔ a = ⨅ i, f i ⊔ a :=
@supr_inf_eq (order_dual α) _ _ _ _

theorem sup_infi_eq (a : α) (f : ι → α) : a ⊔ (⨅ i, f i) = ⨅ i, a ⊔ f i :=
@inf_supr_eq (order_dual α) _ _ _ _

theorem binfi_sup_eq {p : α → Prop} {f : Π i (hi : p i), α} (a : α) :
  (⨅ i hi, f i hi) ⊔ a = ⨅ i hi, f i hi ⊔ a :=
@bsupr_inf_eq (order_dual α) _ _ _ _ _

theorem sup_binfi_eq (a : α) {p : α → Prop} {f : Π i (hi : p i), α} :
  a ⊔ (⨅ i hi, f i hi) = ⨅ i hi, a ⊔ f i hi :=
@inf_bsupr_eq (order_dual α) _ _ _ _ _

instance pi.complete_distrib_lattice {ι : Type*} {π : ι → Type*}
  [∀ i, complete_distrib_lattice (π i)] : complete_distrib_lattice (Π i, π i) :=
{ Sup := Sup,
  Inf := Inf,
  infi_sup_le_sup_Inf := λ a s i,
    by simp only [←sup_infi_eq, Inf_apply, ←infi_subtype'', infi_apply, pi.sup_apply],
  inf_Sup_le_supr_inf := λ a s i,
    by simp only [Sup_apply, supr_apply, pi.inf_apply, inf_supr_eq, ←supr_subtype''],
  .. pi.frame }

theorem Inf_sup_Inf : Inf s ⊔ Inf t = (⨅ p ∈ s ×ˢ t, (p : α × α).1 ⊔ p.2) :=
@Sup_inf_Sup (order_dual α) _ _ _

end complete_distrib_lattice

@[priority 100] -- see Note [lower instance priority]
instance complete_distrib_lattice.to_distrib_lattice [d : complete_distrib_lattice α] :
  distrib_lattice α :=
{ le_sup_inf := λ x y z, by rw [← Inf_pair, ← Inf_pair, sup_Inf_eq, ← Inf_image, set.image_pair],
  ..d }

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

theorem compl_Inf : (Inf s)ᶜ = (⨆ i ∈ s, iᶜ) :=
by simp only [Inf_eq_infi, compl_infi]

theorem compl_Sup : (Sup s)ᶜ = (⨅ i ∈ s, iᶜ) :=
by simp only [Sup_eq_supr, compl_supr]

end complete_boolean_algebra
