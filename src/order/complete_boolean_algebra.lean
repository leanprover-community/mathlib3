/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import order.complete_lattice

/-!
# Completely distributive lattices and Boolean algebras

In this file there are definitions and an API for completely distributive lattices and completely
distributive Boolean algebras.

## Typeclasses

* `complete_distrib_lattice`: Completely distributive lattices: A complete lattice whose `⊓` and `⊔`
  distribute over `⨆` and `⨅` respectively.
* `complete_boolean_algebra`: Completely distributive Boolean algebra: A Boolean algebra whose `⊓`
  and `⊔` distribute over `⨆` and `⨅` respectively.
-/

set_option old_structure_cmd true

universes u v w
variables {α : Type u} {β : Type v} {ι : Sort w}

/-- A complete distributive lattice is a bit stronger than the name might
  suggest; perhaps completely distributive lattice is more descriptive,
  as this class includes a requirement that the lattice join
  distribute over *arbitrary* infima, and similarly for the dual. -/
class complete_distrib_lattice α extends complete_lattice α :=
(infi_sup_le_sup_Inf : ∀ a s, (⨅ b ∈ s, a ⊔ b) ≤ a ⊔ Inf s)
(inf_Sup_le_supr_inf : ∀ a s, a ⊓ Sup s ≤ (⨆ b ∈ s, a ⊓ b))

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

theorem inf_Sup_eq : a ⊓ Sup s = (⨆ b ∈ s, a ⊓ b) :=
(complete_distrib_lattice.inf_Sup_le_supr_inf _ _).antisymm supr_inf_le_inf_Sup

theorem Sup_inf_eq : Sup s ⊓ b = (⨆ a ∈ s, a ⊓ b) :=
by simpa only [inf_comm] using @inf_Sup_eq α _ b s

theorem supr_inf_eq (f : ι → α) (a : α) : (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a :=
by rw [supr, Sup_inf_eq, supr_range]

theorem inf_supr_eq (a : α) (f : ι → α) : a ⊓ (⨆ i, f i) = ⨆ i, a ⊓ f i :=
by simpa only [inf_comm] using supr_inf_eq f a

theorem infi_sup_eq (f : ι → α) (a : α) : (⨅ i, f i) ⊔ a = ⨅ i, f i ⊔ a :=
@supr_inf_eq (order_dual α) _ _ _ _

theorem sup_infi_eq (a : α) (f : ι → α) : a ⊔ (⨅ i, f i) = ⨅ i, a ⊔ f i :=
@inf_supr_eq (order_dual α) _ _ _ _

theorem bsupr_inf_eq {p : α → Prop} {f : Π i (hi : p i), α} (a : α) :
  (⨆ i hi, f i hi) ⊓ a = ⨆ i hi, f i hi ⊓ a :=
by simp only [supr_inf_eq]

theorem inf_bsupr_eq (a : α) {p : α → Prop} {f : Π i (hi : p i), α} :
  a ⊓ (⨆ i hi, f i hi) = ⨆ i hi, a ⊓ f i hi :=
by simp only [inf_supr_eq]

theorem binfi_sup_eq {p : α → Prop} {f : Π i (hi : p i), α} (a : α) :
  (⨅ i hi, f i hi) ⊔ a = ⨅ i hi, f i hi ⊔ a :=
@bsupr_inf_eq (order_dual α) _ _ _ _

theorem sup_binfi_eq (a : α) {p : α → Prop} {f : Π i (hi : p i), α} :
  a ⊔ (⨅ i hi, f i hi) = ⨅ i hi, a ⊔ f i hi :=
@inf_bsupr_eq (order_dual α) _ _ _ _

instance pi.complete_distrib_lattice {ι : Type*} {π : ι → Type*}
  [∀ i, complete_distrib_lattice (π i)] : complete_distrib_lattice (Π i, π i) :=
{ infi_sup_le_sup_Inf := λ a s i,
    by simp only [← sup_infi_eq, complete_lattice.Inf, Inf_apply, ←infi_subtype'', infi_apply,
      pi.sup_apply],
  inf_Sup_le_supr_inf := λ a s i,
    by simp only [complete_lattice.Sup, Sup_apply, supr_apply, pi.inf_apply, inf_supr_eq,
      ← supr_subtype''],
  .. pi.complete_lattice }

theorem Inf_sup_Inf : Inf s ⊔ Inf t = (⨅ p ∈ set.prod s t, (p : α × α).1 ⊔ p.2) :=
begin
  apply le_antisymm,
  { simp only [and_imp, prod.forall, le_infi_iff, set.mem_prod],
    intros a b ha hb,
    exact sup_le_sup (Inf_le ha) (Inf_le hb) },
  { have : ∀ a ∈ s, (⨅ p ∈ set.prod s t, (p : α × α).1 ⊔ p.2) ≤ a ⊔ Inf t,
    { rintro a ha,
      have : (⨅ p ∈ set.prod s t, ((p : α × α).1 : α) ⊔ p.2) ≤
             (⨅ p ∈ prod.mk a '' t, (p : α × α).1 ⊔ p.2),
      { apply infi_le_infi_of_subset,
        rintro ⟨x, y⟩,
        simp only [and_imp, set.mem_image, prod.mk.inj_iff, set.prod_mk_mem_set_prod_eq,
                   exists_imp_distrib],
        rintro x' x't ax x'y,
        rw [← x'y, ← ax],
        simp [ha, x't] },
      rw [infi_image] at this,
      simp only at this,
      rwa ← sup_Inf_eq at this },
    calc (⨅ p ∈ set.prod s t, (p : α × α).1 ⊔ p.2) ≤ (⨅ a ∈ s, a ⊔ Inf t) : by simp; exact this
       ... = Inf s ⊔ Inf t : Inf_sup_eq.symm }
end

theorem Sup_inf_Sup : Sup s ⊓ Sup t = (⨆ p ∈ set.prod s t, (p : α × α).1 ⊓ p.2) :=
@Inf_sup_Inf (order_dual α) _ _ _

lemma supr_disjoint_iff {f : ι → α} : disjoint (⨆ i, f i) a ↔ ∀ i, disjoint (f i) a :=
by simp only [disjoint_iff, supr_inf_eq, supr_eq_bot]

lemma disjoint_supr_iff {f : ι → α} : disjoint a (⨆ i, f i) ↔ ∀ i, disjoint a (f i) :=
by simpa only [disjoint.comm] using @supr_disjoint_iff _ _ _ a f

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
