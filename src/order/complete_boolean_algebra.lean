/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Theory of complete Boolean algebras.
-/
import order.complete_lattice
import order.boolean_algebra

set_option old_structure_cmd true

universes u v w
variables {α : Type u} {β : Type v} {ι : Sort w}

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A complete distributive lattice is a bit stronger than the name might
  suggest; perhaps completely distributive lattice is more descriptive,
  as this class includes a requirement that the lattice join
  distribute over *arbitrary* infima, and similarly for the dual. -/
class complete_distrib_lattice α extends complete_lattice α :=
(infi_sup_le_sup_Inf : ∀a s, (⨅ b ∈ s, a ⊔ b) ≤ a ⊔ Inf s)
(inf_Sup_le_supr_inf : ∀a s, a ⊓ Sup s ≤ (⨆ b ∈ s, a ⊓ b))
end prio

section complete_distrib_lattice
variables [complete_distrib_lattice α] {a b : α} {s t : set α}

theorem sup_Inf_eq : a ⊔ Inf s = (⨅ b ∈ s, a ⊔ b) :=
le_antisymm
  (le_infi $ assume i, le_infi $ assume h, sup_le_sup_left (Inf_le h) _)
  (complete_distrib_lattice.infi_sup_le_sup_Inf _ _)

theorem Inf_sup_eq : Inf s ⊔ b = (⨅ a ∈ s, a ⊔ b) :=
by simpa [sup_comm] using @sup_Inf_eq α _ b s

theorem inf_Sup_eq : a ⊓ Sup s = (⨆ b ∈ s, a ⊓ b) :=
le_antisymm
  (complete_distrib_lattice.inf_Sup_le_supr_inf _ _)
  (supr_le $ assume i, supr_le $ assume h, inf_le_inf_left _ (le_Sup h))

theorem Sup_inf_eq : Sup s ⊓ b = (⨆ a ∈ s, a ⊓ b) :=
by simpa [inf_comm] using @inf_Sup_eq α _ b s

theorem Inf_sup_Inf : Inf s ⊔ Inf t = (⨅p ∈ set.prod s t, (p : α × α).1 ⊔ p.2) :=
begin
  apply le_antisymm,
  { finish },
  { have : ∀ a ∈ s, (⨅p ∈ set.prod s t, (p : α × α).1 ⊔ p.2) ≤ a ⊔ Inf t,
    { assume a ha,
      have : (⨅p ∈ set.prod s t, ((p : α × α).1 : α) ⊔ p.2) ≤
             (⨅p ∈ prod.mk a '' t, (p : α × α).1 ⊔ p.2),
      { apply infi_le_infi_of_subset,
        rintros ⟨x, y⟩,
        simp only [and_imp, set.mem_image, prod.mk.inj_iff, set.prod_mk_mem_set_prod_eq,
                   exists_imp_distrib],
        assume x' x't ax x'y,
        rw [← x'y, ← ax],
        simp [ha, x't] },
      rw [infi_image] at this,
      simp only at this,
      rwa ← sup_Inf_eq at this },
    calc (⨅p ∈ set.prod s t, (p : α × α).1 ⊔ p.2) ≤ (⨅a∈s, a ⊔ Inf t) : by simp; exact this
       ... = Inf s ⊔ Inf t : Inf_sup_eq.symm }
end

theorem Sup_inf_Sup : Sup s ⊓ Sup t = (⨆p ∈ set.prod s t, (p : α × α).1 ⊓ p.2) :=
begin
  apply le_antisymm,
  { have : ∀ a ∈ s, a ⊓ Sup t ≤ (⨆p ∈ set.prod s t, (p : α × α).1 ⊓ p.2),
    { assume a ha,
      have : (⨆p ∈ prod.mk a '' t, (p : α × α).1 ⊓ p.2)
             ≤ (⨆p ∈ set.prod s t, ((p : α × α).1 : α) ⊓ p.2),
      { apply supr_le_supr_of_subset,
        rintros ⟨x, y⟩,
        simp only [and_imp, set.mem_image, prod.mk.inj_iff, set.prod_mk_mem_set_prod_eq,
                   exists_imp_distrib],
        assume x' x't ax x'y,
        rw [← x'y, ← ax],
        simp [ha, x't] },
      rw [supr_image] at this,
      simp only at this,
      rwa ← inf_Sup_eq at this },
    calc Sup s ⊓ Sup t = (⨆a∈s, a ⊓ Sup t) : Sup_inf_eq
      ... ≤ (⨆p ∈ set.prod s t, (p : α × α).1 ⊓ p.2) : by simp; exact this },
  { finish }
end

end complete_distrib_lattice

@[priority 100] -- see Note [lower instance priority]
instance complete_distrib_lattice.bounded_distrib_lattice [d : complete_distrib_lattice α] :
  bounded_distrib_lattice α :=
{ le_sup_inf := λ x y z, by rw [← Inf_pair, ← Inf_pair, sup_Inf_eq, ← Inf_image, set.image_pair],
  ..d }

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A complete boolean algebra is a completely distributive boolean algebra. -/
class complete_boolean_algebra α extends boolean_algebra α, complete_distrib_lattice α
end prio

section complete_boolean_algebra
variables [complete_boolean_algebra α] {a b : α} {s : set α} {f : ι → α}

theorem compl_infi : (infi f)ᶜ = (⨆i, (f i)ᶜ) :=
le_antisymm
  (compl_le_of_compl_le $ le_infi $ assume i, compl_le_of_compl_le $ le_supr (compl ∘ f) i)
  (supr_le $ assume i, compl_le_compl $ infi_le _ _)

theorem compl_supr : (supr f)ᶜ = (⨅i, (f i)ᶜ) :=
compl_injective (by simp [compl_infi])

theorem compl_Inf : (Inf s)ᶜ = (⨆i∈s, iᶜ) :=
by simp only [Inf_eq_infi, compl_infi]

theorem compl_Sup : (Sup s)ᶜ = (⨅i∈s, iᶜ) :=
by simp only [Sup_eq_supr, compl_supr]

end complete_boolean_algebra
