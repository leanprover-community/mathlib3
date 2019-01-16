/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Theory of complete Boolean algebras.
-/
import order.complete_lattice order.boolean_algebra data.set.basic

set_option old_structure_cmd true

universes u v w
variables {α : Type u} {β : Type v} {ι : Sort w}

namespace lattice

/-- A complete distributive lattice is a bit stronger than the name might
  suggest; perhaps completely distributive lattice is more descriptive,
  as this class includes a requirement that the lattice join
  distribute over *arbitrary* infima, and similarly for the dual. -/
class complete_distrib_lattice α extends complete_lattice α :=
(infi_sup_le_sup_Inf : ∀a s, (⨅ b ∈ s, a ⊔ b) ≤ a ⊔ Inf s)
(inf_Sup_le_supr_inf : ∀a s, a ⊓ Sup s ≤ (⨆ b ∈ s, a ⊓ b))

section complete_distrib_lattice
variables [complete_distrib_lattice α] {a : α} {s : set α}

theorem sup_Inf_eq : a ⊔ Inf s = (⨅ b ∈ s, a ⊔ b) :=
le_antisymm
  (le_infi $ assume i, le_infi $ assume h, sup_le_sup (le_refl _) (Inf_le h))
  (complete_distrib_lattice.infi_sup_le_sup_Inf _ _)

theorem inf_Sup_eq : a ⊓ Sup s = (⨆ b ∈ s, a ⊓ b) :=
le_antisymm
  (complete_distrib_lattice.inf_Sup_le_supr_inf _ _)
  (supr_le $ assume i, supr_le $ assume h, inf_le_inf (le_refl _) (le_Sup h))

end complete_distrib_lattice

instance [d : complete_distrib_lattice α] : bounded_distrib_lattice α :=
{ le_sup_inf := assume x y z,
    calc (x ⊔ y) ⊓ (x ⊔ z) ≤ (⨅ b ∈ ({z, y} : set α), x ⊔ b) :
        by simp [or_imp_distrib] {contextual := tt}
      ... = x ⊔ Inf {z, y} : sup_Inf_eq.symm
      ... = x ⊔ y ⊓ z : by rw insert_of_has_insert; simp,
  ..d }

/-- A complete boolean algebra is a completely distributive boolean algebra. -/
class complete_boolean_algebra α extends boolean_algebra α, complete_distrib_lattice α

section complete_boolean_algebra
variables [complete_boolean_algebra α] {a b : α} {s : set α} {f : ι → α}

theorem neg_infi : - infi f = (⨆i, - f i) :=
le_antisymm
  (neg_le_of_neg_le $ le_infi $ assume i, neg_le_of_neg_le $ le_supr (λi, - f i) i)
  (supr_le $ assume i, neg_le_neg $ infi_le _ _)

theorem neg_supr : - supr f = (⨅i, - f i) :=
neg_eq_neg_of_eq (by simp [neg_infi])

theorem neg_Inf : - Inf s = (⨆i∈s, - i) :=
by simp [Inf_eq_infi, neg_infi]

theorem neg_Sup : - Sup s = (⨅i∈s, - i) :=
by simp [Sup_eq_supr, neg_supr]

end complete_boolean_algebra

end lattice
