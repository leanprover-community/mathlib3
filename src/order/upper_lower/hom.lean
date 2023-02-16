/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.upper_lower.basic
import order.hom.complete_lattice

/-!
# `upper_set.Ici` etc as `sup`/`Sup`/`inf`/`Inf`-homomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `upper_set.Ici_sup_hom` etc. These functions are `upper_set.Ici` and
`lower_set.Iic` bundled as `sup_hom`s, `inf_hom`s, `Sup_hom`s, or `Inf_hom`s.
-/

variable {α : Type*}
open order_dual

namespace upper_set

section semilattice_sup

variable [semilattice_sup α]

/-- `upper_set.Ici` as a `sup_hom`. -/
def Ici_sup_hom : sup_hom α (upper_set α) := ⟨Ici, Ici_sup⟩

@[simp] lemma coe_Ici_sup_hom : (Ici_sup_hom : α → upper_set α) = Ici := rfl
@[simp] lemma Ici_sup_hom_apply (a : α) : Ici_sup_hom a = (Ici a) := rfl

end semilattice_sup

variable [complete_lattice α]

/-- `upper_set.Ici` as a `Sup_hom`. -/
def Ici_Sup_hom : Sup_hom α (upper_set α) := ⟨Ici, λ s, (Ici_Sup s).trans Sup_image.symm⟩

@[simp] lemma coe_Ici_Sup_hom : (Ici_Sup_hom : α → upper_set α) = Ici := rfl
@[simp] lemma Ici_Sup_hom_apply (a : α) : Ici_Sup_hom a = Ici a := rfl

end upper_set

namespace lower_set

section semilattice_inf

variable [semilattice_inf α]

/-- `lower_set.Iic` as an `inf_hom`. -/
def Iic_inf_hom : inf_hom α (lower_set α) := ⟨Iic, Iic_inf⟩

@[simp] lemma coe_Iic_inf_hom : (Iic_inf_hom : α → lower_set α) = Iic := rfl
@[simp] lemma Iic_inf_hom_apply (a : α) : Iic_inf_hom a = Iic a := rfl

end semilattice_inf

variable [complete_lattice α]

/-- `lower_set.Iic` as an `Inf_hom`. -/
def Iic_Inf_hom : Inf_hom α (lower_set α) := ⟨Iic, λ s, (Iic_Inf s).trans Inf_image.symm⟩

@[simp] lemma coe_Iic_Inf_hom : (Iic_Inf_hom : α → lower_set α) = Iic := rfl
@[simp] lemma Iic_Inf_hom_apply (a : α) : Iic_Inf_hom a = Iic a := rfl

end lower_set
