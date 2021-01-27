/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import order.rel_iso
import order.lattice_intervals
import order.order_dual

/-!
# Modular Lattices
This file defines Modular Lattices, a kind of lattice useful in algebra.
For examples, look to the subobject lattices of abelian groups, submodules, and ideals, or consider
any distributive lattice.

## Main Definitions
- `is_modular_lattice` defines a modular lattice to be one such that
  `x ≤ z → (x ⊔ y) ⊓ z ≤ x ⊔ (y ⊓ z)`
- `inf_Icc_order_iso_Icc_sup` gives an order isomorphism between the intervals
  `[a ⊓ b, a]` and `[b, a ⊔ b]`.
  This corresponds to the diamond (or second) isomorphism theorems of algebra.

## Main Results
- `is_modular_lattice_iff_sup_inf_sup_assoc`:
  Modularity is equivalent to the `sup_inf_sup_assoc`: `(x ⊓ z) ⊔ (y ⊓ z) = ((x ⊓ z) ⊔ y) ⊓ z`
- `distrib_lattice.is_modular_lattice`: Distributive lattices are modular.

## To do
- Relate atoms and coatoms in modular lattices

-/

variable {α : Type*}

/-- A modular lattice is one with a limited associativity between `⊓` and `⊔`. -/
class is_modular_lattice α [lattice α] : Prop :=
(sup_inf_le_assoc_of_le : ∀ {x : α} (y : α) {z : α}, x ≤ z → (x ⊔ y) ⊓ z ≤ x ⊔ (y ⊓ z))

section is_modular_lattice
variables [lattice α] [is_modular_lattice α ]

theorem sup_inf_assoc_of_le {x : α} (y : α) {z : α} (h : x ≤ z) :
  (x ⊔ y) ⊓ z = x ⊔ (y ⊓ z) :=
le_antisymm (is_modular_lattice.sup_inf_le_assoc_of_le y h)
  (le_inf (sup_le_sup_left inf_le_left _) (sup_le h inf_le_right))

theorem is_modular_lattice.sup_inf_sup_assoc {x y z : α} :
  (x ⊓ z) ⊔ (y ⊓ z) = ((x ⊓ z) ⊔ y) ⊓ z :=
(sup_inf_assoc_of_le y inf_le_right).symm

lemma inf_sup_assoc_of_le {x : α} (y : α) {z : α} (h : z ≤ x) :
  (x ⊓ y) ⊔ z = x ⊓ (y ⊔ z) :=
by rw [inf_comm, sup_comm, ← sup_inf_assoc_of_le y h, inf_comm, sup_comm]

instance : is_modular_lattice (order_dual α) :=
⟨λ x y z xz, le_of_eq (by { rw [inf_comm, sup_comm, eq_comm, inf_comm, sup_comm],
  convert sup_inf_assoc_of_le (order_dual.of_dual y) (order_dual.dual_le.2 xz) })⟩

/-- The diamond isomorphism between the intervals `[a ⊓ b, a]` and `[b, a ⊔ b]` -/
def inf_Icc_order_iso_Icc_sup (a b : α) : set.Icc (a ⊓ b) a ≃o set.Icc b (a ⊔ b) :=
{ to_fun := λ x, ⟨x ⊔ b, ⟨le_sup_right, sup_le_sup_right x.prop.2 b⟩⟩,
  inv_fun := λ x, ⟨a ⊓ x, ⟨inf_le_inf_left a x.prop.1, inf_le_left⟩⟩,
  left_inv := λ x, subtype.ext (by { change a ⊓ (↑x ⊔ b) = ↑x,
    rw [sup_comm, ← inf_sup_assoc_of_le _ x.prop.2, sup_eq_right.2 x.prop.1] }),
  right_inv := λ x, subtype.ext (by { change a ⊓ ↑x ⊔ b = ↑x,
    rw [inf_comm, inf_sup_assoc_of_le _ x.prop.1, inf_eq_left.2 x.prop.2] }),
  map_rel_iff' := λ x y, begin
    simp only [subtype.mk_le_mk, equiv.coe_fn_mk, and_true, le_sup_right],
    rw [← subtype.coe_le_coe],
    refine ⟨λ h, _, λ h, sup_le_sup_right h _⟩,
    rw [← sup_eq_right.2 x.prop.1, inf_sup_assoc_of_le _ x.prop.2, sup_comm,
      ← sup_eq_right.2 y.prop.1, inf_sup_assoc_of_le _ y.prop.2, @sup_comm _ _ b],
    exact inf_le_inf_left _ h
  end }
end is_modular_lattice

namespace is_compl
variables [bounded_lattice α] [is_modular_lattice α]

/-- The diamond isomorphism between the intervals `set.Iic a` and `set.Ici b`. -/
def Iic_order_iso_Ici {a b : α} (h : is_compl a b) : set.Iic a ≃o set.Ici b :=
(order_iso.set_congr (set.Iic a) (set.Icc (a ⊓ b) a) (h.inf_eq_bot.symm ▸ set.Icc_bot.symm)).trans $
  (inf_Icc_order_iso_Icc_sup a b).trans
  (order_iso.set_congr (set.Icc b (a ⊔ b)) (set.Ici b) (h.sup_eq_top.symm ▸ set.Icc_top))

end is_compl

theorem is_modular_lattice_iff_sup_inf_sup_assoc [lattice α] :
  is_modular_lattice α ↔ ∀ (x y z : α), (x ⊓ z) ⊔ (y ⊓ z) = ((x ⊓ z) ⊔ y) ⊓ z :=
⟨λ h, @is_modular_lattice.sup_inf_sup_assoc _ _ h, λ h, ⟨λ x y z xz, by rw [← inf_eq_left.2 xz, h]⟩⟩

namespace distrib_lattice

@[priority 100]
instance [distrib_lattice α] : is_modular_lattice α :=
⟨λ x y z xz, by rw [inf_sup_right, inf_eq_left.2 xz]⟩

end distrib_lattice

namespace is_modular_lattice

variables [bounded_lattice α] [is_modular_lattice α] {a : α}

instance is_modular_lattice_Iic : is_modular_lattice (set.Iic a) :=
⟨λ x y z xz, (sup_inf_le_assoc_of_le (y : α) xz : (↑x ⊔ ↑y) ⊓ ↑z ≤ ↑x ⊔ ↑y ⊓ ↑z)⟩

instance is_modular_lattice_Ici : is_modular_lattice (set.Ici a) :=
⟨λ x y z xz, (sup_inf_le_assoc_of_le (y : α) xz : (↑x ⊔ ↑y) ⊓ ↑z ≤ ↑x ⊔ ↑y ⊓ ↑z)⟩

end is_modular_lattice
