/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import order.rel_iso
import order.lattice_intervals

/-!
# Modular Lattices
This file defines Modular Lattices, a kind of lattice useful in algebra.
For examples, look to the subobject lattices of abelian groups, submodules, and ideals, or consider
any distributive lattice.

## Main Definitions
- `is_modular_lattice` defines a modular lattice to be one such that
  `x ≤ z → (x ⊔ y) ⊓ z ≤ x ⊔ (y ⊓ z)`
- `diamond_iso` gives an order isomorphism between the intervals `[a ⊓ b, a]` and `[b, a ⊔ b]`.
  This corresponds to the diamond (or second) isomorphism theorems of algebra.

## Main Results
- `is_modular_lattice_iff_modular_identity`:
  Modularity is equivalent to the `modular_identity`: `(x ⊓ z) ⊔ (y ⊓ z) = ((x ⊓ z) ⊔ y) ⊓ z`
- `distrib_lattice.is_modular_lattice`: Distributive lattices are modular.

## To do
- Relate atoms and coatoms in modular lattices

-/

variable {α : Type*}

/-- A modular lattice is one with a limited associativity between `⊓` and `⊔`. -/
class is_modular_lattice α [lattice α] : Prop :=
(modular_law : ∀ {x y z : α}, x ≤ z → (x ⊔ y) ⊓ z ≤ x ⊔ (y ⊓ z))

section is_modular_lattice
variables [lattice α] [is_modular_lattice α ]

theorem sup_inf_assoc_of_le {x y z : α} (h : x ≤ z) :
  (x ⊔ y) ⊓ z = x ⊔ (y ⊓ z) :=
le_antisymm (is_modular_lattice.modular_law h)
  (le_inf (sup_le_sup_left inf_le_left _) (sup_le h inf_le_right))

theorem is_modular_lattice.modular_identity {x y z : α} :
  (x ⊓ z) ⊔ (y ⊓ z) = ((x ⊓ z) ⊔ y) ⊓ z :=
(sup_inf_assoc_of_le inf_le_right).symm

lemma inf_sup_assoc_of_le {x y z : α} (h : z ≤ x) :
  (x ⊓ y) ⊔ z = x ⊓ (y ⊔ z) :=
by rw [inf_comm, sup_comm, ← sup_inf_assoc_of_le h, inf_comm, sup_comm]

instance : is_modular_lattice (order_dual α) :=
⟨λ x y z xz, le_of_eq (by { rw [inf_comm, sup_comm, eq_comm, inf_comm, sup_comm],
  exact @sup_inf_assoc_of_le α _ _ _ y _ xz })⟩

/-- The diamond isomorphism between the intervals `[a ⊓ b, a]` and `[b, a ⊔ b]` -/
def diamond_iso (a b : α) : set.Icc (a ⊓ b) a ≃o set.Icc b (a ⊔ b) :=
{ to_fun := λ x, ⟨x ⊔ b, ⟨le_sup_right, sup_le_sup_right x.prop.2 b⟩⟩,
  inv_fun := λ x, ⟨a ⊓ x, ⟨inf_le_inf_left a x.prop.1, inf_le_left⟩⟩,
  left_inv := λ x, subtype.ext (by { dsimp,
    rw [sup_comm, ← inf_sup_assoc_of_le x.prop.2, sup_eq_right.2 x.prop.1] }),
  right_inv := λ x, subtype.ext (by { dsimp,
    rw [inf_comm, inf_sup_assoc_of_le x.prop.1, inf_eq_left.2 x.prop.2] }),
  map_rel_iff' := λ x y, begin
    dsimp,
    rw [subtype.mk_le_mk, ← subtype.coe_le_coe],
    refine ⟨λ h, sup_le_sup_right h _, λ h, _⟩,
    rw [← sup_eq_right.2 x.prop.1, inf_sup_assoc_of_le x.prop.2, sup_comm,
      ← sup_eq_right.2 y.prop.1, inf_sup_assoc_of_le y.prop.2, @sup_comm _ _ b],
    exact inf_le_inf_left _ h
  end }

end is_modular_lattice

section is_modular_lattice
variables [bounded_lattice α] [is_modular_lattice α]

/-- The diamond isomorphism between the intervals `set.Iic a` and `set.Ici b`. -/
def is_compl.diamond_iso {a b : α} (h : is_compl a b) : set.Iic a ≃o set.Ici b :=
(order_iso.set_congr (set.Iic a) (set.Icc (a ⊓ b) a) (h.inf_eq_bot.symm ▸ set.Icc_bot.symm)).trans $
  (diamond_iso a b).trans
  (order_iso.set_congr (set.Icc b (a ⊔ b)) (set.Ici b) (h.sup_eq_top.symm ▸ set.Icc_top))

end is_modular_lattice

theorem is_modular_lattice_iff_modular_identity [lattice α] :
  is_modular_lattice α ↔ ∀ (x y z : α), (x ⊓ z) ⊔ (y ⊓ z) = ((x ⊓ z) ⊔ y) ⊓ z :=
⟨λ h, @is_modular_lattice.modular_identity _ _ h, λ h, ⟨λ x y z xz, by rw [← inf_eq_left.2 xz, h]⟩⟩

namespace distrib_lattice

@[priority 100]
instance [distrib_lattice α] : is_modular_lattice α :=
⟨λ x y z xz, by rw [inf_sup_right, inf_eq_left.2 xz]⟩

end distrib_lattice

namespace is_modular_lattice

variables [bounded_lattice α] [is_modular_lattice α]

section is_complemented
variables [is_complemented α] {a : α}

theorem is_complemented_Iic : is_complemented (set.Iic a) :=
⟨λ ⟨x, hx⟩, ⟨⟨(classical.some (exists_is_compl x)) ⊓ a, set.mem_Iic.2 inf_le_right⟩, begin
    split,
    { change x ⊓ (classical.some _ ⊓ a) ≤ ⊥, -- improve lattice subtype API
      rw ← inf_assoc,
      exact le_trans inf_le_left (classical.some_spec (exists_is_compl x)).1 },
    { change a ≤ x ⊔ (classical.some _ ⊓ a), -- improve lattice subtype API
      rw [← sup_inf_assoc_of_le (set.mem_Iic.1 hx),
          top_le_iff.1 (classical.some_spec (exists_is_compl x)).2, top_inf_eq] }
  end⟩⟩

theorem is_complemented_Ici : is_complemented (set.Ici a) :=
⟨λ ⟨x, hx⟩, ⟨⟨(classical.some (exists_is_compl x)) ⊔ a, set.mem_Ici.2 le_sup_right⟩, begin
    split,
    { change x ⊓ (classical.some _ ⊔ a) ≤ a, -- improve lattice subtype API
      rw [← inf_sup_assoc_of_le (set.mem_Ici.1 hx),
          le_bot_iff.1 (classical.some_spec (exists_is_compl x)).1, bot_sup_eq] },
    { change ⊤ ≤ x ⊔ (classical.some _ ⊔ a), -- improve lattice subtype API
      rw ← sup_assoc,
      exact le_trans (classical.some_spec (exists_is_compl x)).2 le_sup_left }
  end⟩⟩

end is_complemented

end is_modular_lattice
