/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/

import order.complete_boolean_algebra
import order.modular_lattice
import data.fintype.basic

/-!
# Atoms, Coatoms, and Simple Lattices

This module defines atoms, which are minimal non-`⊥` elements in bounded lattices, simple lattices,
which are lattices with only two elements, and related ideas.

## Main definitions

### Atoms and Coatoms
  * `is_atom a` indicates that the only element below `a` is `⊥`.
  * `is_coatom a` indicates that the only element above `a` is `⊤`.

### Atomic and Atomistic Lattices
  * `is_atomic` indicates that every element other than `⊥` is above an atom.
  * `is_coatomic` indicates that every element other than `⊤` is below a coatom.
  * `is_atomistic` indicates that every element is the `Sup` of a set of atoms.
  * `is_coatomistic` indicates that every element is the `Inf` of a set of coatoms.

### Simple Lattices
  * `is_simple_lattice` indicates that a bounded lattice has only two elements, `⊥` and `⊤`.
  * `is_simple_lattice.bounded_distrib_lattice`
  * Given an instance of `is_simple_lattice`, we provide the following definitions. These are not
    made global instances as they contain data :
    * `is_simple_lattice.boolean_algebra`
    * `is_simple_lattice.complete_lattice`
    * `is_simple_lattice.complete_boolean_algebra`

## Main results
  * `is_atom_dual_iff_is_coatom` and `is_coatom_dual_iff_is_atom` express the (definitional) duality
   of `is_atom` and `is_coatom`.
  * `is_simple_lattice_iff_is_atom_top` and `is_simple_lattice_iff_is_coatom_bot` express the
  connection between atoms, coatoms, and simple lattices
  * `is_compl.is_atom_iff_is_coatom` and `is_compl.is_coatom_if_is_atom`: In a modular
  bounded lattice, a complement of an atom is a coatom and vice versa.
  * ``is_atomic_iff_is_coatomic`: A modular complemented lattice is atomic iff it is coatomic.

-/

variable {α : Type*}

section atoms

section is_atom

variable [order_bot α]

/-- An atom of an `order_bot` is an element with no other element between it and `⊥`,
  which is not `⊥`. -/
def is_atom (a : α) : Prop := a ≠ ⊥ ∧ (∀ b, b < a → b = ⊥)

lemma eq_bot_or_eq_of_le_atom {a b : α} (ha : is_atom a) (hab : b ≤ a) : b = ⊥ ∨ b = a :=
hab.lt_or_eq.imp_left (ha.2 b)

lemma is_atom.Iic {x a : α} (ha : is_atom a) (hax : a ≤ x) : is_atom (⟨a, hax⟩ : set.Iic x) :=
⟨λ con, ha.1 (subtype.mk_eq_mk.1 con), λ ⟨b, hb⟩ hba, subtype.mk_eq_mk.2 (ha.2 b hba)⟩

lemma is_atom.of_is_atom_coe_Iic {x : α} {a : set.Iic x} (ha : is_atom a) : is_atom (a : α) :=
⟨λ con, ha.1 (subtype.ext con), λ b hba, subtype.mk_eq_mk.1 (ha.2 ⟨b, hba.le.trans a.prop⟩ hba)⟩

end is_atom

section is_coatom

variable [order_top α]

/-- A coatom of an `order_top` is an element with no other element between it and `⊤`,
  which is not `⊤`. -/
def is_coatom (a : α) : Prop := a ≠ ⊤ ∧ (∀ b, a < b → b = ⊤)

lemma eq_top_or_eq_of_coatom_le {a b : α} (ha : is_coatom a) (hab : a ≤ b) : b = ⊤ ∨ b = a :=
hab.lt_or_eq.imp (ha.2 b) eq_comm.2

lemma is_coatom.Ici {x a : α} (ha : is_coatom a) (hax : x ≤ a) : is_coatom (⟨a, hax⟩ : set.Ici x) :=
⟨λ con, ha.1 (subtype.mk_eq_mk.1 con), λ ⟨b, hb⟩ hba, subtype.mk_eq_mk.2 (ha.2 b hba)⟩

lemma is_coatom.of_is_coatom_coe_Ici {x : α} {a : set.Ici x} (ha : is_coatom a) :
  is_coatom (a : α) :=
⟨λ con, ha.1 (subtype.ext con), λ b hba, subtype.mk_eq_mk.1 (ha.2 ⟨b, le_trans a.prop hba.le⟩ hba)⟩

end is_coatom

section pairwise

lemma is_atom.inf_eq_bot_of_ne [semilattice_inf_bot α] {a b : α}
  (ha : is_atom a) (hb : is_atom b) (hab : a ≠ b) : a ⊓ b = ⊥ :=
or.elim (eq_bot_or_eq_of_le_atom ha inf_le_left) id
  (λ h1, or.elim (eq_bot_or_eq_of_le_atom hb inf_le_right) id
  (λ h2, false.rec _ (hab (le_antisymm (inf_eq_left.mp h1) (inf_eq_right.mp h2)))))

lemma is_atom.disjoint_of_ne [semilattice_inf_bot α] {a b : α}
  (ha : is_atom a) (hb : is_atom b) (hab : a ≠ b) : disjoint a b :=
disjoint_iff.mpr (is_atom.inf_eq_bot_of_ne ha hb hab)

lemma is_coatom.sup_eq_top_of_ne [semilattice_sup_top α] {a b : α}
  (ha : is_coatom a) (hb : is_coatom b) (hab : a ≠ b) : a ⊔ b = ⊤ :=
or.elim (eq_top_or_eq_of_coatom_le ha le_sup_left) id
  (λ h1, or.elim (eq_top_or_eq_of_coatom_le hb le_sup_right) id
  (λ h2, false.rec _ (hab (le_antisymm (sup_eq_right.mp h2) (sup_eq_left.mp h1)))))

end pairwise

variable {a : α}

@[simp]
lemma is_coatom_dual_iff_is_atom [order_bot α] : is_coatom (order_dual.to_dual a) ↔ is_atom a :=
iff.rfl

@[simp]
lemma is_atom_dual_iff_is_coatom [order_top α] : is_atom (order_dual.to_dual a) ↔ is_coatom a :=
iff.rfl

end atoms

section atomic

variable (α)

/-- A lattice is atomic iff every element other than `⊥` has an atom below it. -/
class is_atomic [order_bot α] : Prop :=
(eq_bot_or_exists_atom_le : ∀ (b : α), b = ⊥ ∨ ∃ (a : α), is_atom a ∧ a ≤ b)

/-- A lattice is coatomic iff every element other than `⊤` has a coatom above it. -/
class is_coatomic [order_top α] : Prop :=
(eq_top_or_exists_le_coatom : ∀ (b : α), b = ⊤ ∨ ∃ (a : α), is_coatom a ∧ b ≤ a)

export is_atomic (eq_bot_or_exists_atom_le) is_coatomic (eq_top_or_exists_le_coatom)

variable {α}

@[simp] theorem is_coatomic_dual_iff_is_atomic [order_bot α] :
  is_coatomic (order_dual α) ↔ is_atomic α :=
⟨λ h, ⟨λ b, by apply h.eq_top_or_exists_le_coatom⟩, λ h, ⟨λ b, by apply h.eq_bot_or_exists_atom_le⟩⟩

@[simp] theorem is_atomic_dual_iff_is_coatomic [order_top α] :
  is_atomic (order_dual α) ↔ is_coatomic α :=
⟨λ h, ⟨λ b, by apply h.eq_bot_or_exists_atom_le⟩, λ h, ⟨λ b, by apply h.eq_top_or_exists_le_coatom⟩⟩

namespace is_atomic

variables [order_bot α] [is_atomic α]

instance is_coatomic_dual : is_coatomic (order_dual α) :=
is_coatomic_dual_iff_is_atomic.2 ‹is_atomic α›

instance {x : α} : is_atomic (set.Iic x) :=
⟨λ ⟨y, hy⟩, (eq_bot_or_exists_atom_le y).imp subtype.mk_eq_mk.2
  (λ ⟨a, ha, hay⟩, ⟨⟨a, hay.trans hy⟩, ha.Iic (hay.trans hy), hay⟩)⟩

end is_atomic

namespace is_coatomic

variables [order_top α] [is_coatomic α]

instance is_coatomic : is_atomic (order_dual α) :=
is_atomic_dual_iff_is_coatomic.2 ‹is_coatomic α›

instance {x : α} : is_coatomic (set.Ici x) :=
⟨λ ⟨y, hy⟩, (eq_top_or_exists_le_coatom y).imp subtype.mk_eq_mk.2
  (λ ⟨a, ha, hay⟩, ⟨⟨a, le_trans hy hay⟩, ha.Ici (le_trans hy hay), hay⟩)⟩

end is_coatomic

theorem is_atomic_iff_forall_is_atomic_Iic [order_bot α] :
  is_atomic α ↔ ∀ (x : α), is_atomic (set.Iic x) :=
⟨@is_atomic.set.Iic.is_atomic _ _, λ h, ⟨λ x, ((@eq_bot_or_exists_atom_le _ _ (h x))
  (⊤ : set.Iic x)).imp subtype.mk_eq_mk.1 (exists_imp_exists' coe
  (λ ⟨a, ha⟩, and.imp_left (is_atom.of_is_atom_coe_Iic)))⟩⟩

theorem is_coatomic_iff_forall_is_coatomic_Ici [order_top α] :
  is_coatomic α ↔ ∀ (x : α), is_coatomic (set.Ici x) :=
is_atomic_dual_iff_is_coatomic.symm.trans $ is_atomic_iff_forall_is_atomic_Iic.trans $ forall_congr
  (λ x, is_coatomic_dual_iff_is_atomic.symm.trans iff.rfl)

end atomic

section atomistic

variables (α) [complete_lattice α]

/-- A lattice is atomistic iff every element is a `Sup` of a set of atoms. -/
class is_atomistic : Prop :=
(eq_Sup_atoms : ∀ (b : α), ∃ (s : set α), b = Sup s ∧ ∀ a, a ∈ s → is_atom a)

/-- A lattice is coatomistic iff every element is an `Inf` of a set of coatoms. -/
class is_coatomistic : Prop :=
(eq_Inf_coatoms : ∀ (b : α), ∃ (s : set α), b = Inf s ∧ ∀ a, a ∈ s → is_coatom a)

export is_atomistic (eq_Sup_atoms) is_coatomistic (eq_Inf_coatoms)

variable {α}

@[simp]
theorem is_coatomistic_dual_iff_is_atomistic : is_coatomistic (order_dual α) ↔ is_atomistic α :=
⟨λ h, ⟨λ b, by apply h.eq_Inf_coatoms⟩, λ h, ⟨λ b, by apply h.eq_Sup_atoms⟩⟩

@[simp]
theorem is_atomistic_dual_iff_is_coatomistic : is_atomistic (order_dual α) ↔ is_coatomistic α :=
⟨λ h, ⟨λ b, by apply h.eq_Sup_atoms⟩, λ h, ⟨λ b, by apply h.eq_Inf_coatoms⟩⟩

namespace is_atomistic

instance is_coatomistic_dual [h : is_atomistic α] : is_coatomistic (order_dual α) :=
is_coatomistic_dual_iff_is_atomistic.2 h

variable [is_atomistic α]

@[priority 100]
instance : is_atomic α :=
⟨λ b, by { rcases eq_Sup_atoms b with ⟨s, rfl, hs⟩,
  cases s.eq_empty_or_nonempty with h h,
  { simp [h] },
  { exact or.intro_right _ ⟨h.some, hs _ h.some_spec, le_Sup h.some_spec⟩ } } ⟩

end is_atomistic

section is_atomistic
variables [is_atomistic α]

@[simp]
theorem Sup_atoms_le_eq (b : α) : Sup {a : α | is_atom a ∧ a ≤ b} = b :=
begin
  rcases eq_Sup_atoms b with ⟨s, rfl, hs⟩,
  exact le_antisymm (Sup_le (λ _, and.right)) (Sup_le_Sup (λ a ha, ⟨hs a ha, le_Sup ha⟩)),
end

@[simp]
theorem Sup_atoms_eq_top : Sup {a : α | is_atom a} = ⊤ :=
begin
  refine eq.trans (congr rfl (set.ext (λ x, _))) (Sup_atoms_le_eq ⊤),
  exact (and_iff_left le_top).symm,
end

theorem le_iff_atom_le_imp {a b : α} :
  a ≤ b ↔ ∀ c : α, is_atom c → c ≤ a → c ≤ b :=
⟨λ ab c hc ca, le_trans ca ab, λ h, begin
  rw [← Sup_atoms_le_eq a, ← Sup_atoms_le_eq b],
  exact Sup_le_Sup (λ c hc, ⟨hc.1, h c hc.1 hc.2⟩),
end⟩

end is_atomistic

namespace is_coatomistic

instance is_atomistic_dual [h : is_coatomistic α] : is_atomistic (order_dual α) :=
is_atomistic_dual_iff_is_coatomistic.2 h

variable [is_coatomistic α]

@[priority 100]
instance : is_coatomic α :=
⟨λ b, by { rcases eq_Inf_coatoms b with ⟨s, rfl, hs⟩,
  cases s.eq_empty_or_nonempty with h h,
  { simp [h] },
  { exact or.intro_right _ ⟨h.some, hs _ h.some_spec, Inf_le h.some_spec⟩ } } ⟩

end is_coatomistic
end atomistic

/-- A lattice is simple iff it has only two elements, `⊥` and `⊤`. -/
class is_simple_lattice (α : Type*) [bounded_lattice α] extends nontrivial α : Prop :=
(eq_bot_or_eq_top : ∀ (a : α), a = ⊥ ∨ a = ⊤)

export is_simple_lattice (eq_bot_or_eq_top)

theorem is_simple_lattice_iff_is_simple_lattice_order_dual [bounded_lattice α] :
  is_simple_lattice α ↔ is_simple_lattice (order_dual α) :=
begin
  split; intro i; haveI := i,
  { exact { exists_pair_ne := @exists_pair_ne α _,
      eq_bot_or_eq_top := λ a, or.symm (eq_bot_or_eq_top ((order_dual.of_dual a)) : _ ∨ _) } },
  { exact { exists_pair_ne := @exists_pair_ne (order_dual α) _,
      eq_bot_or_eq_top := λ a, or.symm (eq_bot_or_eq_top (order_dual.to_dual a)) } }
end

section is_simple_lattice

variables [bounded_lattice α] [is_simple_lattice α]

instance : is_simple_lattice (order_dual α) :=
is_simple_lattice_iff_is_simple_lattice_order_dual.1 (by apply_instance)

@[simp] lemma is_atom_top : is_atom (⊤ : α) :=
⟨top_ne_bot, λ a ha, or.resolve_right (eq_bot_or_eq_top a) (ne_of_lt ha)⟩

@[simp] lemma is_coatom_bot : is_coatom (⊥ : α) := is_atom_dual_iff_is_coatom.1 is_atom_top

end is_simple_lattice

namespace is_simple_lattice

section bounded_lattice

variables [bounded_lattice α] [is_simple_lattice α]

/-- A simple `bounded_lattice` is also distributive. -/
@[priority 100]
instance : bounded_distrib_lattice α :=
{ le_sup_inf := λ x y z, by { rcases eq_bot_or_eq_top x with rfl | rfl; simp },
  .. (infer_instance : bounded_lattice α) }

@[priority 100]
instance : is_atomic α :=
⟨λ b, (eq_bot_or_eq_top b).imp_right (λ h, ⟨⊤, ⟨is_atom_top, ge_of_eq h⟩⟩)⟩

@[priority 100]
instance : is_coatomic α := is_atomic_dual_iff_is_coatomic.1 is_simple_lattice.is_atomic

end bounded_lattice

/- It is important that in this section `is_simple_lattice` is the last type-class argument. -/
section decidable_eq

variables [decidable_eq α] [bounded_lattice α] [is_simple_lattice α]

/-- Every simple lattice is order-isomorphic to `bool`. -/
def order_iso_bool : α ≃o bool :=
{ to_fun := λ x, x = ⊤,
  inv_fun := λ x, cond x ⊤ ⊥,
  left_inv := λ x, by { rcases (eq_bot_or_eq_top x) with rfl | rfl; simp [bot_ne_top] },
  right_inv := λ x, by { cases x; simp [bot_ne_top] },
  map_rel_iff' := λ a b, begin
    rcases (eq_bot_or_eq_top a) with rfl | rfl,
    { simp [bot_ne_top] },
    { rcases (eq_bot_or_eq_top b) with rfl | rfl,
      { simp [bot_ne_top.symm, bot_ne_top, bool.ff_lt_tt] },
      { simp [bot_ne_top] } }
  end }

/- It is important that `is_simple_lattice` is the last type-class argument of this instance,
so that type-class inference fails quickly if it doesn't apply. -/
@[priority 200]
instance : fintype α := fintype.of_equiv bool (order_iso_bool.to_equiv).symm

/-- A simple `bounded_lattice` is also a `boolean_algebra`. -/
protected def boolean_algebra : boolean_algebra α :=
{ compl := λ x, if x = ⊥ then ⊤ else ⊥,
  sdiff := λ x y, if x = ⊤ ∧ y = ⊥ then ⊤ else ⊥,
  sdiff_eq := λ x y, by rcases eq_bot_or_eq_top x with rfl | rfl;
      simp [bot_ne_top, has_sdiff.sdiff, compl],
  inf_compl_le_bot := λ x, by rcases eq_bot_or_eq_top x with rfl | rfl; simp,
  top_le_sup_compl := λ x, by rcases eq_bot_or_eq_top x with rfl | rfl; simp,
  sup_inf_sdiff := λ x y, by rcases eq_bot_or_eq_top x with rfl | rfl;
      rcases eq_bot_or_eq_top y with rfl | rfl; simp [bot_ne_top],
  inf_inf_sdiff := λ x y, by rcases eq_bot_or_eq_top x with rfl | rfl;
      rcases eq_bot_or_eq_top y with rfl | rfl; simp,
  .. is_simple_lattice.bounded_distrib_lattice }

end decidable_eq

variables [bounded_lattice α] [is_simple_lattice α]
open_locale classical

/-- A simple `bounded_lattice` is also complete. -/
protected noncomputable def complete_lattice : complete_lattice α :=
{ Sup := λ s, if ⊤ ∈ s then ⊤ else ⊥,
  Inf := λ s, if ⊥ ∈ s then ⊥ else ⊤,
  le_Sup := λ s x h, by { rcases eq_bot_or_eq_top x with rfl | rfl,
    { exact bot_le },
    { rw if_pos h } },
  Sup_le := λ s x h, by { rcases eq_bot_or_eq_top x with rfl | rfl,
    { rw if_neg,
      intro con,
      exact bot_ne_top (eq_top_iff.2 (h ⊤ con)) },
    { exact le_top } },
  Inf_le := λ s x h, by { rcases eq_bot_or_eq_top x with rfl | rfl,
    { rw if_pos h },
    { exact le_top } },
  le_Inf := λ s x h, by { rcases eq_bot_or_eq_top x with rfl | rfl,
    { exact bot_le },
    { rw if_neg,
      intro con,
      exact top_ne_bot (eq_bot_iff.2 (h ⊥ con)) } },
  .. (infer_instance : bounded_lattice α) }

/-- A simple `bounded_lattice` is also a `complete_boolean_algebra`. -/
protected noncomputable def complete_boolean_algebra : complete_boolean_algebra α :=
{ infi_sup_le_sup_Inf := λ x s, by { rcases eq_bot_or_eq_top x with rfl | rfl,
    { simp only [bot_sup_eq, ← Inf_eq_infi], apply le_refl },
    { simp only [top_sup_eq, le_top] }, },
  inf_Sup_le_supr_inf := λ x s, by { rcases eq_bot_or_eq_top x with rfl | rfl,
    { simp only [bot_inf_eq, bot_le] },
    { simp only [top_inf_eq, ← Sup_eq_supr], apply le_refl } },
  .. is_simple_lattice.complete_lattice,
  .. is_simple_lattice.boolean_algebra }

end is_simple_lattice

namespace is_simple_lattice
variables [complete_lattice α] [is_simple_lattice α]
set_option default_priority 100

instance : is_atomistic α :=
⟨λ b, (eq_bot_or_eq_top b).elim
  (λ h, ⟨∅, ⟨h.trans Sup_empty.symm, λ a ha, false.elim (set.not_mem_empty _ ha)⟩⟩)
  (λ h, ⟨{⊤}, h.trans Sup_singleton.symm, λ a ha, (set.mem_singleton_iff.1 ha).symm ▸ is_atom_top⟩)⟩

instance : is_coatomistic α := is_atomistic_dual_iff_is_coatomistic.1 is_simple_lattice.is_atomistic

end is_simple_lattice
namespace fintype
namespace is_simple_lattice
variables [bounded_lattice α] [is_simple_lattice α] [decidable_eq α]

lemma univ : (finset.univ : finset α) = {⊤, ⊥} :=
begin
  change finset.map _ (finset.univ : finset bool) = _,
  rw fintype.univ_bool,
  simp only [finset.map_insert, function.embedding.coe_fn_mk, finset.map_singleton],
  refl,
end

lemma card : fintype.card α = 2 :=
(fintype.of_equiv_card _).trans fintype.card_bool

end is_simple_lattice
end fintype

namespace bool

instance : is_simple_lattice bool :=
⟨λ a, begin
  rw [← finset.mem_singleton, or.comm, ← finset.mem_insert,
      top_eq_tt, bot_eq_ff, ← fintype.univ_bool],
  apply finset.mem_univ,
end⟩

end bool

theorem is_simple_lattice_iff_is_atom_top [bounded_lattice α] :
  is_simple_lattice α ↔ is_atom (⊤ : α) :=
⟨λ h, @is_atom_top _ _ h, λ h, {
  exists_pair_ne := ⟨⊤, ⊥, h.1⟩,
  eq_bot_or_eq_top := λ a, ((eq_or_lt_of_le (@le_top _ _ a)).imp_right (h.2 a)).symm }⟩

theorem is_simple_lattice_iff_is_coatom_bot [bounded_lattice α] :
  is_simple_lattice α ↔ is_coatom (⊥ : α) :=
is_simple_lattice_iff_is_simple_lattice_order_dual.trans is_simple_lattice_iff_is_atom_top

namespace set

theorem is_simple_lattice_Iic_iff_is_atom [bounded_lattice α] {a : α} :
  is_simple_lattice (Iic a) ↔ is_atom a :=
is_simple_lattice_iff_is_atom_top.trans $ and_congr (not_congr subtype.mk_eq_mk)
  ⟨λ h b ab, subtype.mk_eq_mk.1 (h ⟨b, le_of_lt ab⟩ ab),
    λ h ⟨b, hab⟩ hbotb, subtype.mk_eq_mk.2 (h b (subtype.mk_lt_mk.1 hbotb))⟩

theorem is_simple_lattice_Ici_iff_is_coatom [bounded_lattice α] {a : α} :
  is_simple_lattice (Ici a) ↔ is_coatom a :=
is_simple_lattice_iff_is_coatom_bot.trans $ and_congr (not_congr subtype.mk_eq_mk)
  ⟨λ h b ab, subtype.mk_eq_mk.1 (h ⟨b, le_of_lt ab⟩ ab),
    λ h ⟨b, hab⟩ hbotb, subtype.mk_eq_mk.2 (h b (subtype.mk_lt_mk.1 hbotb))⟩

end set

namespace order_iso

@[simp] lemma is_atom_iff [order_bot α] {β : Type*} [order_bot β] (f : α ≃o β) (a : α) :
  is_atom (f a) ↔ is_atom a :=
and_congr (not_congr ⟨λ h, f.injective (f.map_bot.symm ▸ h), λ h, f.map_bot ▸ (congr rfl h)⟩)
  ⟨λ h b hb, f.injective ((h (f b) ((f : α ↪o β).lt_iff_lt.2 hb)).trans f.map_bot.symm),
  λ h b hb, f.symm.injective begin
    rw f.symm.map_bot,
    apply h,
    rw [← f.symm_apply_apply a],
    exact (f.symm : β ↪o α).lt_iff_lt.2 hb,
  end⟩

@[simp] lemma is_coatom_iff [order_top α] {β : Type*} [order_top β] (f : α ≃o β) (a : α) :
  is_coatom (f a) ↔ is_coatom a :=
f.dual.is_atom_iff a

lemma is_simple_lattice_iff [bounded_lattice α] {β : Type*} [bounded_lattice β] (f : α ≃o β) :
  is_simple_lattice α ↔ is_simple_lattice β :=
by rw [is_simple_lattice_iff_is_atom_top, is_simple_lattice_iff_is_atom_top,
  ← f.is_atom_iff ⊤, f.map_top]

lemma is_simple_lattice [bounded_lattice α] {β : Type*} [bounded_lattice β]
  [h : is_simple_lattice β] (f : α ≃o β) :
  is_simple_lattice α :=
f.is_simple_lattice_iff.mpr h

lemma is_atomic_iff [order_bot α] {β : Type*} [order_bot β] (f : α ≃o β) :
  is_atomic α ↔ is_atomic β :=
begin
  suffices : (∀ b : α, b = ⊥ ∨ ∃ (a : α), is_atom a ∧ a ≤ b) ↔
    (∀ b : β, b = ⊥ ∨ ∃ (a : β), is_atom a ∧ a ≤ b),
  from ⟨λ ⟨p⟩, ⟨this.mp p⟩, λ ⟨p⟩, ⟨this.mpr p⟩⟩,
  apply f.to_equiv.forall_congr,
  simp_rw [rel_iso.coe_fn_to_equiv],
  intro b, apply or_congr,
  { rw [f.apply_eq_iff_eq_symm_apply, map_bot], },
  { split,
    { exact λ ⟨a, ha⟩, ⟨f a, ⟨(f.is_atom_iff a).mpr ha.1, f.le_iff_le.mpr ha.2⟩⟩, },
    { rintros ⟨b, ⟨hb1, hb2⟩⟩,
      refine ⟨f.symm b, ⟨(f.symm.is_atom_iff b).mpr hb1, _⟩⟩,
      rwa [←f.le_iff_le, f.apply_symm_apply], }, },
end

lemma is_coatomic_iff [order_top α] {β : Type*} [order_top β] (f : α ≃o β) :
  is_coatomic α ↔ is_coatomic β :=
by { rw [←is_atomic_dual_iff_is_coatomic, ←is_atomic_dual_iff_is_coatomic],
  exact f.dual.is_atomic_iff }

end order_iso

section is_modular_lattice
variables [bounded_lattice α] [is_modular_lattice α]

namespace is_compl
variables {a b : α} (hc : is_compl a b)
include hc

lemma is_atom_iff_is_coatom : is_atom a ↔ is_coatom b :=
set.is_simple_lattice_Iic_iff_is_atom.symm.trans $ hc.Iic_order_iso_Ici.is_simple_lattice_iff.trans
  set.is_simple_lattice_Ici_iff_is_coatom

lemma is_coatom_iff_is_atom : is_coatom a ↔ is_atom b := hc.symm.is_atom_iff_is_coatom.symm

end is_compl

variables [is_complemented α]

lemma is_coatomic_of_is_atomic_of_is_complemented_of_is_modular [is_atomic α] : is_coatomic α :=
⟨λ x, begin
  rcases exists_is_compl x with ⟨y, xy⟩,
  apply (eq_bot_or_exists_atom_le y).imp _ _,
  { rintro rfl,
    exact eq_top_of_is_compl_bot xy },
  { rintro ⟨a, ha, ay⟩,
    rcases exists_is_compl (xy.symm.Iic_order_iso_Ici ⟨a, ay⟩) with ⟨⟨b, xb⟩, hb⟩,
    refine ⟨↑(⟨b, xb⟩ : set.Ici x), is_coatom.of_is_coatom_coe_Ici _, xb⟩,
    rw [← hb.is_atom_iff_is_coatom, order_iso.is_atom_iff],
    apply ha.Iic }
end⟩

lemma is_atomic_of_is_coatomic_of_is_complemented_of_is_modular [is_coatomic α] : is_atomic α :=
is_coatomic_dual_iff_is_atomic.1 is_coatomic_of_is_atomic_of_is_complemented_of_is_modular

theorem is_atomic_iff_is_coatomic : is_atomic α ↔ is_coatomic α :=
⟨λ h, @is_coatomic_of_is_atomic_of_is_complemented_of_is_modular _ _ _ _ h,
  λ h, @is_atomic_of_is_coatomic_of_is_complemented_of_is_modular _ _ _ _ h⟩

end is_modular_lattice
