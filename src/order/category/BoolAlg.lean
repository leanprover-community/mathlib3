/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.fintype.order
import order.atoms
import order.category.BoundedDistribLattice
import order.hom.complete_lattice

/-!
# The category of boolean algebras

This defines `BoolAlg`, the category of boolean algebras.
-/

open order_dual opposite set

--TODO@Yaël: Once we have Heyting algebras, we won't need to go through `boolean_algebra.of_core`
instance {α : Type*} [boolean_algebra α] : boolean_algebra (order_dual α) :=
boolean_algebra.of_core
{ compl := λ a, to_dual (of_dual a)ᶜ,
  inf_compl_le_bot := λ _, sup_compl_eq_top.ge,
  top_le_sup_compl := λ _, inf_compl_eq_bot.ge,
  ..order_dual.distrib_lattice α, ..order_dual.bounded_order α }

/-- `set.preimage` as a bounded lattice homomorphism. -/
def bounded_lattice_hom.set_preimage {α β : Type*} (f : α → β) :
  bounded_lattice_hom (set β) (set α) :=
{ to_fun := set.preimage f,
  map_sup' := λ s t, set.preimage_union,
  map_inf' := λ s t, set.preimage_inter,
  map_top' := set.preimage_univ,
  map_bot' := set.preimage_empty }

@[simp] lemma preimage_sInter {α β : Type*} {f : α → β} {s : set (set β)} :
  f ⁻¹' (⋂₀ s) = ⋂ t ∈ s, f ⁻¹' t :=
set.ext $ by simp only [set.preimage, set.mem_sInter, set.mem_set_of_eq, set.mem_Inter, iff_self,
  implies_true_iff]

/-- `set.preimage` as a complete lattice homomorphism. -/
def complete_lattice_hom.set_preimage {α β : Type*} (f : α → β) :
  complete_lattice_hom (set β) (set α) :=
{ to_fun := set.preimage f,
  map_Sup' := λ s, preimage_sUnion.trans $ by simp only [set.Sup_eq_sUnion, set.sUnion_image],
  map_Inf' := λ s, preimage_sInter.trans $ by simp only [set.Inf_eq_sInter, set.sInter_image] }

universes u

open category_theory

/-- The category of boolean algebras. -/
def BoolAlg := bundled boolean_algebra

namespace BoolAlg

instance : has_coe_to_sort BoolAlg Type* := bundled.has_coe_to_sort
instance (X : BoolAlg) : boolean_algebra X := X.str

/-- Construct a bundled `BoolAlg` from a `boolean_algebra`. -/
def of (α : Type*) [boolean_algebra α] : BoolAlg := bundled.of α

instance : inhabited BoolAlg := ⟨of punit⟩

/-- Turn a `BoolAlg` into a `BoundedDistribLattice` by forgetting its complement operation. -/
def to_BoundedDistribLattice (X : BoolAlg) : BoundedDistribLattice := BoundedDistribLattice.of X

instance : large_category.{u} BoolAlg := induced_category.category to_BoundedDistribLattice
instance : concrete_category BoolAlg := induced_category.concrete_category to_BoundedDistribLattice

instance has_forget_to_BoundedDistribLattice : has_forget₂ BoolAlg BoundedDistribLattice :=
induced_category.has_forget₂ to_BoundedDistribLattice

/-- Constructs an equivalence between boolean algebras from an order isomorphism
between them. -/
@[simps] def iso.mk {α β : BoolAlg.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := (e : bounded_lattice_hom α β),
  inv := (e.symm : bounded_lattice_hom β α),
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

/-- `order_dual` as a functor. -/
@[simps] def dual : BoolAlg ⥤ BoolAlg :=
{ obj := λ X, of (order_dual X), map := λ X Y, bounded_lattice_hom.dual }

/-- The equivalence between `NonemptyFinLinOrd` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : BoolAlg ≌ BoolAlg :=
equivalence.mk dual dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end BoolAlg

lemma BoolAlg_dual_comp_forget_to_BoundedDistribLattice :
  BoolAlg.dual ⋙ forget₂ BoolAlg BoundedDistribLattice =
    forget₂ BoolAlg BoundedDistribLattice ⋙ BoundedDistribLattice.dual := rfl

/-! ### Clopen sets -/

/-- The type of clopen sets of a topological space. -/
structure atom (α : Type*) [preorder α] [order_bot α] :=
(carrier : α)
(atom' : is_atom carrier)

namespace atom

lemma clopen (s : atom α) : is_clopen (s : set α) := s.clopen'

/-- Reinterpret a compact open as an open. -/
@[simps] def to_opens (s : atom α) : opens α := ⟨s, s.clopen.is_open⟩

@[ext] protected lemma ext {s t : atom α} (h : (s : set α) = t) : s = t := set_like.ext' h

@[simp] lemma coe_mk (s : set α) (h) : (mk s h : set α) = s := rfl

instance : has_sup (atom α) := ⟨λ s t, ⟨s ∪ t, s.clopen.union t.clopen⟩⟩
instance [t2_space α] : has_inf (atom α) := ⟨λ s t, ⟨s ∩ t, s.clopen.inter t.clopen⟩⟩
instance [compact_space α] : has_top (atom α) := ⟨⟨⊤, is_clopen_univ⟩⟩
instance : has_bot (atom α) := ⟨⟨⊥, is_clopen_empty⟩⟩

instance : semilattice_sup (atom α) := set_like.coe_injective.semilattice_sup _ (λ _ _, rfl)

instance [t2_space α] : distrib_lattice (atom α) :=
set_like.coe_injective.distrib_lattice _ (λ _ _, rfl) (λ _ _, rfl)

instance : order_bot (atom α) := order_bot.lift (coe : _ → set α) (λ _ _, id) rfl

instance [compact_space α] : bounded_order (atom α) :=
bounded_order.lift (coe : _ → set α) (λ _ _, id) rfl rfl

@[simp] lemma coe_sup (s t : atom α) : (↑(s ⊔ t) : set α) = s ∪ t := rfl
@[simp] lemma coe_inf [t2_space α] (s t : atom α) : (↑(s ⊓ t) : set α) = s ∩ t := rfl
@[simp] lemma coe_top [compact_space α] : (↑(⊤ : atom α) : set α) = univ := rfl
@[simp] lemma coe_bot : (↑(⊥ : atom α) : set α) = ∅ := rfl

instance : inhabited (atom α) := ⟨⊥⟩

end atom

/-- The powerset functor. `set` as a functor. -/
def Type_to_BoolAlg : Type* ⥤ BoolAlgᵒᵖ :=
{ obj := λ X, op $ BoolAlg.of (set X),
  map := λ X Y f, quiver.hom.op $ bounded_lattice_hom.set_preimage f }

/-- The atoms functor. `atom` as a functor. -/
def BoolAlg_to_Type : Type* ⥤ BoolAlgᵒᵖ :=
{ obj := λ X, op $ BoolAlg.of (set X),
  map := λ X Y f, quiver.hom.op $ bounded_lattice_hom.set_preimage f }
