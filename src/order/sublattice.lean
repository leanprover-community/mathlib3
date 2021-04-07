/-
Copyright (c) 2020 Matúš Behun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matúš Behun
-/

import order.lattice

variables { L : Type* } [ lattice L ] { s : set L }

structure sublattice ( L : Type* ) [ lattice L ] :=
  ( carrier : set L)
  ( inf_mem'  {a b : L} : a ∈ carrier → b ∈ carrier → a ⊓ b ∈ carrier )
  ( sup_mem'  {a b : L} : a ∈ carrier → b ∈ carrier → a ⊔ b ∈ carrier )

namespace sublattice

instance : has_coe (sublattice L) (set L) := ⟨sublattice.carrier⟩

instance : has_mem L (sublattice L) := ⟨ λ m S, m ∈ ( S : set L) ⟩

instance : has_coe_to_sort (set L) := ⟨_, λ s, {x // x ∈ s}⟩

@[simp]
lemma mem_carrier {SL : sublattice L} {x : L} : x ∈ SL.carrier ↔ x ∈ SL := iff.rfl

@[simp, norm_cast]
lemma mem_coe {SL : sublattice L} {x : L} : x ∈ (SL : set L) ↔ x ∈ SL := iff.rfl

@[simp, norm_cast]
lemma coe_coe (SL : sublattice L) : ↥(SL : set L) = SL := rfl

@[simp] theorem set_coe.exists {S : set L} {p : S → Prop} :
  (∃ x : S, p x) ↔ (∃ x (h : x ∈ S), p ⟨x, h⟩) :=
subtype.exists

@[simp] theorem set_coe.forall {S : set L} {p : S → Prop} :
  (∀ x : S, p x) ↔ (∀ x (h : x ∈ S), p ⟨x, h⟩) :=
subtype.forall

protected lemma sublattice.exists {SL : sublattice L} {p : SL → Prop} :
  (∃ x : SL, p x) ↔ ∃ x ∈ SL, p ⟨x, ‹x ∈ SL›⟩
:=
  set_coe.exists

protected lemma sublattice.forall {SL : sublattice L} {p : SL → Prop} :
  (∀ x : SL, p x) ↔ ∀ x ∈ SL, p ⟨x, ‹x ∈ SL›⟩
:=
  set_coe.forall

@[ext]
theorem ext' ⦃ A B : sublattice L ⦄ (h : (A : set L) = B) :
  A = B
:=
  by cases A; cases B; congr'


/- TODO haven't figure it out -/
/-
@[ext]
theorem ext {A B : sublattice L} (h : ∀ x, x ∈ A ↔ x ∈ B)
:
  A = B
:=
-/

def copy (SL : sublattice L) (S : set L) (hs : S = SL) :
  sublattice L
:=
  {
    carrier := S,
    inf_mem' := hs.symm ▸ SL.inf_mem',
    sup_mem' := hs.symm ▸ SL.sup_mem'
  }

variables { SL : sublattice L }

lemma coe_copy {B : sublattice L} {A : set L} (hs : A = SL) :
  (SL.copy A hs : set L) = A
:=
  rfl

lemma copy_eq {s : set L} (hs : s = SL) :
  SL.copy s hs = SL
:=
  ext' hs

theorem inf_mem {a b : L} :
  a ∈ SL → b ∈ SL → a ⊓ b ∈ SL
:=
  sublattice.inf_mem' SL

theorem sup_mem {a b : L} :
  a ∈ SL → b ∈ SL → a ⊔ b ∈ SL
:=
  sublattice.sup_mem' SL

open function

protected def function.injective.lattice { L : Type* } { β : Type*}
  [ has_inf β ] [ has_sup β ] [ lattice L ]
  (f : β → L )
  (hf: injective f)
  (inf : ∀ a b, f(a ⊓ b) = f(a) ⊓ f(b) )
  (sup : ∀ a b, f(a ⊔ b) = f(a) ⊔ f(b) )
:
  lattice L
:= {
    le           := ( ≤ ),
    le_refl      := λ x, le_refl x,
    le_trans     := λ x y z, le_trans,
    le_antisymm  := λ x y, le_antisymm,
    le_sup_left  := λ x y, le_sup_left,
    le_sup_right := λ x y, le_sup_right,

    sup          := ( ⊔ ),
    sup_le       := λ x y z, sup_le,

    inf          := ( ⊓ ),
    inf_le_left  := λ x y, inf_le_left,
    inf_le_right := λ x y, inf_le_right,
    le_inf       := λ x y z, le_inf
}

end sublattice
