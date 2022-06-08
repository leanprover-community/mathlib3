/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yury G. Kudryashov
-/
import topology.constructions

/-!
# Inseparable points

In this file we require two relations on a topological space: `specializes` (notation : `x ⤳ y`) and
`inseparable`, then prove some basic lemmas about these relations.

## Main definitions

* `specializes` : `specializes x y` (`x ⤳ y`) means that `x` specializes to `y`, i.e.
  `y` is in the closure of `x`.

* `specialization_preorder` : specialization gives a preorder on a topological space. In case of a
  T₀ space, this preorder is a partial order, see `specialization_order`.

* `inseparable x y` means that two points can't be separated by an open set.
-/

open_locale topological_space
open set

variables {X Y : Type*} [topological_space X] [topological_space Y] {x y z : X}

/-- `x` specializes to `y` if `y` is in the closure of `x`. The notation used is `x ⤳ y`. -/
def specializes (x y : X) : Prop := y ∈ closure ({x} : set X)

infix ` ⤳ `:300 := specializes

lemma specializes_iff_mem_closure {x y : X} : x ⤳ y ↔ y ∈ closure ({x} : set X) := iff.rfl

lemma specializes_iff_closure_subset : x ⤳ y ↔ closure ({y} : set X) ⊆ closure ({x} : set X) :=
is_closed_closure.mem_iff_closure_subset

lemma specializes_rfl : x ⤳ x := subset_closure (mem_singleton x)

lemma specializes_refl (x : X) : x ⤳ x := specializes_rfl

lemma specializes.trans : x ⤳ y → y ⤳ z → x ⤳ z :=
by { simp_rw specializes_iff_closure_subset, exact λ a b, b.trans a }

lemma specializes_iff_forall_closed :
  x ⤳ y ↔ ∀ (Z : set X) (h : is_closed Z), x ∈ Z → y ∈ Z :=
begin
  split,
  { intros h Z hZ,
    rw [hZ.mem_iff_closure_subset, hZ.mem_iff_closure_subset],
    exact (specializes_iff_closure_subset.mp h).trans },
  { intro h, exact h _ is_closed_closure (subset_closure $ set.mem_singleton x) }
end

lemma specializes_iff_forall_open :
  x ⤳ y ↔ ∀ (U : set X) (h : is_open U), y ∈ U → x ∈ U :=
begin
  rw specializes_iff_forall_closed,
  exact ⟨λ h U hU, not_imp_not.mp (h _ (is_closed_compl_iff.mpr hU)),
    λ h U hU, not_imp_not.mp (h _ (is_open_compl_iff.mpr hU))⟩,
end

lemma specializes.mem_open (h : x ⤳ y) {U : set X} (hU : is_open U) (hy : y ∈ U) : x ∈ U :=
specializes_iff_forall_open.1 h U hU hy

lemma specializes.map (h : x ⤳ y) {f : X → Y} (hf : continuous f) : f x ⤳ f y :=
begin
  rw [specializes, ← set.image_singleton],
  exact image_closure_subset_closure_image hf ⟨_, h, rfl⟩,
end

section specialize_order

variable (X)

/-- Specialization forms a preorder on the topological space. -/
def specialization_preorder : preorder X :=
{ le := λ x y, y ⤳ x,
  le_refl := λ x, specializes_refl x,
  le_trans := λ _ _ _ h₁ h₂, specializes.trans h₂ h₁ }

local attribute [instance] specialization_preorder

variable {X}

lemma specialization_order.monotone_of_continuous (f : X → Y) (hf : continuous f) : monotone f :=
λ x y h, specializes.map h hf

end specialize_order

/-- Two points are topologically inseparable if no open set separates them. -/
def inseparable (x y : X) : Prop := ∀ (U : set X) (hU : is_open U), x ∈ U ↔ y ∈ U

lemma inseparable_iff_nhds_eq : inseparable x y ↔ 𝓝 x = 𝓝 y :=
⟨λ h, by simp only [nhds_def', h _] { contextual := tt },
  λ h U hU, by simp only [← hU.mem_nhds_iff, h]⟩

alias inseparable_iff_nhds_eq ↔ inseparable.nhds_eq _

lemma inseparable.map {f : X → Y} (h : inseparable x y) (hf : continuous f) :
  inseparable (f x) (f y) :=
λ U hU, h (f ⁻¹' U) (hU.preimage hf)

lemma inseparable_iff_closed :
  inseparable x y ↔ ∀ (U : set X) (hU : is_closed U), x ∈ U ↔ y ∈ U :=
⟨λ h U hU, not_iff_not.mp (h _ hU.1), λ h U hU, not_iff_not.mp (h _ (is_closed_compl_iff.mpr hU))⟩

lemma inseparable_iff_mem_closure (x y : X) :
  inseparable x y ↔ x ∈ closure ({y} : set X) ∧ y ∈ closure ({x} : set X) :=
begin
  rw inseparable_iff_closed,
  exact ⟨λ h, ⟨(h _ is_closed_closure).mpr (subset_closure $ set.mem_singleton y),
      (h _ is_closed_closure).mp (subset_closure $ set.mem_singleton x)⟩,
    λ h U hU, ⟨λ hx, (is_closed.closure_subset_iff hU).mpr (set.singleton_subset_iff.mpr hx) h.2,
      λ hy, (is_closed.closure_subset_iff hU).mpr (set.singleton_subset_iff.mpr hy) h.1⟩⟩
end

lemma inseparable_iff_specializes_and (x y : X) :
  inseparable x y ↔ x ⤳ y ∧ y ⤳ x :=
(inseparable_iff_mem_closure x y).trans (and_comm _ _)

lemma inseparable_iff_closure_eq {x y : X} :
  inseparable x y ↔ (closure {x} : set X) = closure {y} :=
by simp only [inseparable_iff_specializes_and, specializes_iff_closure_subset,
  subset_antisymm_iff, and.comm]

lemma subtype_inseparable_iff {U : set X} (x y : U) :
  inseparable x y ↔ inseparable (x : X) y :=
by { simp_rw [inseparable_iff_mem_closure, closure_subtype, image_singleton] }
