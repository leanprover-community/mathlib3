/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import order.rel_iso.set
import set_theory.zfc.basic

/-!
# Von Neumann ordinals

This file works towards the development of von Neumann ordinals, i.e. transitive sets, well-ordered
under `∈`. We currently only have an initial development of transitive sets.

Further development can be found on the branch `von_neumann_v2`.

## Definitions

- `Set.is_transitive`: every element of a set is a subset.
- `Set.is_ordinal`: a set is hereditarily transitive.

## Todo

- Define the basic arithmetic operations on ordinals from a purely set-theoretic perspective.
- Prove the equivalences between these definitions and those provided in
  `set_theory/ordinal/arithmetic.lean`.
-/

universe u

variables {x y z w : Set.{u}}

local attribute [simp] subtype.coe_inj

namespace Set

/-! ### Transitive sets -/

/-- A transitive set is one where every element is a subset. -/
def is_transitive (x : Set) : Prop := ∀ y ∈ x, y ⊆ x

@[simp] theorem empty_is_transitive : is_transitive ∅ := λ y hy, (not_mem_empty y hy).elim

theorem is_transitive.subset_of_mem (h : x.is_transitive) : y ∈ x → y ⊆ x := h y

theorem is_transitive_iff_mem_trans : z.is_transitive ↔ ∀ ⦃x y : Set⦄, x ∈ y → y ∈ z → x ∈ z :=
⟨λ h x y hx hy, h.subset_of_mem hy hx, λ H x hx y hy, H hy hx⟩

theorem is_transitive.mem_trans (h : z.is_transitive) : ∀ {x y : Set}, x ∈ y → y ∈ z → x ∈ z :=
is_transitive_iff_mem_trans.mp h

protected theorem is_transitive.inter (hx : x.is_transitive) (hy : y.is_transitive) :
  (x ∩ y).is_transitive :=
λ z hz w hw, by { rw mem_inter at hz ⊢, exact ⟨hx.mem_trans hw hz.1, hy.mem_trans hw hz.2⟩ }

protected theorem is_transitive.sUnion (h : x.is_transitive) : (⋃₀ x).is_transitive :=
λ y hy z hz, begin
  rcases mem_sUnion.1 hy with ⟨w, hw, hw'⟩,
  exact mem_sUnion_of_mem hz (h.mem_trans hw' hw)
end

theorem is_transitive.sUnion' (H : ∀ y ∈ x, is_transitive y) : (⋃₀ x).is_transitive :=
λ y hy z hz, begin
  rcases mem_sUnion.1 hy with ⟨w, hw, hw'⟩,
  exact mem_sUnion_of_mem ((H w hw).mem_trans hz hw') hw
end

theorem is_transitive_iff_sUnion_subset : x.is_transitive ↔ ⋃₀ x ⊆ x :=
⟨λ h y hy, by { rcases mem_sUnion.1 hy with ⟨z, hz, hz'⟩, exact h.mem_trans hz' hz },
  λ H y hy z hz, H $ mem_sUnion_of_mem hz hy⟩

alias is_transitive_iff_sUnion_subset ↔ is_transitive.sUnion_subset _

theorem is_transitive_iff_subset_powerset : x.is_transitive ↔ x ⊆ powerset x :=
⟨λ h y hy, mem_powerset.2 $ h.subset_of_mem hy, λ H y hy z hz, mem_powerset.1 (H hy) hz⟩

alias is_transitive_iff_subset_powerset ↔ is_transitive.subset_powerset _

/-! ### Ordinals as sets -/

/-- A set `x` is a von Neumann ordinal when it's a hereditarily transitive set. We prove that this
further implies that `x` is well-ordered under `∈`. -/
def is_ordinal (x : Set) : Prop := x.hereditarily is_transitive

theorem is_ordinal_iff {x : Set} : x.is_ordinal ↔ x.is_transitive ∧ ∀ y ∈ x, is_ordinal y :=
hereditarily_iff

alias is_ordinal_iff ↔ is_ordinal.def _

namespace is_ordinal

protected theorem is_transitive (h : x.is_ordinal) : x.is_transitive := h.self

protected lemma mem (h : x.is_ordinal) (hy : y ∈ x) : is_ordinal y := h.mem hy

theorem subset_of_mem (h : x.is_ordinal) : y ∈ x → y ⊆ x := h.is_transitive.subset_of_mem

theorem mem_trans (h : z.is_ordinal) : x ∈ y → y ∈ z → x ∈ z := h.is_transitive.mem_trans

theorem mem_trans' (h : x.is_ordinal) (hw : w ∈ x) : y ∈ z → z ∈ w → y ∈ w := (h.mem hw).mem_trans

protected theorem sUnion' (H : ∀ y ∈ x, is_ordinal y) : (⋃₀ x).is_ordinal :=
begin
  refine is_ordinal_iff.mpr ⟨is_transitive.sUnion' $ λ y hy, (H y hy).is_transitive, λ y hy, _⟩,
  obtain ⟨w, hw, hy⟩ := mem_sUnion.1 hy,
  exact (H _ hw).mem hy,
end

protected theorem sUnion (H : is_ordinal x) : (⋃₀ x).is_ordinal :=
is_ordinal.sUnion' (λ y hy, H.mem hy)

protected theorem sUnion_subset (H : is_ordinal x) : ⋃₀ x ⊆ x :=
λ y hy, let ⟨z, hz, hyz⟩ := mem_sUnion.mp hy in H.mem_trans hyz hz

protected theorem union (hx : x.is_ordinal) (hy : y.is_ordinal) : (x ∪ y).is_ordinal :=
is_ordinal.sUnion' $ λ z hz, by { rcases mem_pair.1 hz with rfl | rfl; assumption }

protected theorem inter (hx : x.is_ordinal) (hy : y.is_ordinal) : (x ∩ y).is_ordinal :=
is_ordinal_iff.mpr ⟨hx.is_transitive.inter hy.is_transitive, λ z hz, hx.mem (mem_inter.mp hz).1⟩

protected theorem is_trans (h : x.is_ordinal) : is_trans x.to_set (subrel (∈) _) :=
⟨λ a b c, h.mem_trans' c.2⟩

theorem _root_.Set.is_ordinal_iff_mem_is_transitive (x : Set) :
  x.is_ordinal ↔ x.is_transitive ∧ ∀ y ∈ x, is_transitive y :=
⟨λ h, ⟨h.is_transitive, λ y hy, (h.mem hy).is_transitive⟩, Set.induction_on x (λ x ih ⟨h₁, h₂⟩,
  is_ordinal_iff.mpr ⟨h₁, λ y hy, ih _ hy ⟨h₂ _ hy, λ z hz, h₂ _ (h₁.mem_trans hz hy)⟩⟩)⟩

theorem _root_.Set.is_ordinal_iff_mem_trans (x : Set) :
  x.is_ordinal ↔ x.is_transitive ∧ ∀ y z w : Set, w ∈ x → y ∈ z → z ∈ w → y ∈ w :=
⟨λ h, ⟨h.is_transitive, λ _ _ _, h.mem_trans'⟩, λ ⟨h₁, h₂⟩, x.is_ordinal_iff_mem_is_transitive.mpr
  ⟨h₁, λ c hc, is_transitive_iff_mem_trans.mpr $ λ a b hab hbc, h₂ _ _ _ hc hab hbc⟩⟩

theorem _root_.Set.is_ordinal_iff_is_trans : x.is_ordinal ↔
  x.is_transitive ∧ is_trans x.to_set (subrel (∈) _) :=
⟨λ h, ⟨h.is_transitive, h.is_trans⟩, λ ⟨h₁, ⟨h₂⟩⟩, x.is_ordinal_iff_mem_trans.mpr
  ⟨h₁, λ y z w hwx hyz hzw, let hzx := h₁.mem_trans hzw hwx in
    h₂ ⟨y, h₁.mem_trans hyz hzx⟩ ⟨z, hzx⟩ ⟨w, hwx⟩ hyz hzw⟩⟩

/-- A relation embedding between a smaller and a larger ordinal. -/
protected def rel_embedding (hx : x.is_ordinal) (hy : y ∈ x) :
  subrel (∈) y.to_set ↪r subrel (∈) x.to_set :=
⟨⟨λ b, ⟨b.1, hx.subset_of_mem hy b.2⟩, λ a b, by simp⟩, λ a b, by simp⟩

end is_ordinal

end Set
