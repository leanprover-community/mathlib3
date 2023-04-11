/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import order.game_add
import order.rel_iso.set
import set_theory.zfc.basic

/-!
# Von Neumann ordinals

This file develops the theory of von Neumann ordinals: transitive sets, well-ordered under `∈`.

## Definitions

- `Set.is_transitive`: every element of a set is a subset.
- `Set.is_ordinal`: a set is transitive, and transitive under `∈`.

## Main results

- `Set.is_ordinal_iff_well_founded`: proves our simple characterization of von Neumann sets to be
  equivalent with the usual characterization.

## Todo

- Define the basic arithmetic operations on ordinals from a purely set-theoretic perspective.
- Prove the equivalences between these definitions and those provided in
  `set_theory/ordinal/arithmetic.lean`.
-/

universe u

variables {x y z w : Set.{u}}

local attribute [simp] subtype.coe_inj

namespace Set

open relation

/-! ### Transitive sets -/

/-- A transitive set is one where every element is a subset. -/
def is_transitive (x : Set) : Prop := ∀ y ∈ x, y ⊆ x

@[simp] theorem empty_is_transitive : is_transitive ∅ := λ y hy, (not_mem_empty y hy).elim

theorem is_transitive.subset_of_mem (h : x.is_transitive) : y ∈ x → y ⊆ x := h y

theorem is_transitive_iff_mem_trans : z.is_transitive ↔ ∀ {x y : Set}, x ∈ y → y ∈ z → x ∈ z :=
⟨λ h x y hx hy, h.subset_of_mem hy hx, λ H x hx y hy, H hy hx⟩

alias is_transitive_iff_mem_trans ↔ is_transitive.mem_trans _

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

protected theorem is_transitive.union (hx : x.is_transitive) (hy : y.is_transitive) :
  (x ∪ y).is_transitive :=
begin
  rw ←sUnion_pair,
  apply is_transitive.sUnion' (λ z, _),
  rw mem_pair,
  rintro (rfl | rfl),
  assumption'
end

protected theorem is_transitive.powerset (h : x.is_transitive) : (powerset x).is_transitive :=
λ y hy z hz, by { rw mem_powerset at ⊢ hy, exact h.subset_of_mem (hy hz) }

theorem is_transitive_iff_sUnion_subset : x.is_transitive ↔ ⋃₀ x ⊆ x :=
⟨λ h y hy, by { rcases mem_sUnion.1 hy with ⟨z, hz, hz'⟩, exact h.mem_trans hz' hz },
  λ H y hy z hz, H $ mem_sUnion_of_mem hz hy⟩

alias is_transitive_iff_sUnion_subset ↔ is_transitive.sUnion_subset _

theorem is_transitive_iff_subset_powerset : x.is_transitive ↔ x ⊆ powerset x :=
⟨λ h y hy, mem_powerset.2 $ h.subset_of_mem hy, λ H y hy z hz, mem_powerset.1 (H hy) hz⟩

alias is_transitive_iff_subset_powerset ↔ is_transitive.subset_powerset _

/-! ### Ordinals as sets -/

/-- A set `x` is a von Neumann ordinal when it's a transitive set, that's transitive under `∈`.

There are many equivalences to this definition, which we aim to state and prove. These include:

- A transitive set of transitive sets (`is_ordinal_iff_transitive_mem_transitive`).
- A transitive set that's trichotomous under `∈`.
- A transitive set that's (strictly) totally ordered under `∈`
  (`is_ordinal_iff_is_strict_total_order`).
- A transitive set that's well-ordered under `∈` (`is_ordinal_iff_is_well_order`).
-/
def is_ordinal (x : Set) : Prop := x.is_transitive ∧ ∀ y z w : Set, y ∈ z → z ∈ w → w ∈ x → y ∈ w

namespace is_ordinal

protected theorem is_transitive (h : x.is_ordinal) : x.is_transitive := h.1

theorem subset_of_mem (h : x.is_ordinal) : y ∈ x → y ⊆ x := h.is_transitive.subset_of_mem

theorem mem_trans (h : z.is_ordinal) : x ∈ y → y ∈ z → x ∈ z := h.is_transitive.mem_trans

theorem mem_trans' (hx : x.is_ordinal) : y ∈ z → z ∈ w → w ∈ x → y ∈ w := hx.2 y z w

protected theorem sUnion (H : ∀ y ∈ x, is_ordinal y) : (⋃₀ x).is_ordinal :=
begin
  refine ⟨is_transitive.sUnion' $ λ y hy, (H y hy).is_transitive, λ y z w hyz hzw hwx, _⟩,
  { rcases mem_sUnion.1 hwx with ⟨v, hvx, hwv⟩,
    exact (H v hvx).mem_trans' hyz hzw hwv }
end

protected theorem union (hx : x.is_ordinal) (hy : y.is_ordinal) : (x ∪ y).is_ordinal :=
is_ordinal.sUnion $ λ z hz, by { rcases mem_pair.1 hz with rfl | rfl, assumption' }

protected theorem inter (hx : x.is_ordinal) (hy : y.is_ordinal) : (x ∩ y).is_ordinal :=
⟨hx.is_transitive.inter hy.is_transitive, λ z w v hzw hwv hv,
  hx.mem_trans' hzw hwv (mem_inter.1 hv).1⟩

protected theorem is_trans (h : x.is_ordinal) : is_trans x.to_set (subrel (∈) _) :=
⟨λ a b c hab hbc, h.mem_trans' hab hbc c.2⟩

theorem _root_.Set.is_ordinal_iff_is_trans : x.is_ordinal ↔
  x.is_transitive ∧ is_trans x.to_set (subrel (∈) _) :=
⟨λ h, ⟨h.is_transitive, h.is_trans⟩, λ ⟨h₁, ⟨h₂⟩⟩, ⟨h₁, λ y z w hyz hzw hwx,
  let hzx := h₁.mem_trans hzw hwx in h₂ ⟨y, h₁.mem_trans hyz hzx⟩ ⟨z, hzx⟩ ⟨w, hwx⟩ hyz hzw⟩⟩

/-- A relation embedding between a smaller and a larger ordinal. -/
protected def rel_embedding (hx : x.is_ordinal) (hy : y ∈ x) :
  subrel (∈) y.to_set ↪r subrel (∈) x.to_set :=
⟨⟨λ b, ⟨b.1, hx.subset_of_mem hy b.2⟩, λ a b, by simp⟩, λ a b, by simp⟩

protected theorem mem (hx : x.is_ordinal) (hy : y ∈ x) : y.is_ordinal :=
begin
  haveI := hx.is_trans,
  exact is_ordinal_iff_is_trans.2 ⟨λ z hz a ha, hx.mem_trans' ha hz hy,
    (hx.rel_embedding hy).is_trans⟩
end

end is_ordinal

theorem is_ordinal_of_transitive_of_mem_transitive (hx : x.is_transitive)
  (H : ∀ y : Set, y ∈ x → y.is_transitive) : x.is_ordinal :=
⟨hx, λ y z w hyz hzw hwx, (H w hwx).subset_of_mem hzw hyz⟩

theorem is_ordinal_iff_transitive_mem_transitive :
  x.is_ordinal ↔ x.is_transitive ∧ ∀ y : Set, y ∈ x → y.is_transitive :=
⟨λ hx, ⟨hx.is_transitive, λ y hy, (hx.mem hy).is_transitive⟩,
  λ ⟨hx, H⟩, is_ordinal_of_transitive_of_mem_transitive hx H⟩

theorem is_ordinal_of_subset_ordinal (hx : x.is_transitive) (hy : y.is_ordinal) (hxy : x ⊆ y) :
  x.is_ordinal :=
⟨hx, λ a b c hab hbc hcx, hy.mem_trans' hab hbc (hxy hcx)⟩

theorem is_transitive.subset_of_eq_or_mem (h : y.is_transitive) : x = y ∨ x ∈ y → x ⊆ y :=
begin
  rintro (rfl | hx),
  { exact subset_rfl },
  { exact h.subset_of_mem hx }
end

namespace is_ordinal

theorem subset_of_eq_or_mem (h : y.is_ordinal) : x = y ∨ x ∈ y → x ⊆ y :=
h.is_transitive.subset_of_eq_or_mem

theorem subset_iff_eq_or_mem' (hx : x.is_transitive) (hy : y.is_ordinal) : x ⊆ y ↔ x = y ∨ x ∈ y :=
⟨begin
  revert hx hy,
  apply sym2.game_add.induction mem_wf _ x y,
  intros x y IH hx hy hxy,
  by_cases hyx : y ⊆ x,
  { exact or.inl (subset_antisymm hxy hyx) },
  obtain ⟨m, hm, hm'⟩ := mem_wf.has_min (y.to_set \ x.to_set) (set.nonempty_diff.2 hyx),
  have hmy : m ∈ y := set.mem_of_mem_diff hm,
  have hmx : m ⊆ x,
  { intros z hzm,
    by_contra hzx,
    exact hm' _ ⟨hy.mem_trans hzm hmy, hzx⟩ hzm },
    cases IH m x (sym2.game_add.fst_snd hmy)
      (hy.mem hmy).is_transitive (is_ordinal_of_subset_ordinal hx hy hxy) hmx with H H,
  { right, rwa ←H },
  { exact (set.not_mem_of_mem_diff hm H).elim }
end, hy.subset_of_eq_or_mem⟩

theorem subset_iff_eq_or_mem (hx : x.is_ordinal) (hy : y.is_ordinal) : x ⊆ y ↔ x = y ∨ x ∈ y :=
subset_iff_eq_or_mem' hx.is_transitive hy

alias subset_iff_eq_or_mem' ↔ eq_or_mem_of_subset' _
alias subset_iff_eq_or_mem ↔ eq_or_mem_of_subset _

theorem mem_of_subset_of_mem (h : x.is_ordinal) (hz : z.is_ordinal) (hx : x ⊆ y) (hy : y ∈ z) :
  x ∈ z :=
begin
  rcases h.eq_or_mem_of_subset (hz.mem hy) hx with rfl | hx,
  { exact hy },
  { exact hz.mem_trans hx hy }
end

theorem not_mem_iff_subset (hx : x.is_ordinal) (hy : y.is_ordinal) : x ∉ y ↔ y ⊆ x :=
⟨begin
  revert hx hy,
  apply sym2.game_add.induction mem_wf _ x y,
  intros x y IH hx hy hyx z hzy,
  by_contra hzx,
  refine hyx (mem_of_subset_of_mem hx hy (IH z x _ (hy.mem hzy) hx hzx) hzy),
  exact sym2.game_add.fst_snd hzy,
end, λ hxy hyx, mem_irrefl _ (hxy hyx)⟩

theorem not_subset_iff_mem (hx : x.is_ordinal) (hy : y.is_ordinal) : ¬ x ⊆ y ↔ y ∈ x :=
by rw [not_iff_comm, not_mem_iff_subset hy hx]

theorem mem_iff_subset_not_subset (hx : x.is_ordinal) (hy : y.is_ordinal) :
  x ∈ y ↔ x ⊆ y ∧ ¬ y ⊆ x :=
by { rw [not_subset_iff_mem hy hx, iff_and_self], exact hy.subset_of_mem }

theorem mem_or_subset (hx : x.is_ordinal) (hy : y.is_ordinal) : x ∈ y ∨ y ⊆ x :=
or_iff_not_imp_left.2 (not_mem_iff_subset hx hy).1

theorem subset_total (hx : x.is_ordinal) (hy : y.is_ordinal) : x ⊆ y ∨ y ⊆ x :=
begin
  cases mem_or_subset hx hy,
  { exact or.inl (hy.subset_of_mem h) },
  { exact or.inr h }
end

theorem mem_trichotomous (hx : x.is_ordinal) (hy : y.is_ordinal) : x ∈ y ∨ x = y ∨ y ∈ x :=
by { rw [eq_comm, ←subset_iff_eq_or_mem hy hx], exact mem_or_subset hx hy }

protected theorem is_trichotomous (h : x.is_ordinal) : is_trichotomous x.to_set (subrel (∈) _) :=
⟨λ ⟨a, ha⟩ ⟨b, hb⟩, by simpa using mem_trichotomous (h.mem ha) (h.mem hb)⟩

protected theorem is_well_order (h : x.is_ordinal) : is_well_order x.to_set (subrel (∈) _) :=
{ wf := (subrel.rel_embedding _ _).well_founded mem_wf,
  ..h.is_trans, ..h.is_trichotomous }

protected theorem is_strict_total_order (h : x.is_ordinal) :
  is_strict_total_order x.to_set (subrel (∈) _) :=
{ ..h.is_well_order }

end is_ordinal

theorem is_ordinal_iff_is_strict_total_order : x.is_ordinal ↔
  x.is_transitive ∧ is_strict_total_order x.to_set (subrel (∈) _) :=
⟨λ h, ⟨h.is_transitive, h.is_strict_total_order⟩, λ ⟨h₁, h₂⟩, is_ordinal_iff_is_trans.2 ⟨h₁,
  by { haveI := h₂, exact by apply_instance }⟩⟩

/-- Our definition of von Neumann ordinals is equivalent to the standard one. -/
theorem is_ordinal_iff_is_well_order : x.is_ordinal ↔
  x.is_transitive ∧ is_well_order x.to_set (subrel (∈) _) :=
⟨λ h, ⟨h.is_transitive, h.is_well_order⟩, λ ⟨h₁, h₂⟩, is_ordinal_iff_is_trans.2 ⟨h₁,
  by { haveI := h₂, exact by apply_instance }⟩⟩

theorem is_transitive.is_ordinal (h : x.is_transitive) (H : ∀ y ∈ x, is_ordinal y) : x.is_ordinal :=
⟨h, λ y z w hyz hzw hwx, (H w hwx).mem_trans hyz hzw⟩

@[simp] theorem empty_is_ordinal : is_ordinal ∅ :=
⟨empty_is_transitive, λ y z w _ _ H, (not_mem_empty w H).elim⟩

end Set
