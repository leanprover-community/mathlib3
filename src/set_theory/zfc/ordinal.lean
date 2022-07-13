/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import order.succ_pred.basic
import set_theory.zfc.basic
import logic.hydra

/-!
# Von Neumann ordinals

This file works towards the development of von Neumann ordinals, i.e. transitive sets, well-ordered
under `∈`. We currently only have an initial development of transitive sets.

Further development can be found on the branch `von_neumann_v2`.

## Definitions

- `Set.is_transitive` means that every element of a set is a subset.

## Todo

- Define von Neumann ordinals.
- Define the basic arithmetic operations on ordinals from a purely set-theoretic perspective.
- Prove the equivalences between these definitions and those provided in
  `set_theory/ordinal/arithmetic.lean`.
-/

universe u

variables {x y z w : Set.{u}}

open relation

namespace Set

/-! ### Transitive sets -/

/-- A transitive set is one where every element is a subset. -/
def is_transitive (x : Set) : Prop := ∀ y ∈ x, y ⊆ x

@[simp] theorem empty_is_transitive : is_transitive ∅ := λ y hy, (mem_empty y hy).elim

theorem is_transitive.subset_of_mem (h : x.is_transitive) : y ∈ x → y ⊆ x := h y

theorem is_transitive_iff_mem_trans : z.is_transitive ↔ ∀ {x y : Set}, x ∈ y → y ∈ z → x ∈ z :=
⟨λ h x y hx hy, h.subset_of_mem hy hx, λ H x hx y hy, H hy hx⟩

alias is_transitive_iff_mem_trans ↔ is_transitive.mem_trans _

theorem is_transitive.Union (h : x.is_transitive) : (⋃ x).is_transitive :=
λ y hy z hz, begin
  rcases mem_Union.1 hy with ⟨w, hw, hw'⟩,
  exact mem_Union_of_mem hz (h.mem_trans hw' hw)
end

theorem is_transitive_iff_Union_subset : x.is_transitive ↔ ⋃ x ⊆ x :=
⟨λ h y hy, by { rcases mem_Union.1 hy with ⟨z, hz, hz'⟩, exact h.mem_trans hz' hz },
  λ H y hy z hz, H $ mem_Union_of_mem hz hy⟩

alias is_transitive_iff_Union_subset ↔ is_transitive.Union_subset _

theorem is_transitive_iff_subset_powerset : x.is_transitive ↔ x ⊆ powerset x :=
⟨λ h y hy, mem_powerset.2 $ h.subset_of_mem hy, λ H y hy z hz, mem_powerset.1 (H hy) hz⟩

alias is_transitive_iff_subset_powerset ↔ is_transitive.subset_powerset _

/-! ### Ordinals -/

/-- A set `x` is a von Neumann ordinal when it's a transitive set, that's transitive under `∈`. We
prove that this further implies that `x` is well-ordered under `∈`. -/
def is_ordinal (x : Set) : Prop := x.is_transitive ∧ ∀ y z w : Set, y ∈ z → z ∈ w → w ∈ x → y ∈ w

namespace is_ordinal

protected theorem is_transitive (h : x.is_ordinal) : x.is_transitive := h.1

theorem subset_of_mem (h : x.is_ordinal) : y ∈ x → y ⊆ x := h.is_transitive.subset_of_mem

theorem mem_trans (h : z.is_ordinal) : x ∈ y → y ∈ z → x ∈ z := h.is_transitive.mem_trans

theorem mem_trans' (hx : x.is_ordinal) : y ∈ z → z ∈ w → w ∈ x → y ∈ w := hx.2 y z w

protected theorem is_trans (h : x.is_ordinal) : is_trans x.to_set (subrel (∈) _) :=
⟨λ a b c hab hbc, h.mem_trans' hab hbc c.2⟩

theorem _root_.is_ordinal_iff_is_trans : x.is_ordinal ↔
  x.is_transitive ∧ is_trans x.to_set (subrel (∈) _) :=
⟨λ h, ⟨h.is_transitive, h.is_trans⟩, λ ⟨h₁, ⟨h₂⟩⟩, ⟨h₁, λ y z w hyz hzw hwx,
  let hzx := h₁.mem_trans hzw hwx in h₂ ⟨y, h₁.mem_trans hyz hzx⟩ ⟨z, hzx⟩ ⟨w, hwx⟩ hyz hzw⟩⟩

/-- A relation embedding between a smaller and larger ordinal. -/
protected def rel_embedding (hx : x.is_ordinal) (hy : y ∈ x) :
  subrel (∈) y.to_set ↪r subrel (∈) x.to_set :=
⟨⟨λ b, ⟨b.1, hx.subset_of_mem hy b.2⟩, λ a b, by simp [subtype.coe_inj]⟩, λ a b, by simp⟩

protected theorem mem (hx : x.is_ordinal) (hy : y ∈ x) : y.is_ordinal :=
begin
  haveI := hx.is_trans,
  exact is_ordinal_iff_is_trans.2 ⟨λ z hz a ha, hx.mem_trans' ha hz hy,
    (hx.rel_embedding hy).is_trans⟩
end

theorem subset_of_eq_or_mem (h : y.is_ordinal) : x = y ∨ x ∈ y → x ⊆ y :=
begin
  rintro (rfl | hx),
  { exact subset_rfl },
  { exact h.subset_of_mem hx }
end

theorem subset_iff_eq_or_mem (hx : x.is_ordinal) (hy : y.is_ordinal) : x ⊆ y ↔ x = y ∨ x ∈ y :=
⟨begin
  revert hx hy,
  apply game_add_swap.induction mem_wf _ x y,
  intros x y IH hx hy hxy,
  by_cases hyx : y ⊆ x,
  { exact or.inl (subset_antisymm hxy hyx) },
  let m := mem_wf.min (y.to_set \ x.to_set) (set.nonempty_diff.2 hyx),
  have hm : m ∈ y.to_set \ x.to_set := mem_wf.min_mem _ _,
  have hmy : m ∈ y := set.mem_of_mem_diff hm,
  have hmx : m ⊆ x,
  { intros z hzm,
    by_contra hzx,
    exact mem_wf.not_lt_min (y.to_set \ x.to_set) _ ⟨hy.mem_trans hzm hmy, hzx⟩ hzm },
  cases IH m x (game_add.snd hmy).swap_mk_left (hy.mem hmy) hx hmx with H H,
  { right, rwa ←H },
  { exact (set.not_mem_of_mem_diff hm H).elim }
end, hy.subset_of_eq_or_mem⟩

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
  apply game_add_swap.induction mem_wf _ x y,
  intros x y IH hx hy hyx z hzy,
  by_contra hzx,
  exact hyx (mem_of_subset_of_mem hx hy
    (IH z x (game_add.snd hzy).swap_mk_left (hy.mem hzy) hx hzx) hzy),
end, λ hxy hyx, mem_irrefl (hxy hyx)⟩

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

end is_ordinal

/-- Our definition of von Neumann ordinals is equivalent to the standard one. -/
theorem is_ordinal_iff_is_well_order : x.is_ordinal ↔
  x.is_transitive ∧ is_well_order x.to_set (subrel (∈) _) :=
⟨λ h, ⟨h.is_transitive, h.is_well_order⟩, begin
  rintro ⟨h₁, h₂⟩,
  haveI := h₂,
  exact is_ordinal_iff_is_trans.2 ⟨h₁, by apply_instance⟩
end⟩

@[simp] theorem empty_is_ordinal : is_ordinal ∅ :=
⟨empty_is_transitive, λ y z w _ _ H, (mem_empty w H).elim⟩

/-- The successor of an ordinal `x` is `x ∪ {x}`. -/
def succ (x : Set) : Set := insert x x

@[simp] theorem mem_succ_iff {x y : Set} : y ∈ succ x ↔ y = x ∨ y ∈ x := by simp [succ]

theorem mem_succ_of_mem {x y : Set} (h : y ∈ x) : y ∈ succ x := mem_succ_iff.2 $ or.inr h

theorem mem_succ_self (x : Set) : x ∈ succ x := mem_succ_iff.2 $ or.inl rfl

@[simp] theorem succ_to_set (x : Set) : x.succ.to_set = insert x x.to_set := by simp [succ]

theorem is_ordinal.mem_succ_iff_subset (hx : x.is_ordinal) (hy : y.is_ordinal) :
  x ∈ succ y ↔ x ⊆ y :=
by rw [mem_succ_iff, hx.subset_iff_eq_or_mem hy]

theorem is_ordinal.succ {x : Set} (hx : x.is_ordinal) : x.succ.is_ordinal :=
begin
  refine ⟨λ y hy z hz, _, λ y z w hyz hzw hwx, _⟩,
  { rw mem_succ_iff at hy ⊢,
    rcases hy with rfl | hy,
    { exact or.inr hz },
    { exact or.inr (hx.mem_trans hz hy) } },
  { rcases mem_succ_iff.1 hwx with rfl | hwx,
    { exact hx.mem_trans hyz hzw },
    { exact hx.mem_trans' hyz hzw hwx } }
end

theorem is_ordinal.succ_subset_iff_mem (hx : x.is_ordinal) (hy : y.is_ordinal) :
  succ x ⊆ y ↔ x ∈ y :=
by rw [←not_iff_not, hx.succ.not_subset_iff_mem hy, hx.not_mem_iff_subset hy,
  hy.mem_succ_iff_subset hx]

/-- The subtype of von Neumann ordinals. See `ordinal` for the preferred, type-theoretic formulation
of ordinals. -/
def Ordinal : Type* := subtype is_ordinal

instance : partial_order Ordinal :=
{ le := subrel (⊆) _,
  lt := subrel (∈) _,
  le_refl := λ x, subset_refl x.1,
  le_trans := λ x y z, @subset_trans Set _ _ x.1 y.1 z.1,
  lt_iff_le_not_le := λ x y, x.2.mem_iff_subset_not_subset y.2,
  le_antisymm := λ x y hx hy, by simpa [subtype.coe_inj] using subset_antisymm hx hy }

noncomputable instance : linear_order Ordinal :=
{ le_total := λ x y, x.2.subset_total y.2,
  decidable_le := classical.dec_rel _,
  ..Ordinal.partial_order }

instance : has_lt Ordinal := ⟨subrel (∈) _⟩
instance : has_le Ordinal := ⟨subrel (⊆) _⟩

instance : has_zero Ordinal := ⟨⟨∅, empty_is_ordinal⟩⟩

instance Ordinal.is_well_order_to_set (x : Ordinal) : is_well_order x.1.to_set (subrel (∈) _) :=
x.2.is_well_order

/-- **Transfinite induction** on ordinals amounts to saying `<` is well-founded. -/
theorem Ordinal.lt_wf : @well_founded Ordinal (<) := (subrel.rel_embedding _ _).well_founded mem_wf

instance Ordinal.is_well_order : @is_well_order Ordinal (<) := ⟨Ordinal.lt_wf⟩

instance : no_top_order Ordinal :=
⟨λ x, ⟨⟨_, x.2.succ⟩, (@not_le Ordinal _ _ _).2 $ mem_succ_self x.1⟩⟩

instance : succ_order Ordinal := succ_order.of_succ_le_iff_of_le_lt_succ
  (λ x, ⟨_, x.2.succ⟩) (λ x y, x.2.succ_subset_iff_mem y.2) (λ x y, (x.2.mem_succ_iff_subset y.2).1)

instance : has_one Ordinal := ⟨order.succ 0⟩

end Set
