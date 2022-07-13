/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import logic.hydra
import order.succ_pred.basic
import set_theory.ordinal.arithmetic
import set_theory.zfc.basic

/-!
# Von Neumann ordinals

This file develops the theory of von Neumann ordinals: transitive sets, well-ordered under `∈`.

## Definitions

- `Set.is_transitive`: every element of a set is a subset.
- `Set.is_ordinal`: a set is transitive, and transitive under `∈`.
- `Ordinal`: the subtype of ordinal `Set`s.

## Main results

- `is_ordinal_iff_well_founded`: proves our simple characterization of von Neumann sets to be
  equivalent with the usual characterization.
- `Ordinal.lt_wf`: transfinite induction on ordinals.
- `Ordinal.linear_order`: ordinals form a linear order.

## Todo

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

protected theorem is_transitive.inter (hx : x.is_transitive) (hy : y.is_transitive) :
  (x ∩ y).is_transitive :=
λ z hz w hw, by { rw mem_inter at hz ⊢, exact ⟨hx.mem_trans hw hz.1, hy.mem_trans hw hz.2⟩ }

protected theorem is_transitive.Union (h : x.is_transitive) : (⋃ x).is_transitive :=
λ y hy z hz, begin
  rcases mem_Union.1 hy with ⟨w, hw, hw'⟩,
  exact mem_Union_of_mem hz (h.mem_trans hw' hw)
end

theorem is_transitive.Union' (H : ∀ y ∈ x, is_transitive y) : (⋃ x).is_transitive :=
λ y hy z hz, begin
  rcases mem_Union.1 hy with ⟨w, hw, hw'⟩,
  exact mem_Union_of_mem ((H w hw).mem_trans hz hw') hw
end

theorem is_transitive_iff_Union_subset : x.is_transitive ↔ ⋃ x ⊆ x :=
⟨λ h y hy, by { rcases mem_Union.1 hy with ⟨z, hz, hz'⟩, exact h.mem_trans hz' hz },
  λ H y hy z hz, H $ mem_Union_of_mem hz hy⟩

alias is_transitive_iff_Union_subset ↔ is_transitive.Union_subset _

theorem is_transitive_iff_subset_powerset : x.is_transitive ↔ x ⊆ powerset x :=
⟨λ h y hy, mem_powerset.2 $ h.subset_of_mem hy, λ H y hy z hz, mem_powerset.1 (H hy) hz⟩

alias is_transitive_iff_subset_powerset ↔ is_transitive.subset_powerset _

/-! ### Ordinals as sets -/

/-- A set `x` is a von Neumann ordinal when it's a transitive set, that's transitive under `∈`. We
prove that this further implies that `x` is well-ordered under `∈`. -/
def is_ordinal (x : Set) : Prop := x.is_transitive ∧ ∀ y z w : Set, y ∈ z → z ∈ w → w ∈ x → y ∈ w

namespace is_ordinal

protected theorem is_transitive (h : x.is_ordinal) : x.is_transitive := h.1

theorem subset_of_mem (h : x.is_ordinal) : y ∈ x → y ⊆ x := h.is_transitive.subset_of_mem

theorem mem_trans (h : z.is_ordinal) : x ∈ y → y ∈ z → x ∈ z := h.is_transitive.mem_trans

theorem mem_trans' (hx : x.is_ordinal) : y ∈ z → z ∈ w → w ∈ x → y ∈ w := hx.2 y z w

protected theorem Union (H : ∀ y ∈ x, is_ordinal y) : (Union x).is_ordinal :=
begin
  refine ⟨is_transitive.Union' $ λ y hy, (H y hy).is_transitive, λ y z w hyz hzw hwx, _⟩,
  { rcases mem_Union.1 hwx with ⟨v, hvx, hwv⟩,
    exact (H v hvx).mem_trans' hyz hzw hwv }
end

protected theorem union (hx : x.is_ordinal) (hy : y.is_ordinal) : (x ∪ y).is_ordinal :=
is_ordinal.Union $ λ z hz, by { rcases mem_pair.1 hz with rfl | rfl, assumption' }

protected theorem inter (hx : x.is_ordinal) (hy : y.is_ordinal) : (x ∩ y).is_ordinal :=
⟨hx.is_transitive.inter hy.is_transitive, λ z w v hzw hwv hv,
  hx.mem_trans' hzw hwv (mem_inter.1 hv).1⟩

protected theorem is_trans (h : x.is_ordinal) : is_trans x.to_set (subrel (∈) _) :=
⟨λ a b c hab hbc, h.mem_trans' hab hbc c.2⟩

theorem _root_.is_ordinal_iff_is_trans : x.is_ordinal ↔
  x.is_transitive ∧ is_trans x.to_set (subrel (∈) _) :=
⟨λ h, ⟨h.is_transitive, h.is_trans⟩, λ ⟨h₁, ⟨h₂⟩⟩, ⟨h₁, λ y z w hyz hzw hwx,
  let hzx := h₁.mem_trans hzw hwx in h₂ ⟨y, h₁.mem_trans hyz hzx⟩ ⟨z, hzx⟩ ⟨w, hwx⟩ hyz hzw⟩⟩

/-- A relation embedding between a smaller and a larger ordinal. -/
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
⟨λ h, ⟨h.is_transitive, h.is_well_order⟩, λ ⟨h₁, h₂⟩, is_ordinal_iff_is_trans.2 $
  by { haveI := h₂, exact ⟨h₁, by apply_instance⟩ }⟩

theorem is_transitive.is_ordinal (h : x.is_transitive) (H : ∀ y ∈ x, is_ordinal y) : x.is_ordinal :=
⟨h, λ y z w hyz hzw hwx, (H w hwx).mem_trans hyz hzw⟩

@[simp] theorem empty_is_ordinal : is_ordinal ∅ :=
⟨empty_is_transitive, λ y z w _ _ H, (mem_empty w H).elim⟩

/-- The successor of an ordinal `x` is `{x} ∪ x`. -/
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

/-! ### Subtype of ordinals -/

/-- The subtype of von Neumann ordinals. See `ordinal` for the preferred, type-theoretic formulation
of ordinals. -/
def Ordinal : Type* := subtype is_ordinal

namespace Ordinal

instance : has_coe Ordinal.{u} Set.{u} := coe_subtype

def mk (h : x.is_ordinal) : Ordinal := ⟨x, h⟩

@[simp] theorem mk_eq (h : x.is_ordinal) : (⟨x, h⟩ : Ordinal) = mk h := rfl
@[simp] theorem val_eq_coe (x : Ordinal) : x.val = x := rfl
@[simp] theorem coe_mk (h : x.is_ordinal) : ↑(mk h) = x := rfl

instance : partial_order Ordinal :=
{ le := subrel (⊆) _,
  lt := subrel (∈) _,
  le_refl := λ x, subset_refl x.1,
  le_trans := λ x y z, @subset_trans Set _ _ x.1 y.1 z.1,
  lt_iff_le_not_le := λ x y, x.2.mem_iff_subset_not_subset y.2,
  le_antisymm := λ x y hx hy, by simpa [subtype.coe_inj] using subset_antisymm hx hy }

@[simp] theorem mk_lt_mk (hx : x.is_ordinal) (hy : y.is_ordinal) : mk hx < mk hy ↔ x ∈ y := iff.rfl
@[simp] theorem mk_le_mk (hx : x.is_ordinal) (hy : y.is_ordinal) : mk hx ≤ mk hy ↔ x ⊆ y := iff.rfl

@[simp] theorem coe_mem_coe {x y : Ordinal.{u}} : (x : Set.{u}) ∈ (y : Set.{u}) ↔ x < y :=
iff.rfl
@[simp] theorem coe_subset_coe {x y : Ordinal.{u}} : (x : Set.{u}) ⊆ (y : Set.{u}) ↔ x ≤ y :=
iff.rfl

noncomputable instance : linear_order Ordinal :=
{ max := λ x y, ⟨x.1 ∪ y.1, x.2.union y.2⟩,
  max_def := begin
    ext x y z,
    cases x.2.mem_or_subset y.2 with h h,
    { simp only [val_eq_coe, coe_mem_coe] at h,
      have : x ≤ y := h.le,
      simpa [max_default, h, not_le_of_gt h] using @this z },
    { simp only [val_eq_coe, coe_subset_coe] at h,
      simpa [max_default, h] using @h z }
  end,
  min := λ x y, ⟨x.1 ∩ y.1, x.2.inter y.2⟩,
  min_def := begin
    ext x y z,
    cases y.2.mem_or_subset x.2 with h h,
    { simp only [val_eq_coe, coe_mem_coe] at h,
      have : y ≤ x := h.le,
      simpa [min_default, h, not_le_of_gt h] using @this z },
    { simp only [val_eq_coe, coe_subset_coe] at h,
      simpa [min_default, h] using @h z },
  end,
  le_total := λ x y, x.2.subset_total y.2,
  decidable_le := classical.dec_rel _,
  ..Ordinal.partial_order }

instance : has_zero Ordinal := ⟨⟨∅, empty_is_ordinal⟩⟩

instance Ordinal.is_well_order_to_set (x : Ordinal) : is_well_order x.1.to_set (subrel (∈) _) :=
x.2.is_well_order

/-- **Transfinite induction** on ordinals amounts to saying `<` is well-founded. -/
theorem Ordinal.lt_wf : @well_founded Ordinal (<) := (subrel.rel_embedding _ _).well_founded mem_wf

instance Ordinal.is_well_order : @is_well_order Ordinal (<) := ⟨Ordinal.lt_wf⟩

instance : no_max_order Ordinal := ⟨λ x, ⟨⟨_, x.2.succ⟩, mem_succ_self x.1⟩⟩

instance : succ_order Ordinal := succ_order.of_succ_le_iff_of_le_lt_succ
  (λ x, ⟨_, x.2.succ⟩) (λ x y, x.2.succ_subset_iff_mem y.2) (λ x y, (x.2.mem_succ_iff_subset y.2).1)

instance : has_one Ordinal := ⟨order.succ 0⟩

end Ordinal

end Set

/-! ### Convert between ordinals -/

namespace ordinal

variables {a b o : ordinal.{u}}

/-- Converts an ordinal to a pre-Set. Compare with `ordinal.to_pgame`. -/
noncomputable! def to_pSet : ordinal → pSet
| o := ⟨o.out.α, λ i, let hwf := typein_lt_self i in to_pSet (typein (<) i)⟩
using_well_founded { dec_tac := `[assumption] }

theorem to_pSet_def (o : ordinal) : o.to_pSet = ⟨o.out.α, to_pSet ∘ typein (<)⟩ := by rw to_pSet

@[simp] theorem to_pSet_type (o : ordinal) : o.to_pSet.type = o.out.α := by { rw to_pSet_def, refl }

/-- Converts an ordinal less than `o` into a member of the type for the `pSet` corresponding to `o`,
and vice versa. -/
noncomputable def to_type_to_pSet : set.Iio o ≃ o.to_pSet.type :=
(enum_iso_out o).to_equiv.trans $ (equiv.cast $ to_pSet_type o).symm

@[simp] theorem to_type_to_pSet_symm_lt (i : o.to_pSet.type) : ↑(to_type_to_pSet.symm i) < o :=
(to_type_to_pSet.symm i).prop

theorem to_pSet_func_heq : o.to_pSet.func == λ x : o.out.α, (typein (<) x).to_pSet :=
by { rw to_pSet, refl }

@[simp] theorem to_pSet_func' (i) : o.to_pSet.func i = (to_type_to_pSet.symm i).val.to_pSet :=
(congr_heq to_pSet_func_heq.symm (cast_heq _ i)).symm

theorem to_pSet_func (i) : o.to_pSet.func (to_type_to_pSet i) = i.val.to_pSet := by simp

instance is_empty_zero_to_pSet_type : is_empty (to_pSet 0).type :=
by { rw to_pSet_type, apply_instance }

@[simp] theorem mem_to_pSet_iff {x : pSet} : x ∈ o.to_pSet ↔ ∃ a < o, pSet.equiv x a.to_pSet :=
begin
  split,
  { rintro ⟨b, h⟩,
    refine ⟨_, to_type_to_pSet_symm_lt b, _⟩,
    simpa using h },
  { rintro ⟨a, ha, h⟩,
    use to_type_to_pSet ⟨a, ha⟩,
    simpa using h }
end

theorem mem_to_pSet_of_lt (h : a < b) : a.to_pSet ∈ b.to_pSet :=
mem_to_pSet_iff.2 ⟨a, h, pSet.equiv.refl _⟩

theorem subset_to_pSet_of_le (h : a ≤ b) : a.to_pSet ⊆ b.to_pSet :=
begin
  rcases eq_or_lt_of_le h with rfl | h,
  { exact subset_rfl },
  { refine λ i, ⟨to_type_to_pSet ⟨(to_type_to_pSet.symm i).1,
      (to_type_to_pSet_symm_lt i).trans h⟩, _⟩,
    simp }
end

/-- Converts an ordinal to a Set. -/
noncomputable def to_Set (o : ordinal) : Set := Set.mk o.to_pSet

theorem mem_to_Set_of_lt : a < b → a.to_Set ∈ b.to_Set := mem_to_pSet_of_lt

theorem subset_to_Set_of_le : a ≤ b → a.to_Set ⊆ b.to_Set :=
by simpa [to_Set] using subset_to_pSet_of_le

@[simp] theorem to_Set_mem_iff : a.to_Set ∈ b.to_Set ↔ a < b :=
⟨λ h, by { by_contra' h', exact Set.mem_irrefl (subset_to_Set_of_le h' h) }, mem_to_Set_of_lt⟩

@[simp] theorem to_Set_subset_iff : a.to_Set ⊆ b.to_Set ↔ a ≤ b :=
⟨λ h, by { by_contra' h', exact Set.mem_irrefl (h (mem_to_Set_of_lt h')) }, subset_to_Set_of_le⟩

@[simp] theorem mem_to_Set_iff : x ∈ o.to_Set ↔ ∃ a < o, x = a.to_Set :=
by { rw [←quotient.out_eq x, to_Set, Set.mk_eq, Set.mk_mem_iff, mem_to_pSet_iff], simpa [←Set.eq] }

theorem to_Set_is_ordinal (o : ordinal) : o.to_Set.is_ordinal :=
begin
  induction o using ordinal.induction with o IH,
  refine ⟨λ a ha b hb, _, λ a b c hab hbc hco, _⟩,
  { rcases mem_to_Set_iff.1 ha with ⟨c, hc, rfl⟩,
    exact Set.mem_of_mem_of_subset hb (subset_to_Set_of_le hc.le) },
  { rcases mem_to_Set_iff.1 hco with ⟨d, hd, rfl⟩,
    exact (IH d hd).mem_trans hab hbc }
end

theorem zero_to_pSet : pSet.equiv (to_pSet 0) ∅ := pSet.equiv.equiv_of_is_empty _ _

@[simp] theorem zero_to_Set : to_Set 0 = ∅ := quotient.sound zero_to_pSet

@[simp] theorem succ_to_Set (o : ordinal) : (order.succ o).to_Set = o.to_Set.succ :=
begin
  ext x,
  simp only [mem_to_Set_iff, order.lt_succ_iff, exists_prop, Set.mem_succ_iff],
  split,
  { rintro ⟨a, ha, rfl⟩,
    rcases eq_or_lt_of_le ha with rfl | ha,
    { exact or.inl rfl },
    { exact or.inr ⟨a, ha, rfl⟩ } },
  { rintro (rfl | ⟨a, ha, rfl⟩),
    { exact ⟨o, le_rfl, rfl⟩ },
    { exact ⟨a, ha.le, rfl⟩ } }
end

/-- Converts an ordinal to a von Neumann ordinal. -/
noncomputable def to_Ordinal (o : ordinal) : Set.Ordinal := ⟨_, o.to_Set_is_ordinal⟩

@[simp] theorem to_Ordinal_lt_iff : a.to_Ordinal < b.to_Ordinal ↔ a < b := to_Set_mem_iff
@[simp] theorem to_Ordinal_le_iff : a.to_Ordinal ≤ b.to_Ordinal ↔ a ≤ b := to_Set_subset_iff

theorem to_Ordinal_strict_mono : strict_mono to_Ordinal := λ a b, to_Ordinal_lt_iff.2

@[simp] theorem zero_to_Ordinal : to_Ordinal 0 = 0 := subtype.coe_injective zero_to_Set

@[simp] theorem succ_to_Ordinal (o : ordinal) :
  (order.succ o).to_Ordinal = order.succ o.to_Ordinal :=
subtype.coe_injective $ succ_to_Set o

@[simp] theorem one_to_Ordinal : to_Ordinal 1 = 1 := by simpa using succ_to_Ordinal 0

end ordinal
