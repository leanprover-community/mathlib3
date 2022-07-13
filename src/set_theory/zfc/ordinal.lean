/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

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

/-- A set `x` is a von Neumann ordinal when it's a transitive set, that's transitive and
trichotomous under `∈`. Note that this further implies that `x` is well-ordered under `∈`. -/
def is_ordinal (x : Set) : Prop :=
x.is_transitive ∧ is_trans x.to_set (subrel (∈) _) ∧ is_trichotomous x.to_set (subrel (∈) _)

namespace is_ordinal

protected theorem is_transitive (h : x.is_ordinal) : x.is_transitive := h.1

theorem subset_of_mem (h : x.is_ordinal) : y ∈ x → y ⊆ x := h.is_transitive.subset_of_mem

theorem mem_trans (h : z.is_ordinal) : x ∈ y → y ∈ z → x ∈ z := h.is_transitive.mem_trans

protected theorem is_trans (h : x.is_ordinal) : is_trans x.to_set (subrel (∈) _) := h.2.1

theorem mem_trans' (hx : x.is_ordinal) (hy : y ∈ z) (hz : z ∈ w) (hw : w ∈ x) : y ∈ w :=
let H := hx.is_trans.trans, hz' := hx.mem_trans hz hw in
  H ⟨y, hx.mem_trans hy hz'⟩ ⟨z, hz'⟩ ⟨w, hw⟩ hy hz

protected theorem is_trichotomous (h : x.is_ordinal) : is_trichotomous x.to_set (subrel (∈) _) :=
h.2.2

theorem mem_trichotomous (hx : x.is_ordinal) (hy : y ∈ x) (hz : z ∈ x) : y ∈ z ∨ y = z ∨ z ∈ y :=
begin
  haveI := hx.is_trichotomous,
  simpa using @trichotomous x.to_set (subrel (∈) _) _ ⟨y, hy⟩ ⟨z, hz⟩
end

protected theorem is_well_order (h : x.is_ordinal) : is_well_order x.to_set (subrel (∈) _) :=
{ wf := (subrel.rel_embedding _ _).well_founded mem_wf,
  ..h.is_trans, ..h.is_trichotomous }

/-- A relation embedding between an element of an ordinal, and the ordinal itself. -/
protected def rel_embedding (hx : x.is_ordinal) (hy : y ∈ x) :
  subrel (∈) y.to_set ↪r subrel (∈) x.to_set :=
⟨⟨λ b, ⟨b.1, hx.subset_of_mem hy b.2⟩, λ a b, by simp [subtype.coe_inj]⟩, λ a b, by simp⟩

protected theorem mem (hx : x.is_ordinal) (hy : y ∈ x) : y.is_ordinal :=
begin
  haveI := hx.is_well_order,
  haveI := (hx.rel_embedding hy).is_well_order,
  exact ⟨λ z hz a ha, hx.mem_trans' ha hz hy, by apply_instance, by apply_instance⟩
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

theorem not_mem_iff_subset (hx : x.is_ordinal) (hy : y.is_ordinal) : ¬ y ∈ x ↔ x ⊆ y :=
⟨begin
  revert hx hy,
  apply game_add_swap.induction mem_wf _ x y,
  intros x y IH hx hy hyx z hzx,
  by_contra hzy,
  exact hyx (mem_of_subset_of_mem hy hx
    (IH y z (game_add.fst hzx).swap_mk_left hy (hx.mem hzx) hzy) hzx),
end, λ hxy hyx, mem_irrefl (hxy hyx)⟩

end is_ordinal

/-theorem is_transitive.is_ordinal (h : x.is_transitive) (H : ∀ y : Set, y ∈ x → y.is_ordinal) :
  x.is_ordinal :=
⟨h, ⟨begin
  rintros ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ hab hbc,


end⟩, ⟨sorry⟩⟩-/

@[simp] theorem empty_is_ordinal : is_ordinal ∅ :=
⟨empty_is_transitive, by { rw empty_to_set, split; apply_instance }⟩

/-- The successor of an ordinal `x` is `x ∪ {x}`. -/
def succ (x : Set) : Set := insert x x

@[simp] theorem mem_succ_iff {x y : Set} : y ∈ succ x ↔ y = x ∨ y ∈ x := by simp [succ]

theorem mem_succ_of_mem {x y : Set} (h : y ∈ x) : y ∈ succ x := mem_succ_iff.2 $ or.inr h

theorem mem_succ_self (x : Set) : x ∈ succ x := mem_succ_iff.2 $ or.inl rfl

@[simp] theorem succ_to_set (x : Set) : x.succ.to_set = insert x x.to_set := by simp [succ]

theorem subset_iff_mem_succ (hx : x.is_ordinal) (hy : y.is_ordinal) : x ⊆ y ↔ x ∈ succ y :=
by rw [mem_succ_iff, hx.subset_iff_eq_or_mem hy]

/-def foo {x : Set} (h : x.is_ordinal) :
  subrel (∈) x.succ.to_set ↪r @has_lt.lt (with_top {y : Ordinal // y < ⟨x, h⟩}) _ :=
sorry

example {x : Set} (h : x.is_ordinal) : is_well_order x.succ.to_set (subrel (∈) _) :=
begin
haveI := with_top.is_well_order,
  apply (foo h).is_well_order,
end-/

/-theorem is_ordinal.succ {x : Set} (hx : x.is_ordinal) : x.succ.is_ordinal :=
begin
  refine ⟨λ y hy z hz, _, _⟩,
  { exact
    { trichotomous := begin
        rintros ⟨a, ha⟩ ⟨b, hb⟩,
        rw [mem_to_set, mem_succ_iff] at ha hb,
        rcases ha with rfl | ha;
        rcases hb with rfl | hb,
        { exact or.inr (or.inl rfl) },
        { exact or.inr (or.inr hb) },
        { exact or.inl ha },
        { simpa using hx.mem_trichotomous ha hb }
      end,
      irrefl := sorry, -- This field is redundant; a future refactor removes it.
      trans := begin
        rintros ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩,
        rw [mem_to_set, mem_succ_iff] at ha hb hc,
        rcases hc with rfl | hc, swap,
        { exact λ hab hbc, hx.mem_trans' hab hbc hc },
        all_goals { rcases ha with rfl | ha; rcases hb with rfl | hb },
        { exact λ _, id },
        { exact λ hcb hbc, (mem_asymm hcb hbc).elim },
        { exact λ _ h, (mem_irrefl h).elim },
        { exact λ hab hbc, hx.mem_trans hab hb }
      end,
      wf := begin
        split,
        rintro ⟨a, ha⟩,
        rw [mem_to_set, mem_succ_iff] at ha,
        rcases ha with rfl | ha,
      end } },
  { rcases mem_succ_iff.1 hy with rfl | hy,
    { exact mem_succ_of_mem hz },
    { exact mem_succ_of_mem (hx.mem_trans hz hy) } }
end-/



/-instance : partial_order Ordinal :=
{ le_refl := λ x, subset_refl x.1,
  le_trans := λ x y z, @subset_trans Set _ _ x.1 y.1 z.1,
  lt_iff_le_not_le := λ x y, begin
    use λ hx, ⟨y.2.subset_of_mem hx, λ hy, mem_irrefl (mem_of_mem_of_subset hx hy)⟩,

  end,
  le_antisymm := λ x y hx hy, by simpa [subtype.coe_inj] using @subset_antisymm _ _ x.1 y.1 _ hx hy,
  ..Ordinal.has_lt, ..Ordinal.has_le }-/


/-- The subtype of von Neumann ordinals. See `ordinal` for the preferred, type-theoretic formulation
of ordinals. -/
def Ordinal : Type* := subtype is_ordinal

instance : has_lt Ordinal := ⟨subrel (∈) _⟩
instance : has_le Ordinal := ⟨subrel (⊆) _⟩

instance : has_zero Ordinal := ⟨⟨∅, empty_is_ordinal⟩⟩

instance Ordinal.is_well_order_to_set (x : Ordinal) : is_well_order x.1.to_set (subrel (∈) _) :=
x.2.is_well_order

instance Ordinal.subtype_is_well_order (x : Ordinal) : is_well_order {y // y < x} (<) :=
begin
  apply @rel_embedding.is_well_order _ x.1.to_set _ (subrel (∈) _),
  exact ⟨⟨λ a, ⟨a.1.1, a.2⟩, λ a b, by simp [subtype.coe_inj]⟩, λ a b, by simpa⟩
end

/-- **Transfinite induction** on ordinals amounts to saying `<` is well-founded. -/
theorem Ordinal.lt_wf : @well_founded Ordinal (<) := (subrel.rel_embedding _ _).well_founded mem_wf

end Set
