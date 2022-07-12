/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import logic.hydra
import set_theory.zfc.basic

namespace Set

/-- A transitive set is one where every element is a subset. -/
def is_transitive (x : Set) : Prop := ∀ y ∈ x, y ⊆ x

theorem is_transitive.subset_of_mem {x y : Set} (h : x.is_transitive) : y ∈ x → y ⊆ x := h y

theorem is_transitive_iff_mem_trans {z : Set} :
  z.is_transitive ↔ ∀ {x y : Set}, x ∈ y → y ∈ z → x ∈ z :=
⟨λ h x y hx hy, h.subset_of_mem hy hx, λ H x hx y hy, H hy hx⟩

alias is_transitive_iff_mem_trans ↔ is_transitive.mem_trans _

theorem is_transitive.Union {x : Set} (h : x.is_transitive) : (⋃ x).is_transitive :=
λ y hy z hz, begin
  rcases mem_Union.1 hy with ⟨w, hw, hw'⟩,
  exact mem_Union_of_mem hz (h.mem_trans hw' hw)
end

theorem is_transitive_iff_Union_subset {x : Set} : x.is_transitive ↔ ⋃ x ⊆ x :=
⟨λ h y hy, by { rcases mem_Union.1 hy with ⟨z, hz, hz'⟩, exact h.mem_trans hz' hz },
  λ H y hy z hz, H $ mem_Union_of_mem hz hy⟩

alias is_transitive_iff_Union_subset ↔ is_transitive.Union_subset _

theorem is_transitive_iff_subset_powerset {x : Set} : x.is_transitive ↔ x ⊆ powerset x :=
⟨λ h y hy, mem_powerset.2 $ h.subset_of_mem hy, λ H y hy z hz, mem_powerset.1 (H hy) hz⟩

alias is_transitive_iff_subset_powerset ↔ is_transitive.subset_powerset _

#exit

/-- A set is a von Neumann ordinal when it's well-ordered with respect to `∈`, and every element is
a subset.-/
def is_ordinal (x : Set) : Prop := is_well_order x.to_set (subrel (∈) _) ∧ ∀ y ∈ x, y ⊆ x

theorem is_ordinal.is_well_order {x : Set} (h : x.is_ordinal) :
  is_well_order x.to_set (subrel (∈) _) :=
h.1

theorem is_ordinal.subset_of_mem {x y : Set} (hx : x.is_ordinal) : y ∈ x → y ⊆ x :=
hx.2 y

theorem is_ordinal.mem_trichotomous {x y z : Set} (hx : x.is_ordinal) (hy : y ∈ x) (hz : z ∈ x) :
  y ∈ z ∨ y = z ∨ z ∈ y :=
begin
  haveI := hx.is_well_order,
  simpa using @trichotomous x.to_set (subrel (∈) _) _ ⟨y, hy⟩ ⟨z, hz⟩
end

theorem is_ordinal.mem_trans {x y z : Set} (hx : x.is_ordinal) (hz : z ∈ y) (hy : y ∈ x) : z ∈ x :=
hx.subset_of_mem hy hz

theorem is_ordinal.mem_trans' {x y z w : Set} (hx : x.is_ordinal)
  (hy : y ∈ z) (hz : z ∈ w) (hw : w ∈ x) : y ∈ w :=
let H := hx.is_well_order.trans, hz' := hx.mem_trans hz hw in
  H ⟨y, hx.mem_trans hy hz'⟩ ⟨z, hz'⟩ ⟨w, hw⟩ hy hz

theorem is_ordinal.mem {x y : Set} (hx : x.is_ordinal) (hy : y ∈ x) : y.is_ordinal :=
begin
  refine ⟨@rel_embedding.is_well_order _ _ _ _ _ hx.is_well_order,
    λ z hz a ha, hx.mem_trans' ha hz hy⟩,
  exact ⟨⟨λ b, ⟨b.1, hx.subset_of_mem hy b.2⟩, λ a b, by simp [subtype.coe_inj]⟩,
    λ a b, by simp⟩
end

@[simp] theorem empty_is_ordinal : is_ordinal ∅ :=
⟨by { rw empty_to_set, apply_instance }, λ y, by simp⟩

theorem is_ordinal.subset_of_mem_or_eq {x y : Set} (h : y.is_ordinal) :
  x ∈ y ∨ x = y → x ⊆ y :=
begin
  rintro (hx | rfl),
  { exact h.subset_of_mem hx },
  { exact subset_rfl }
end

theorem is_ordinal.subset_iff_mem_or_eq {x y : Set} (hx : x.is_ordinal) (hy : y.is_ordinal) :
  x ⊆ y ↔ x ∈ y ∨ x = y :=
⟨begin
  suffices : ∀ a : Set × Set, a.1.is_ordinal → a.2.is_ordinal → a.1 ⊆ a.2 → a.1 ∈ a.2 ∨ a.1 = a.2,
  { exact this (x, y) hx hy },
  intro a,
  apply (well_founded.game_add_swap mem_wf).induction a, clear hx hy x y,
  rintros ⟨x, y⟩ IH h₁ h₂ Hxy,
  dsimp at *,
  by_cases Hyx : y ⊆ x,
  { exact or.inr (subset_antisymm Hxy Hyx) },
  let m := mem_wf.min (x.to_set \ y.to_set) (set.nonempty_diff.2 (begin
    simp,
  end)),
end, hy.subset_of_mem_or_eq⟩

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

/-- The successor of an ordinal `x` is `x ∪ {x}`. -/
def succ (x : Set) : Set := insert x x

@[simp] theorem mem_succ_iff {x y : Set} : y ∈ succ x ↔ y = x ∨ y ∈ x := by simp [succ]

theorem mem_succ_of_mem {x y : Set} (h : y ∈ x) : y ∈ succ x := mem_succ_iff.2 $ or.inr h

theorem mem_succ_self (x : Set) : x ∈ succ x := mem_succ_iff.2 $ or.inl rfl

@[simp] theorem succ_to_set (x : Set) : x.succ.to_set = insert x x.to_set := by simp [succ]

def foo {x : Set} (h : x.is_ordinal) :
  subrel (∈) x.succ.to_set ↪r @has_lt.lt (with_top {y : Ordinal // y < ⟨x, h⟩}) _ :=
sorry

example {x : Set} (h : x.is_ordinal) : is_well_order x.succ.to_set (subrel (∈) _) :=
begin
haveI := with_top.is_well_order,
  apply (foo h).is_well_order,
end

theorem is_ordinal.succ {x : Set} (hx : x.is_ordinal) : x.succ.is_ordinal :=
begin
  refine ⟨_, λ y hy z hz, _⟩,
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
end



instance : partial_order Ordinal :=
{ le_refl := λ x, subset_refl x.1,
  le_trans := λ x y z, @subset_trans Set _ _ x.1 y.1 z.1,
  lt_iff_le_not_le := λ x y, begin
    use λ hx, ⟨y.2.subset_of_mem hx, λ hy, mem_irrefl (mem_of_mem_of_subset hx hy)⟩,

  end,
  le_antisymm := λ x y hx hy, by simpa [subtype.coe_inj] using @subset_antisymm _ _ x.1 y.1 _ hx hy,
  ..Ordinal.has_lt, ..Ordinal.has_le }

theorem is_ordinal.eq_or_mem_of_subset {x y : Set} (hx : x.is_ordinal) (hy : y.is_ordinal)
  (h : x ⊆ y) : x = y ∨ x ∈ y :=
begin

end

end Set
