/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import set_theory.ordinal.arithmetic
import set_theory.zfc.basic

/-!
# Von Neumann ordinals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

variables {x y z : Set.{u}}

namespace Set

/- ### Transitive sets -/

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

/- ### Von Neumann Hierarchy -/

section von_neumann
variables {o a b : ordinal.{u}}

/-- The von Neumann hierarchy, defined so that

- $V_{\alpha+1}=\mathcal P(V_\alpha)$,
- $V_\alpha=\bigcup_{\beta<\alpha}V_\beta$ for $\alpha=0$ or limit.

Every set belongs to the von Neumann hierarchy (`exists_mem_von_neumann`). -/
-- Todo: the 0 case is the same as the limit case, use an induction principle that merges these.
noncomputable def von_neumann (o : ordinal.{u}) : Set.{u} :=
o.limit_rec_on ∅ (λ x, powerset)
  (λ x hx IH, ⋃₀ range.{u u} (λ i : x.out.α, IH (ordinal.typein (<) i) $ ordinal.typein_lt_self _))

@[simp] theorem von_neumann_zero : von_neumann 0 = ∅ :=
ordinal.limit_rec_on_zero _ _ _

@[simp] theorem von_neumann_succ (o : ordinal) :
  von_neumann (order.succ o) = powerset (von_neumann o) :=
ordinal.limit_rec_on_succ _ _ _ _

theorem von_neumann_limit : o.is_limit →
  von_neumann o = ⋃₀ range.{u u} (λ i : o.out.α, von_neumann (ordinal.typein (<) i)) :=
ordinal.limit_rec_on_limit _ _ _ _

theorem mem_von_neumann_limit (ho : o.is_limit) : x ∈ von_neumann o ↔ ∃ a < o, x ∈ von_neumann a :=
begin
  simp only [von_neumann_limit ho, mem_sUnion, mem_range, set.mem_range, exists_prop,
    exists_exists_eq_and],
  split,
  { rintro ⟨a, ha⟩,
    exact ⟨_, ordinal.typein_lt_self _, ha⟩ },
  { rintro ⟨a, ha, hx⟩,
    refine ⟨ordinal.enum (<) a _, _⟩;
    simpa }
end

theorem von_neumann_transitive (o : ordinal) : (von_neumann o).is_transitive :=
begin
  induction o using ordinal.limit_rec_on with o ho o ho IH,
  { rw von_neumann_zero,
    exact empty_is_transitive },
  { rw von_neumann_succ,
    exact ho.powerset },
  { intros x hx y hy,
    rw mem_von_neumann_limit ho at hx ⊢,
    rcases hx with ⟨b, hb, hx⟩,
    exact ⟨b, hb, (IH b hb).subset_of_mem hx hy⟩ }
end

/-- The rank of a set, recursively defined as the least ordinal greater than the ranks of all its
    members. -/
noncomputable def rank : Set.{u} → ordinal.{u} :=
mem_wf.fix $ λ x IH, ordinal.lsub.{u u} $
  λ y : shrink x.to_set, IH ((equiv_shrink _).symm y).1 ((equiv_shrink _).symm y).2

theorem rank_def : ∀ x,
  rank x = ordinal.lsub.{u u} (λ y : shrink x.to_set, rank ((equiv_shrink _).symm y).1) :=
mem_wf.fix_eq _

theorem lt_rank_iff : o < rank x ↔ ∃ y ∈ x, o ≤ rank y :=
begin
  rw [rank_def, ordinal.lt_lsub_iff],
  split,
  { rintro ⟨i, hi⟩,
    let a := (equiv_shrink _).symm i,
    use [a.val, a.prop, hi] },
  { rintro ⟨y, hy, ho⟩,
    use equiv_shrink x.to_set ⟨y, hy⟩,
    simpa using ho }
end

theorem rank_le_iff : rank x ≤ o ↔ ∀ y ∈ x, rank y < o :=
by { rw ←not_iff_not, simpa using lt_rank_iff }

theorem rank_lt_of_mem (h : x ∈ y) : rank x < rank y :=
lt_rank_iff.2 ⟨x, h, le_rfl⟩

theorem rank_le_of_subset (h : x ⊆ y) : rank x ≤ rank y :=
rank_le_iff.2 $ λ z hz, rank_lt_of_mem (h hz)

@[simp] theorem rank_eq_zero_iff : rank x = 0 ↔ x = ∅ :=
begin
  rw [←ordinal.le_zero, rank_le_iff],
  rcases eq_empty_or_nonempty x with rfl | ⟨a, ha⟩,
  { simp },
  { refine ⟨λ IH, (ordinal.not_lt_zero _ (IH a ha)).elim, _⟩,
    rintro rfl,
    exact (not_mem_empty a ha).elim }
end

@[simp] theorem rank_empty : rank ∅ = 0 := rank_eq_zero_iff.2 rfl

theorem mem_von_neumann_iff : ∀ {x}, x ∈ von_neumann o ↔ rank x < o :=
begin
  induction o using ordinal.limit_rec_on with o ho o ho IH,
  { simpa using λ x, ordinal.zero_le _ },
  { intro x,
    simp_rw [von_neumann_succ, mem_powerset, order.lt_succ_iff, rank_le_iff, ←ho],
    refl },
  { intro x,
    rw mem_von_neumann_limit ho,
    split,
    { rintro ⟨a, ha, hx⟩,
      rw IH a ha at hx,
      exact hx.trans ha },
    { intro hx,
      have H := ho.succ_lt hx,
      refine ⟨_, H, _⟩,
      rw IH _ H,
      exact order.lt_succ _ } }
end

theorem subset_von_neumann_iff : x ⊆ von_neumann o ↔ rank x ≤ o :=
by rw [←mem_powerset, ←von_neumann_succ, mem_von_neumann_iff, order.lt_succ_iff]

theorem subset_von_neumann (x) : x ⊆ von_neumann (rank x) :=
subset_von_neumann_iff.2 le_rfl

/-- Every set belongs to the von Neumann hierarchy. -/
theorem exists_mem_von_neumann (x) : x ∈ von_neumann (order.succ (rank x)) :=
by { rw [von_neumann_succ, mem_powerset], exact subset_von_neumann x }

@[simp] theorem von_neumann_rank : rank (von_neumann a) = a :=
begin
  apply eq_of_le_of_not_lt,
  { rw ←subset_von_neumann_iff,
    refl },
  { rw ←mem_von_neumann_iff,
    apply irrefl }
end

@[simp] theorem von_neumann_mem_iff : von_neumann a ∈ von_neumann b ↔ a < b :=
by rw [mem_von_neumann_iff, von_neumann_rank]

@[simp] theorem von_neumann_subset_iff : von_neumann a ⊆ von_neumann b ↔ a ≤ b :=
by rw [subset_von_neumann_iff, von_neumann_rank]

end von_neumann
end Set
