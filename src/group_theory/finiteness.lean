/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import data.set.finite
import group_theory.submonoid.operations
import group_theory.subgroup

/-!
# Finitely generated monoid.

We define finitely generated monoids.

## Main definition

* `monoid.fg`, `add_monoid.fg` : A monoid is finitely generated.

-/

section monoid

variables {M N : Type*} [monoid M] [add_monoid N]

/-- A submonoid of `M` is finitely generated if it is the closure of a finite subset of `M`. -/
@[to_additive]
def submonoid.fg (P : submonoid M) : Prop := ∃ S : finset M, submonoid.closure ↑S = P

/-- An additive submonoid of `N` is finitely generated if it is the closure of a finite subset of
`M`. -/
add_decl_doc add_submonoid.fg

variables (M N)

/-- A monoid is finitely generated if it is finitely generated as a submonoid of itself. -/
@[to_additive]
def monoid.fg : Prop := (⊤ : submonoid M).fg

/-- An additive monoid is finitely generated if it is finitely generated as an additive submonoid of
itself. -/
add_decl_doc add_monoid.fg

@[to_additive]
lemma monoid.fg_def : monoid.fg M ↔
  ∃ S : set M, submonoid.closure S = (⊤ : submonoid M) ∧ S.finite :=
⟨λ⟨S, hS⟩, ⟨S, hS, finset.finite_to_set S⟩, λ⟨S, hS, hf⟩, ⟨set.finite.to_finset hf, by simp [hS]⟩⟩

lemma monoid_fg_iff_add_fg : monoid.fg M ↔ add_monoid.fg (additive M) :=
begin
  split,
  { intro h,
    obtain ⟨S, hS, hf⟩ := (monoid.fg_def _).1 h,
    rw [add_monoid.fg_def],
    exact ⟨additive.to_mul ⁻¹' S, by simpa [← submonoid.to_add_submonoid_closure, hS], hf⟩ },
  { intro h,
    obtain ⟨T, hT, hf⟩ := (add_monoid.fg_def _).1 h,
    rw [monoid.fg_def],
    exact ⟨multiplicative.of_add ⁻¹' T, by simpa [← submonoid.of_add_submonoid_closure, hT], hf⟩ }
end

lemma add_monoid_fg_iff_mul_fg : add_monoid.fg N ↔ monoid.fg (multiplicative N) :=
begin
  split,
  { intro h,
    obtain ⟨S, hS, hf⟩ := (add_monoid.fg_def _).1 h,
    rw [monoid.fg_def],
    exact ⟨multiplicative.to_add ⁻¹' S, by simpa [← add_submonoid.to_submonoid_closure, hS], hf⟩, },
  { intro h,
    obtain ⟨T, hT, hf⟩ := (monoid.fg_def _).1 h,
    rw [add_monoid.fg_def],
    exact ⟨additive.of_mul ⁻¹' T, by simpa [← add_submonoid.of_submonoid_closure, hT], hf⟩ }
end

end monoid

section group

variables {G H : Type*} [group G] [add_group H]

/-- A subgroup of `G` is finitely generated if it is the closure of a finite subset of `G`. -/
@[to_additive]
def subgroup.fg (P : subgroup G) : Prop := ∃ S : finset G, subgroup.closure ↑S = P

/-- An additive subgroup of `H` is finitely generated if it is the closure of a finite subset of
`H`. -/
add_decl_doc add_subgroup.fg

variables (G H)

/-- A group is finitely generated if it is finitely generated as a submonoid of itself. -/
@[to_additive]
def group.fg : Prop := (⊤ : subgroup G).fg

/-- An additive group is finitely generated if it is finitely generated as an additive submonoid of
itself. -/
add_decl_doc add_group.fg

@[to_additive]
lemma group.fg_def : group.fg G ↔
  ∃ S : set G, subgroup.closure S = (⊤ : subgroup G) ∧ S.finite :=
⟨λ⟨S, hS⟩, ⟨S, hS, finset.finite_to_set S⟩, λ⟨S, hS, hf⟩, ⟨set.finite.to_finset hf, by simp [hS]⟩⟩

/-- A group if finitely generated if and only if it is finitely generated as a monoid. -/
lemma group.fg_iff_monoid.fg : group.fg G ↔ monoid.fg G :=
begin
  split,
  { rintro ⟨S, hS⟩,
    rw [monoid.fg_def],
    refine ⟨S ∪ S⁻¹, _, _⟩,
    { simpa [← subgroup.closure_to_submonoid, hS] },
    { exact set.finite.union (finset.finite_to_set S) (set.finite.inv (finset.finite_to_set S)) } },
  { rintro ⟨S, hS⟩,
    refine ⟨S, le_antisymm le_top _⟩,
    change (⊤ : submonoid G) ≤ (subgroup.closure ↑S).to_submonoid,
    rw [← hS, submonoid.closure_le],
    exact subgroup.subset_closure }
end

/-- An additive group if finitely generated if and only if it is finitely generated as an additive
monoid. -/
lemma add_group.fg_iff_add_monoid.fg : add_group.fg H ↔ add_monoid.fg H :=
begin
  split,
  { rintro ⟨S, hS⟩,
    rw [add_monoid.fg_def],
    refine ⟨S ∪ -S, _, _⟩,
    { simpa [← add_subgroup.closure_to_add_submonoid, hS] },
    { exact set.finite.union (finset.finite_to_set S) (set.finite.neg (finset.finite_to_set S)) } },
  { rintro ⟨S, hS⟩,
    refine ⟨S, le_antisymm le_top _⟩,
    change (⊤ : add_submonoid H) ≤ (add_subgroup.closure ↑S).to_add_submonoid,
    rw [← hS, add_submonoid.closure_le],
    exact add_subgroup.subset_closure }
end

lemma group_fg_iff_add_fg : group.fg G ↔ add_group.fg (additive G) :=
begin
  rw [group.fg_iff_monoid.fg, add_group.fg_iff_add_monoid.fg],
  exact monoid_fg_iff_add_fg G
end

lemma add_group_fg_iff_mul_fg : add_group.fg H ↔ group.fg (multiplicative H) :=
begin
  rw [group.fg_iff_monoid.fg, add_group.fg_iff_add_monoid.fg],
  exact add_monoid_fg_iff_mul_fg H
end

end group
