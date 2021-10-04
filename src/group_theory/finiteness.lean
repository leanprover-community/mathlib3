/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import data.set.finite
import group_theory.submonoid.operations
import group_theory.subgroup.basic

/-!
# Finitely generated monoids and groups

We define finitely generated monoids and groups. See also `submodule.fg` and `module.finite` for
finitely-generated modules.

## Main definition

* `submonoid.fg S`, `add_submonoid.fg S` : A submonoid `S` is finitely generated.
* `monoid.fg M`, `add_monoid.fg M` : A typeclass indicating a type `M` is finitely generated as a
monoid.
* `subgroup.fg S`, `add_subgroup.fg S` : A subgroup `S` is finitely generated.
* `group.fg M`, `add_group.fg M` : A typeclass indicating a type `M` is finitely generated as a
group.

-/

/-! ### Monoids and submonoids -/

open_locale pointwise
variables {M N : Type*} [monoid M] [add_monoid N]

section submonoid

/-- A submonoid of `M` is finitely generated if it is the closure of a finite subset of `M`. -/
@[to_additive]
def submonoid.fg (P : submonoid M) : Prop := ∃ S : finset M, submonoid.closure ↑S = P

/-- An additive submonoid of `N` is finitely generated if it is the closure of a finite subset of
`M`. -/
add_decl_doc add_submonoid.fg

/-- An equivalent expression of `submonoid.fg` in terms of `set.finite` instead of `finset`. -/
@[to_additive "An equivalent expression of `add_submonoid.fg` in terms of `set.finite` instead of
`finset`."]
lemma submonoid.fg_iff (P : submonoid M) : submonoid.fg P ↔
  ∃ S : set M, submonoid.closure S = P ∧ S.finite :=
⟨λ ⟨S, hS⟩, ⟨S, hS, finset.finite_to_set S⟩, λ ⟨S, hS, hf⟩, ⟨set.finite.to_finset hf, by simp [hS]⟩⟩

lemma submonoid.fg_iff_add_fg (P : submonoid M) : P.fg ↔ P.to_add_submonoid.fg :=
⟨λ h, let ⟨S, hS, hf⟩ := (submonoid.fg_iff _).1 h in (add_submonoid.fg_iff _).mpr
  ⟨additive.to_mul ⁻¹' S, by simp [← submonoid.to_add_submonoid_closure, hS], hf⟩,
 λ h, let ⟨T, hT, hf⟩ := (add_submonoid.fg_iff _).1 h in (submonoid.fg_iff _).mpr
  ⟨multiplicative.of_add ⁻¹' T, by simp [← add_submonoid.to_submonoid'_closure, hT], hf⟩⟩

lemma add_submonoid.fg_iff_mul_fg (P : add_submonoid N) : P.fg ↔ P.to_submonoid.fg :=
begin
  convert (submonoid.fg_iff_add_fg P.to_submonoid).symm,
  exact set_like.ext' rfl
end

end submonoid

section monoid

variables (M N)

/-- A monoid is finitely generated if it is finitely generated as a submonoid of itself. -/
class monoid.fg : Prop := (out : (⊤ : submonoid M).fg)

/-- An additive monoid is finitely generated if it is finitely generated as an additive submonoid of
itself. -/
class add_monoid.fg : Prop := (out : (⊤ : add_submonoid N).fg)

attribute [to_additive] monoid.fg

variables {M N}

lemma monoid.fg_def : monoid.fg M ↔ (⊤ : submonoid M).fg := ⟨λ h, h.1, λ h, ⟨h⟩⟩

lemma add_monoid.fg_def : add_monoid.fg N ↔ (⊤ : add_submonoid N).fg := ⟨λ h, h.1, λ h, ⟨h⟩⟩

/-- An equivalent expression of `monoid.fg` in terms of `set.finite` instead of `finset`. -/
@[to_additive "An equivalent expression of `add_monoid.fg` in terms of `set.finite` instead of
`finset`."]
lemma monoid.fg_iff : monoid.fg M ↔
  ∃ S : set M, submonoid.closure S = (⊤ : submonoid M) ∧ S.finite :=
⟨λ h, (submonoid.fg_iff ⊤).1 h.out, λ h, ⟨(submonoid.fg_iff ⊤).2 h⟩⟩

lemma monoid.fg_iff_add_fg : monoid.fg M ↔ add_monoid.fg (additive M) :=
⟨λ h, ⟨(submonoid.fg_iff_add_fg ⊤).1 h.out⟩, λ h, ⟨(submonoid.fg_iff_add_fg ⊤).2 h.out⟩⟩

lemma add_monoid.fg_iff_mul_fg : add_monoid.fg N ↔ monoid.fg (multiplicative N) :=
⟨λ h, ⟨(add_submonoid.fg_iff_mul_fg ⊤).1 h.out⟩, λ h, ⟨(add_submonoid.fg_iff_mul_fg ⊤).2 h.out⟩⟩

instance add_monoid.fg_of_monoid_fg [monoid.fg M] : add_monoid.fg (additive M) :=
monoid.fg_iff_add_fg.1 ‹_›

instance monoid.fg_of_add_monoid_fg [add_monoid.fg N] : monoid.fg (multiplicative N) :=
add_monoid.fg_iff_mul_fg.1 ‹_›

end monoid

/-! ### Groups and subgroups -/

variables {G H : Type*} [group G] [add_group H]

section subgroup

/-- A subgroup of `G` is finitely generated if it is the closure of a finite subset of `G`. -/
@[to_additive]
def subgroup.fg (P : subgroup G) : Prop := ∃ S : finset G, subgroup.closure ↑S = P

/-- An additive subgroup of `H` is finitely generated if it is the closure of a finite subset of
`H`. -/
add_decl_doc add_subgroup.fg

/-- An equivalent expression of `subgroup.fg` in terms of `set.finite` instead of `finset`. -/
@[to_additive "An equivalent expression of `add_subgroup.fg` in terms of `set.finite` instead of
`finset`."]
lemma subgroup.fg_iff (P : subgroup G) : subgroup.fg P ↔
  ∃ S : set G, subgroup.closure S = P ∧ S.finite :=
⟨λ⟨S, hS⟩, ⟨S, hS, finset.finite_to_set S⟩, λ⟨S, hS, hf⟩, ⟨set.finite.to_finset hf, by simp [hS]⟩⟩

/-- A subgroup is finitely generated if and only if it is finitely generated as a submonoid. -/
@[to_additive add_subgroup.fg_iff_add_submonoid.fg "An additive subgroup is finitely generated if
and only if it is finitely generated as an additive submonoid."]
lemma subgroup.fg_iff_submonoid_fg (P : subgroup G) : P.fg ↔ P.to_submonoid.fg :=
begin
  split,
  { rintro ⟨S, rfl⟩,
    rw submonoid.fg_iff,
    refine ⟨S ∪ S⁻¹, _, S.finite_to_set.union S.finite_to_set.inv⟩,
    exact (subgroup.closure_to_submonoid _).symm },
  { rintro ⟨S, hS⟩,
    refine ⟨S, le_antisymm _ _⟩,
    { rw [subgroup.closure_le, ←subgroup.coe_to_submonoid, ←hS],
      exact submonoid.subset_closure },
    { rw [← subgroup.to_submonoid_le, ← hS, submonoid.closure_le],
      exact subgroup.subset_closure } }
end

lemma subgroup.fg_iff_add_fg (P : subgroup G) : P.fg ↔ P.to_add_subgroup.fg :=
begin
  rw [subgroup.fg_iff_submonoid_fg, add_subgroup.fg_iff_add_submonoid.fg],
  exact (subgroup.to_submonoid P).fg_iff_add_fg
end

lemma add_subgroup.fg_iff_mul_fg (P : add_subgroup H) :
  P.fg ↔ P.to_subgroup.fg :=
begin
  rw [add_subgroup.fg_iff_add_submonoid.fg, subgroup.fg_iff_submonoid_fg],
  exact add_submonoid.fg_iff_mul_fg (add_subgroup.to_add_submonoid P)
end

end subgroup

section group

variables (G H)

/-- A group is finitely generated if it is finitely generated as a submonoid of itself. -/
class group.fg : Prop := (out : (⊤ : subgroup G).fg)

/-- An additive group is finitely generated if it is finitely generated as an additive submonoid of
itself. -/
class add_group.fg : Prop := (out : (⊤ : add_subgroup H).fg)

attribute [to_additive] group.fg

variables {G H}

lemma group.fg_def : group.fg G ↔ (⊤ : subgroup G).fg := ⟨λ h, h.1, λ h, ⟨h⟩⟩

lemma add_group.fg_def : add_group.fg H ↔ (⊤ : add_subgroup H).fg := ⟨λ h, h.1, λ h, ⟨h⟩⟩

/-- An equivalent expression of `group.fg` in terms of `set.finite` instead of `finset`. -/
@[to_additive "An equivalent expression of `add_group.fg` in terms of `set.finite` instead of
`finset`."]
lemma group.fg_iff : group.fg G ↔
  ∃ S : set G, subgroup.closure S = (⊤ : subgroup G) ∧ S.finite :=
⟨λ h, (subgroup.fg_iff ⊤).1 h.out, λ h, ⟨(subgroup.fg_iff ⊤).2 h⟩⟩

/-- A group is finitely generated if and only if it is finitely generated as a monoid. -/
@[to_additive add_group.fg_iff_add_monoid.fg "An additive group is finitely generated if and only
if it is finitely generated as an additive monoid."]
lemma group.fg_iff_monoid.fg : group.fg G ↔ monoid.fg G :=
⟨λ h, monoid.fg_def.2 $ (subgroup.fg_iff_submonoid_fg ⊤).1 (group.fg_def.1 h),
    λ h, group.fg_def.2 $ (subgroup.fg_iff_submonoid_fg ⊤).2 (monoid.fg_def.1 h)⟩

lemma group_fg.iff_add_fg : group.fg G ↔ add_group.fg (additive G) :=
⟨λ h, ⟨(subgroup.fg_iff_add_fg ⊤).1 h.out⟩, λ h, ⟨(subgroup.fg_iff_add_fg ⊤).2 h.out⟩⟩

lemma add_group.fg_iff_mul_fg : add_group.fg H ↔ group.fg (multiplicative H) :=
⟨λ h, ⟨(add_subgroup.fg_iff_mul_fg ⊤).1 h.out⟩, λ h, ⟨(add_subgroup.fg_iff_mul_fg ⊤).2 h.out⟩⟩

instance add_group.fg_of_group_fg [group.fg G] : add_group.fg (additive G) :=
group_fg.iff_add_fg.1 ‹_›

instance group.fg_of_mul_group_fg [add_group.fg H] : group.fg (multiplicative H) :=
add_group.fg_iff_mul_fg.1 ‹_›

end group
