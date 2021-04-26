/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import data.set.finite
import group_theory.submonoid.operations

/-!
# Finitely generated monoid.

We define finitely generated monoids. See also `submodule.fg` and `module.finite` for
finitely-generated modules.

## Main definition

* `submonoid.fg S`, `add_submonoid.fg S` : A submonoid `S` is finitely generated.
* `monoid.fg M`, `add_submonoid.fg M` : A typeclass indicating a type `M` is finitely generated as
a monoid.

-/

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
