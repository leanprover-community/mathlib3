/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import data.set.finite
import group_theory.submonoid.operations

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

variables {M N}

/-- An equivalent expression of `submonoid.fg` in terms of `set.finite` instead of `finset`. -/
@[to_additive "An equivalent expression of `add_submonoid.fg` in terms of `set.finite` instead of
`finset`."]
lemma submonoid.fg_def (P : submonoid M) : submonoid.fg P ↔
  ∃ S : set M, submonoid.closure S = P ∧ S.finite :=
⟨λ ⟨S, hS⟩, ⟨S, hS, finset.finite_to_set S⟩, λ ⟨S, hS, hf⟩, ⟨set.finite.to_finset hf, by simp [hS]⟩⟩

/-- An equivalent expression of `monoid.fg` in terms of `set.finite` instead of `finset`. -/
@[to_additive "An equivalent expression of `add_monoid.fg` in terms of `set.finite` instead of
`finset`."]
lemma monoid.fg_def : monoid.fg M ↔
  ∃ S : set M, submonoid.closure S = (⊤ : submonoid M) ∧ S.finite :=
submonoid.fg_def ⊤

lemma submonoid.fg_iff_add_fg (P : submonoid M) : P.fg ↔ P.to_add_submonoid.fg :=
⟨λ h, let ⟨S, hS, hf⟩ := (submonoid.fg_def _).1 h in (add_submonoid.fg_def _).mpr
  ⟨additive.to_mul ⁻¹' S, by simp [← submonoid.to_add_submonoid_closure, hS], hf⟩,
 λ h, let ⟨T, hT, hf⟩ := (add_submonoid.fg_def _).1 h in (submonoid.fg_def _).mpr
  ⟨multiplicative.of_add ⁻¹' T, by simp [← add_submonoid.to_submonoid'_closure, hT], hf⟩⟩

lemma monoid_fg_iff_add_fg : monoid.fg M ↔ add_monoid.fg (additive M) :=
submonoid.fg_iff_add_fg ⊤

lemma add_submonoid_fg_iff_mul_fg (P : add_submonoid N) : P.fg ↔ P.to_submonoid.fg :=
begin
  convert (submonoid.fg_iff_add_fg P.to_submonoid).symm,
  exact set_like.ext' rfl
end

lemma add_monoid_fg_iff_mul_fg : add_monoid.fg N ↔ monoid.fg (multiplicative N) :=
add_submonoid_fg_iff_mul_fg ⊤

end monoid
