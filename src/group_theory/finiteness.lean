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

/-- A monoid finitely generated if it is finitely generated as a submonoid of itself. -/
@[to_additive]
def monoid.fg : Prop := (⊤ : submonoid M).fg

/-- An additive monoid finitely generated if it is finitely generated as an additive submonoid of
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
