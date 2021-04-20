/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import ring_theory.finiteness
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
def submonoid.fg (P : submonoid M) : Prop := ∃ S : finset M, submonoid.closure ↑S = P

/-- An additive submonoid of `N` is finitely generated if it is the closure of a finite subset of
`M`. -/
def add_submonoid.fg (P : add_submonoid N) : Prop := ∃ S : finset N, add_submonoid.closure ↑S = P

variables (M N)

/-- A monoid finitely generated if it is finitely generated as a submonoid of itself. -/
def monoid.fg : Prop := (⊤ : submonoid M).fg

lemma monoid.fg_def : monoid.fg M ↔
  ∃ S : set M, submonoid.closure S = (⊤ : submonoid M) ∧ S.finite :=
⟨λ⟨S, hS⟩, ⟨S, hS, finset.finite_to_set S⟩, λ⟨S, hS, hf⟩, ⟨set.finite.to_finset hf, by simp [hS]⟩⟩

/-- An additive monoid finitely generated if it is finitely generated as an additive submonoid of
itself. -/
def add_monoid.fg : Prop := (⊤ : add_submonoid N).fg

lemma add_monoid.fg_def : add_monoid.fg N ↔
  ∃ S : set N, add_submonoid.closure S = (⊤ : add_submonoid N) ∧ S.finite :=
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

lemma comm_add_monoid_fg_iff_span {M : Type*} [add_comm_monoid M] :
  add_monoid.fg M ↔ ∃ S : finset M, submodule.span ℕ (S : set M) = (⊤ : submodule ℕ M) :=
begin
  split,
  { rintro ⟨S, hS⟩,
    refine ⟨S, _⟩,
    rw [← submodule.span_nat_eq_add_submonoid_closure] at hS,
    exact submodule.to_add_submonoid_injective hS },
  { rintro ⟨S, hS⟩,
    refine ⟨S, _⟩,
    rw [← submodule.span_nat_eq_add_submonoid_closure],
    simp only [hS, submodule.top_to_add_submonoid] }
end

end monoid
