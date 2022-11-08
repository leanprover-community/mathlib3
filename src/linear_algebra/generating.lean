/-
Copyright (c) 2022 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/
import linear_algebra.finsupp

open_locale big_operators
open submodule set

/-!
## Generating families

Let `V` be a `R`-module. A family `b : ι → V` is a basis if it is both 'linearly independent'
and 'generating `V`'. This statement is `basis.mk` in [linear_algebra.basis].

This file provides methods to proof that a family is generating,
i.e. that `⊤ ≤ span R (range b)`.
-/

/-!
### Finite Type
-/

variables {R M ι : Type*} [ring R] [add_comm_monoid M] [module R M] [fintype ι]
variables {x : M} {b : ι → M}

lemma exists_sum_coef_smul (h : x ∈ span R (range b)) :
  ∃ (coef : ι →₀ R), ∑ i, (coef i) • (b i) = x :=
begin
  rw [←finsupp.range_total, linear_map.mem_range] at h,
  cases h with coef h,
  use coef,
  rw [←h, finsupp.total_apply, finsupp.sum_fintype],
  simp,
end

lemma mem_span_range (h : ∃ (coef : ι → R), ∑ i, (coef i) • (b i) = x) :
  x ∈ span R (range b) :=
begin
  cases h with coef h,
  rw [←finsupp.range_total, linear_map.mem_range],
  lift coef to ι →₀ R using ⟨fintype.of_finite ↥(function.support coef)⟩,
  use coef,
  rw [←h, finsupp.total_apply, finsupp.sum_fintype],
  simp,
end

/--
An element `x` lies in the span of `b` iff it can be written as linear combination of
elements in `b`.
-/
theorem mem_span_range_iff :
  x ∈ span R (range b) ↔ ∃ (coef : ι → R), ∑ i, (coef i) • (b i) = x :=
begin
  constructor,
  { intro h,
    cases exists_sum_coef_smul h with coef h,
    exact ⟨coef, h⟩ },
  { exact mem_span_range }
end
