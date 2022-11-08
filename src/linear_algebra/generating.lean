/-
Copyright (c) 2022 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/
import linear_algebra.finsupp

/-!
## Generating families

Let `V` be a `R`-module. A family `b : ι → V` is a basis if it is both "linearly independent"
and "generating `V`". This statement is `basis.mk` in [linear_algebra.basis].

This file provides methods to prove that a family is generating,
i.e. that `⊤ ≤ span R (range b)`.

This is particularly helpful when dealing with concrete vectors in finite
vector spaces, like `![![1, 0], ![1, 1]]`.

## Main statements:

- `mem_span_range_iff`:    Any `x ∈ span R (range b)` can be written as linear combination of `b`.
- `top_le_span_range_iff`: A family `b` is generating if every element in `V`
                           can be written as linear combination of `b`.

-/

open_locale big_operators
open submodule set

/-!
### Finite Type

These results assume that the family `b : ι → V` is finite. The typical application are
families of the form `b : (fin n) → V`, i.e. see [data.fin.vec_notation].
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
An element `x` lies in the span of `b` iff it can be written as linear combination
of elements in `b`.
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

/--
A family `b: ι → V` is generating `V` iff every element of `V`
can be written as linear combination.
-/
theorem top_le_span_range_iff :
  ⊤ ≤ span R (range b) ↔ ∀ x, ∃ (coef : ι → R), ∑ i, (coef i) • (b i) = x :=
begin
  constructor,
  { intros h x,
    replace h : x ∈ _ := h mem_top,
    cases exists_sum_coef_smul h with coef hc,
    exact ⟨coef, hc⟩ },
  { intros h x _,
    exact mem_span_range (h x) }
end
