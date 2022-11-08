/-
Copyright (c) 2022 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, Yury Kudryashov
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
open submodule set finsupp

/-!
### Finite Type

These results assume that the family `b : ι → V` is finite. The typical application are
families of the form `b : (fin n) → V`, i.e. see [data.fin.vec_notation].
-/

variables {R M ι : Type*} [ring R] [add_comm_monoid M] [module R M] [fintype ι]
variables {x : M} {b : ι → M}

lemma mem_span_range_iff_exists_finsupp :
  x ∈ span R (range b) ↔ ∃ (c : ι →₀ R), c.sum (λ i a, a • b i) = x :=
by simp only [←finsupp.range_total, linear_map.mem_range, finsupp.total_apply]

/--
An element `x` lies in the span of `b` iff it can be written as linear combination
of elements in `b`.
-/
theorem mem_span_range_iff_exists_fun [fintype ι] :
  x ∈ span R (range b) ↔ ∃ (c : ι → R), ∑ i, c i • b i = x :=
begin
  simp only [mem_span_range_iff_exists_finsupp, equiv_fun_on_fintype.surjective.exists,
    equiv_fun_on_fintype_apply],
  exact exists_congr (λ c, eq.congr_left $ sum_fintype _ _ $ λ i, zero_smul _ _)
end

/--
A family `b: ι → V` is generating `V` iff every element of `V`
can be written as linear combination.
-/
theorem top_le_span_range_iff_forall_exists_fun :
  ⊤ ≤ span R (range b) ↔ ∀ x, ∃ (coef : ι → R), ∑ i, (coef i) • (b i) = x :=
begin
  simp_rw ←mem_span_range_iff_exists_fun,
  rw set_like.le_def,
  constructor,
  { intros h x,
    apply h,
    simp only [mem_top] },
  { intros h x _,
    exact h x },
end
