/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import data.finite.basic
import data.set.finite

/-!
# Finite instances for `set`

This module provides ways to go between `set.finite` and `finite` and also provides a number
of `finite` instances for basic set constructions such as unions, intersections, and so on.

## Main definitions

* `set.finite_of_finite` creates a `set.finite` proof from a `finite` instance
* `set.finite.finite` creates a `finite` instance from a `set.finite` proof
* `finite.set.subset` for finiteness of subsets of a finite set

## Tags

finiteness, finite sets

-/

open set
open_locale classical

universes u v w x
variables {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

/-! ### Non-instances -/

lemma finite.of_finite_univ (h : (univ : set α).finite) : finite α :=
set.finite_univ_iff.mp ‹_›

lemma finite.set.finite_of_finite_image (s : set α)
  {f : α → β} (h : s.inj_on f) [finite (f '' s)] : finite s :=
finite.of_equiv _ (equiv.of_bijective _ h.bij_on_image.bijective).symm

lemma finite.of_injective_finite_range {f : α → β}
  (hf : function.injective f) [finite (range f)] : finite α :=
begin
  refine finite.of_injective (set.range_factorization f) (λ x y h, hf _),
  simpa only [range_factorization_coe] using congr_arg (coe : range f → β) h,
end
