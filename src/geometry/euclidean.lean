/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import analysis.normed_space.real_inner_product
import analysis.normed_space.add_torsor

noncomputable theory

/-!
# Euclidean spaces

This file defines Euclidean affine spaces.

## Implementation notes

Rather than requiring Euclidean affine spaces to be finite-dimensional
(as in the definition on Wikipedia), this is specified only for those
theorems that need it.

## References

* https://en.wikipedia.org/wiki/Euclidean_space

-/

/-- A `euclidean_affine_space V P` is an affine space with points `P`
over an `inner_product_space V`. -/
abbreviation euclidean_affine_space (V : Type*) (P : Type*) [inner_product_space V]
    [metric_space P] :=
normed_add_torsor V P

example (n : Type*) [fintype n] : euclidean_affine_space (euclidean_space n) (euclidean_space n) :=
by apply_instance
