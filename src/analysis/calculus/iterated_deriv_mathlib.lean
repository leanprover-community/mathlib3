/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.iterated_deriv

/-!
# One-dimensional iterated derivatives

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the `n`-th derivative of a function `f : 𝕜 → F` as a function
`iterated_deriv n f : 𝕜 → F`, as well as a version on domains `iterated_deriv_within n f s : 𝕜 → F`,
and prove their basic properties.

## Main definitions and results

Let `𝕜` be a nontrivially normed field, and `F` a normed vector space over `𝕜`. Let `f : 𝕜 → F`.

* `iterated_deriv n f` is the `n`-th derivative of `f`, seen as a function from `𝕜` to `F`.
  It is defined as the `n`-th Fréchet derivative (which is a multilinear map) applied to the
  vector `(1, ..., 1)`, to take advantage of all the existing framework, but we show that it
  coincides with the naive iterative definition.
* `iterated_deriv_eq_iterate` states that the `n`-th derivative of `f` is obtained by starting
  from `f` and differentiating it `n` times.
* `iterated_deriv_within n f s` is the `n`-th derivative of `f` within the domain `s`. It only
  behaves well when `s` has the unique derivative property.
* `iterated_deriv_within_eq_iterate` states that the `n`-th derivative of `f` in the domain `s` is
  obtained by starting from `f` and differentiating it `n` times within `s`. This only holds when
  `s` has the unique derivative property.

## Implementation details

The results are deduced from the corresponding results for the more general (multilinear) iterated
Fréchet derivative. For this, we write `iterated_deriv n f` as the composition of
`iterated_fderiv 𝕜 n f` and a continuous linear equiv. As continuous linear equivs respect
differentiability and commute with differentiation, this makes it possible to prove readily that
the derivative of the `n`-th derivative is the `n+1`-th derivative in `iterated_deriv_within_succ`,
by translating the corresponding result `iterated_fderiv_within_succ_apply_left` for the
iterated Fréchet derivative.
-/

noncomputable theory
open_locale classical topology big_operators
open filter asymptotics set


variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
variables {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]

-- lemma iterated_deriv_within_univ {n : ℕ} {f : 𝕜 → F} {n : ℕ} :
--   iterated_deriv_within n f univ = iterated_deriv n f :=

lemma iterated_fderiv_within_nhds {u : set E} {x : E} {f : E → F} {n : ℕ} (hu : u ∈ 𝓝 x) :
  iterated_fderiv_within 𝕜 n f u x = iterated_fderiv 𝕜 n f x :=
by rw [←iterated_fderiv_within_univ, ←univ_inter u, iterated_fderiv_within_inter hu]

lemma iterated_deriv_within_of_is_open {s : set 𝕜} {f : 𝕜 → F} (n : ℕ) (hs : is_open s) :
  eq_on (iterated_deriv_within n f s) (iterated_deriv n f) s :=
λ x hx, by rw [iterated_deriv_within, iterated_deriv, iterated_fderiv_within_of_is_open _ hs hx]

lemma iterated_deriv_within_nhds {u : set 𝕜} {x : 𝕜} {f : 𝕜 → F} {n : ℕ} (hu : u ∈ 𝓝 x) :
  iterated_deriv_within n f u x = iterated_deriv n f x :=
by rw [iterated_deriv_within, iterated_deriv, iterated_fderiv_within_nhds hu]
