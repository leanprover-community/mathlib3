/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.metric_space.basic
import measure_theory.constructions.borel_space

/-!
# Vitali families

On a metric space with a measure `μ`, consider for each `x` a family of closed sets with
nonempty interiors, called `sets_at x`. This family is a Vitali family if it satisfies the following
property: consider a (possible non-measurable) set `s`, and for any `x` in `s` a
subfamily `f x` of `sets_at x` containing sets of arbitrarily small diameter. Then one can extract
a disjoint subfamily covering almost all `s`.

Vitali families are provided by covering theorems such as the Besicovitch covering theorem or the
Vitali covering theorem. They make it possible to formulate general versions of theorems on
differentiations of measure that apply in both contexts.

This file defines Vitali families.
-/

open measure_theory metric set

variables {α : Type*} [metric_space α]

/-- On a metric space with a measure `μ`, consider for each `x` a family of closed sets with
nonempty interiors, called `sets_at x`. This family is a Vitali family if it satisfies the following
property: consider a (possibly non-measurable) set `s`, and for any `x` in `s` a
subfamily `f x` of `sets_at x` containing sets of arbitrarily small diameter. Then one can extract
a disjoint subfamily covering almost all `s`.

Vitali families are provided by covering theorems such as the Besicovitch covering theorem or the
Vitali covering theorem. They make it possible to formulate general versions of theorems on
differentiations of measure that apply in both contexts.
-/
structure vitali_family {m : measurable_space α} (μ : measure α) :=
(sets_at : Π (x : α), set (set α))
(center_mem : ∀ (x : α), ∀ (y : set α), y ∈ sets_at x → x ∈ y)
(is_closed : ∀ (x : α), ∀ (y : set α), y ∈ sets_at x → is_closed y)
(nonempty_interior : ∀ (x : α), ∀ (y : set α), y ∈ sets_at x → (interior y).nonempty)
(covering : ∀ (s : set α) (f : Π (x : α), set (set α)), (∀ x ∈ s, f x ⊆ sets_at x) →
  (∀ (x ∈ s) (ε > (0 : ℝ)), ∃ t ∈ f x, t ⊆ closed_ball x ε) →
  ∃ (t : set α) (u : α → set α), t ⊆ s ∧ pairwise_on t (disjoint on u) ∧ (∀ x ∈ t, u x ∈ f x)
  ∧ μ (s \ ⋃ x ∈ t, u x) = 0)
