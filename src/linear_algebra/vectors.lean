/-
Copyright (c) 2021 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak, Kyle Miller
-/

import data.matrix.basic
import data.matrix.notation
import tactic.fin_cases

/-!
# Vectors

This module privates some trivial lemmata for easier work with explicit vectors in R^2 and R^3.

## Notation

The locale `vectors` gives the following notation:

* `⬝`  for dot products

## Tags

vectors
-/



variables {R : Type*} [comm_ring R]

lemma vec2_eq {a₀ a₁ b₀ b₁ : R} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) :
  ![a₀, a₁] = ![b₀, b₁] :=
by { ext x, fin_cases x; assumption }

lemma vec2_add {a₀ a₁ b₀ b₁ : R} :
  ![a₀, a₁] + ![b₀, b₁] = ![a₀ + b₀, a₁ + b₁] :=
by { ext x, fin_cases x; refl }

lemma vec3_eq {a₀ a₁ a₂ b₀ b₁ b₂ : R} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) :
  ![a₀, a₁, a₂] = ![b₀, b₁, b₂] :=
by { ext x, fin_cases x; assumption }

lemma vec3_add {a₀ a₁ a₂ b₀ b₁ b₂ : R} :
  ![a₀, a₁, a₂] + ![b₀, b₁, b₂] = ![a₀ + b₀, a₁ + b₁, a₂ + b₂] :=
by { ext x, fin_cases x; refl }


localized "infix  ` ⬝ ` : 67 := matrix.dot_product" in vectors

lemma vec2_dot_product (v w : fin 2 → R) :
  v ⬝ w = v 0 * w 0 + v 1 * w 1 :=
by simp [matrix.dot_product, add_assoc, fin.sum_univ_succ]

lemma vec3_dot_product (v w : fin 3 → R) :
  v ⬝ w = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 :=
by simp [matrix.dot_product, add_assoc, fin.sum_univ_succ]
