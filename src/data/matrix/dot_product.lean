/-
Copyright (c) 2020 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade,
-/

import data.complex.basic
import data.fintype.basic
import data.matrix.basic
import linear_algebra.finite_dimensional
import analysis.normed_space.basic
import tactic
/-!
# Complex dot product

In a future refactor, the same facts about the real inner product and complex
inner product should live in this file, assuming we can rip them out of basic.lean without too much trouble.

We give methods for computing coefficients of the characteristic polynomial.

## Main definitions

- `char_poly_degree_eq_dim` proves that the degree of the characteristic polynomial
  over a nonzero ring is the dimension of the matrix
- `det_eq_sign_char_poly_coeff` proves that the determinant is the constant term of the characteristic
  polynomial, up to sign.
- `trace_eq_neg_char_poly_coeff` proves that the trace is the negative of the (d-1)th coefficient of the
  characteristic polynomial, where d is the dimension of the matrix.
  For a nonzero ring, this is the second-highest coefficient.

-/
noncomputable theory
open_locale big_operators
open_locale matrix

universes u v
variables {n m : Type u} [fintype n] [fintype m]

local notation `Euc` := (n → ℂ)

namespace vector
/-- Complex conjugate of a vector.-/
@[simp]
def conj (v : Euc) : Euc :=
λ i, complex.conj (v i)

@[simp]
def complex_dot_product (v : Euc) (w : Euc) : ℂ :=
-- ∑ i, complex.conj (v i) * w i
matrix.dot_product v (conj w)

@[simp]
lemma complex_dot_product_zero {v : Euc} : complex_dot_product v (0 : Euc) = 0 :=
by {ext; simp}

@[simp]
lemma zero_complex_dot_product {v : Euc} : complex_dot_product (0 : Euc) v = 0 :=
by {ext;simp}

@[simp]
lemma complex_dot_product_add {v w u : Euc} :
  complex_dot_product (v + w) u = complex_dot_product v u + complex_dot_product w u :=
by {ext;simp}

@[simp]
lemma complex_dot_product_smul {v w : Euc} {c : ℂ} :
  (c * complex_dot_product v w) = complex_dot_product (c • v) w :=
by {ext; simp}

lemma complex_dot_product_symm {v w : Euc} :
  (complex_dot_product v w) = (complex_dot_product w v).conj :=
begin
  sorry,
end

@[simp]
lemma complex_dot_product_smul' {v w : Euc} {c : ℂ} :
  (c.conj * complex_dot_product v w) = complex_dot_product (c • v) w :=
sorry

@[simp]
lemma complex_dot_product_add' {v w u : Euc} :
  complex_dot_product v (w + u) = complex_dot_product v w + complex_dot_product v u :=
sorry

@[simp]
lemma complex_dot_product_sub {v w u : Euc} :
  complex_dot_product (v - w) u = complex_dot_product v u - complex_dot_product w u :=
begin
suffices : complex_dot_product v u = complex_dot_product (v - w) u +  complex_dot_product w u,
by exact eq_sub_of_add_eq (eq.symm this),
set u' := v - w with hu,
have : v = u' + w, by {exact eq_add_of_sub_eq rfl},
rw this, apply complex_dot_product_add,
end

@[simp]
def orthogonal (v : Euc) (w : Euc) : Prop :=
(complex_dot_product v w = 0)

def complex_norm (v : Euc) := complex_dot_product v v

end vector

-- namespace subspace
--   -- variables {W : Type u'} [add_comm_group W] [vector_space ℂ W] [finite_dimensional ℂ W]

-- def is_orthogonal (S : set Euc) : subspace ℂ Euc → Prop :=
--   λ W, ∀ w ∈ W, ∀ v ∈ S, (vector.complex_dot_product v w = 0)

-- def orthogonal_complement (S : set Euc) : subspace ℂ Euc :=
-- Inf {W | is_orthogonal S W}

-- end subspace
