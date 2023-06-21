/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import linear_algebra.general_linear_group
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.special_linear_group

/-!
# The General Linear group $GL(n, R)$

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the elements of the General Linear group `general_linear_group n R`,
consisting of all invertible `n` by `n` `R`-matrices.

## Main definitions

* `matrix.general_linear_group` is the type of matrices over R which are units in the matrix ring.
* `matrix.GL_pos` gives the subgroup of matrices with
  positive determinant (over a linear ordered ring).

## Tags

matrix group, group, matrix inverse
-/

namespace matrix
universes u v
open_locale matrix
open linear_map

-- disable this instance so we do not accidentally use it in lemmas.
local attribute [-instance] special_linear_group.has_coe_to_fun

/-- `GL n R` is the group of `n` by `n` `R`-matrices with unit determinant.
Defined as a subtype of matrices-/
abbreviation general_linear_group (n : Type u) (R : Type v)
  [decidable_eq n] [fintype n] [comm_ring R] : Type* := (matrix n n R)ˣ

notation `GL` := general_linear_group

namespace general_linear_group

variables {n : Type u} [decidable_eq n] [fintype n] {R : Type v} [comm_ring R]

/-- The determinant of a unit matrix is itself a unit. -/
@[simps]
def det : GL n R →* Rˣ :=
{ to_fun := λ A,
  { val := (↑A : matrix n n R).det,
    inv := (↑(A⁻¹) : matrix n n R).det,
    val_inv := by rw [←det_mul, ←mul_eq_mul, A.mul_inv, det_one],
    inv_val := by rw [←det_mul, ←mul_eq_mul, A.inv_mul, det_one]},
  map_one' := units.ext det_one,
  map_mul' := λ A B, units.ext $ det_mul _ _ }

/--The `GL n R` and `general_linear_group R n` groups are multiplicatively equivalent-/
def to_lin : (GL n R) ≃* (linear_map.general_linear_group R (n → R)) :=
units.map_equiv to_lin_alg_equiv'.to_mul_equiv

/--Given a matrix with invertible determinant we get an element of `GL n R`-/
def mk' (A : matrix n n R) (h : invertible (matrix.det A)) : GL n R :=
unit_of_det_invertible A

/--Given a matrix with unit determinant we get an element of `GL n R`-/
noncomputable def mk'' (A : matrix n n R) (h : is_unit (matrix.det A)) : GL n R :=
nonsing_inv_unit A h

/--Given a matrix with non-zero determinant over a field, we get an element of `GL n K`-/
def mk_of_det_ne_zero {K : Type*} [field K] (A : matrix n n K) (h : matrix.det A ≠ 0) :
  GL n K :=
mk' A (invertible_of_nonzero h)

lemma ext_iff (A B : GL n R) : A = B ↔ (∀ i j, (A : matrix n n R) i j = (B : matrix n n R) i j) :=
units.ext_iff.trans matrix.ext_iff.symm

/-- Not marked `@[ext]` as the `ext` tactic already solves this. -/
lemma ext ⦃A B : GL n R⦄ (h : ∀ i j, (A : matrix n n R) i j = (B : matrix n n R) i j) :
  A = B :=
units.ext $ matrix.ext h

section coe_lemmas

variables (A B : GL n R)

@[simp] lemma coe_mul : ↑(A * B) = (↑A : matrix n n R) ⬝ (↑B : matrix n n R) := rfl

@[simp] lemma coe_one : ↑(1 : GL n R) = (1 : matrix n n R) := rfl

lemma coe_inv : ↑(A⁻¹) = (↑A : matrix n n R)⁻¹ :=
begin
  letI := A.invertible,
  exact inv_of_eq_nonsing_inv (↑A : matrix n n R),
end

/-- An element of the matrix general linear group on `(n) [fintype n]` can be considered as an
element of the endomorphism general linear group on `n → R`. -/
def to_linear : general_linear_group n R ≃* linear_map.general_linear_group R (n → R) :=
units.map_equiv matrix.to_lin_alg_equiv'.to_ring_equiv.to_mul_equiv

-- Note that without the `@` and `‹_›`, lean infers `λ a b, _inst a b` instead of `_inst` as the
-- decidability argument, which prevents `simp` from obtaining the instance by unification.
-- These `λ a b, _inst a b` terms also appear in the type of `A`, but simp doesn't get confused by
-- them so for now we do not care.
@[simp] lemma coe_to_linear :
  (@to_linear n ‹_› ‹_› _ _ A : (n → R) →ₗ[R] (n → R)) = matrix.mul_vec_lin A :=
rfl

@[simp] lemma to_linear_apply (v : n → R) :
  (@to_linear n ‹_› ‹_› _ _ A) v = matrix.mul_vec_lin ↑A v :=
rfl

end coe_lemmas

end general_linear_group

namespace special_linear_group

variables {n : Type u} [decidable_eq n] [fintype n] {R : Type v} [comm_ring R]

instance has_coe_to_general_linear_group : has_coe (special_linear_group n R) (GL n R) :=
⟨λ A, ⟨↑A, ↑(A⁻¹), congr_arg coe (mul_right_inv A), congr_arg coe (mul_left_inv A)⟩⟩

@[simp] lemma coe_to_GL_det (g : special_linear_group n R) : (g : GL n R).det = 1 :=
units.ext g.prop

end special_linear_group

section

variables {n : Type u} {R : Type v} [decidable_eq n] [fintype n] [linear_ordered_comm_ring R ]

section
variables (n R)

/-- This is the subgroup of `nxn` matrices with entries over a
linear ordered ring and positive determinant. -/
def GL_pos : subgroup (GL n R) :=
(units.pos_subgroup R).comap general_linear_group.det
end

@[simp] lemma mem_GL_pos (A : GL n R) : A ∈ GL_pos n R ↔ 0 < (A.det : R) := iff.rfl

lemma GL_pos.det_ne_zero (A : GL_pos n R) : (A : matrix n n R).det ≠ 0 := ne_of_gt A.prop

end

section has_neg

variables {n : Type u} {R : Type v} [decidable_eq n] [fintype n] [linear_ordered_comm_ring R ]
[fact (even (fintype.card n))]

/-- Formal operation of negation on general linear group on even cardinality `n` given by negating
each element. -/
instance : has_neg (GL_pos n R) :=
⟨λ g, ⟨-g, begin
    rw [mem_GL_pos, general_linear_group.coe_det_apply, units.coe_neg, det_neg,
      (fact.out $ even $ fintype.card n).neg_one_pow, one_mul],
    exact g.prop,
  end⟩⟩

@[simp] lemma GL_pos.coe_neg_GL (g : GL_pos n R) : ↑(-g) = -(g : GL n R) := rfl
@[simp] lemma GL_pos.coe_neg (g : GL_pos n R) : ↑(-g) = -(g : matrix n n R) := rfl

@[simp] lemma GL_pos.coe_neg_apply (g : GL_pos n R) (i j : n) :
  (↑(-g) : matrix n n R) i j = -((↑g : matrix n n R) i j) :=
rfl

instance : has_distrib_neg (GL_pos n R) :=
subtype.coe_injective.has_distrib_neg _ GL_pos.coe_neg_GL (GL_pos n R).coe_mul

end has_neg

namespace special_linear_group

variables {n : Type u} [decidable_eq n] [fintype n] {R : Type v} [linear_ordered_comm_ring R]

/-- `special_linear_group n R` embeds into `GL_pos n R` -/
def to_GL_pos : special_linear_group n R →* GL_pos n R :=
{ to_fun := λ A, ⟨(A : GL n R), show 0 < (↑A : matrix n n R).det, from A.prop.symm ▸ zero_lt_one⟩,
  map_one' := subtype.ext $ units.ext $ rfl,
  map_mul' := λ A₁ A₂, subtype.ext $ units.ext $ rfl }

instance : has_coe (special_linear_group n R) (GL_pos n R) := ⟨to_GL_pos⟩

lemma coe_eq_to_GL_pos : (coe : special_linear_group n R → GL_pos n R) = to_GL_pos := rfl

lemma to_GL_pos_injective :
  function.injective (to_GL_pos : special_linear_group n R → GL_pos n R) :=
(show function.injective ((coe : GL_pos n R → matrix n n R) ∘ to_GL_pos),
 from subtype.coe_injective).of_comp

/-- Coercing a `special_linear_group` via `GL_pos` and `GL` is the same as coercing striaght to a
matrix. -/
@[simp]
lemma coe_GL_pos_coe_GL_coe_matrix (g : special_linear_group n R) :
    (↑(↑(↑g : GL_pos n R) : GL n R) : matrix n n R) = ↑g := rfl

@[simp] lemma coe_to_GL_pos_to_GL_det (g : special_linear_group n R) :
  ((g : GL_pos n R) : GL n R).det = 1 :=
units.ext g.prop

variable [fact (even (fintype.card n))]

@[norm_cast] lemma coe_GL_pos_neg (g : special_linear_group n R) :
  ↑(-g) = -(↑g : GL_pos n R) := subtype.ext $ units.ext rfl

end special_linear_group

section examples

/-- The matrix [a, -b; b, a] (inspired by multiplication by a complex number); it is an element of
$GL_2(R)$ if `a ^ 2 + b ^ 2` is nonzero. -/
@[simps coe {fully_applied := ff}]
def plane_conformal_matrix {R} [field R] (a b : R) (hab : a ^ 2 + b ^ 2 ≠ 0) :
  matrix.general_linear_group (fin 2) R :=
general_linear_group.mk_of_det_ne_zero !![a, -b; b, a]
  (by simpa [det_fin_two, sq] using hab)

/- TODO: Add Iwasawa matrices `n_x=!![1,x; 0,1]`, `a_t=!![exp(t/2),0;0,exp(-t/2)]` and
  `k_θ=!![cos θ, sin θ; -sin θ, cos θ]`
-/

end examples

namespace general_linear_group
variables {n : Type u} [decidable_eq n] [fintype n] {R : Type v} [comm_ring R]

-- this section should be last to ensure we do not use it in lemmas
section coe_fn_instance

/-- This instance is here for convenience, but is not the simp-normal form. -/
instance : has_coe_to_fun (GL n R) (λ _, n → n → R) :=
{ coe := λ A, A.val }

@[simp] lemma coe_fn_eq_coe (A : GL n R) : ⇑A = (↑A : matrix n n R) := rfl

end coe_fn_instance

end general_linear_group

end matrix
