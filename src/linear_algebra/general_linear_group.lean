/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import linear_algebra.matrix
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.special_linear_group
import linear_algebra.determinant

/-!
# The General Linear group $GL(n, R)$
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

/-- `GL n R` is the group of `n` by `n` `R`-matrices with unit determinant.
Defined as a subtype of matrices-/
abbreviation general_linear_group (n : Type u) (R : Type v)
  [decidable_eq n] [fintype n] [comm_ring R] : Type* := units (matrix n n R)

notation `GL` := general_linear_group

namespace general_linear_group

variables {n : Type u} [decidable_eq n] [fintype n] {R : Type v} [comm_ring R]

/-- The determinant of a unit matrix is itself a unit. -/
@[simps]
def det : GL n R →* units R :=
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

instance coe_fun : has_coe_to_fun (GL n R) (λ _, n → n → R) :=
{ coe := λ A, A.val }

lemma ext_iff (A B : GL n R) : A = B ↔ (∀ i j, (A : matrix n n R) i j = (B : matrix n n R) i j) :=
units.ext_iff.trans matrix.ext_iff.symm

/-- Not marked `@[ext]` as the `ext` tactic already solves this. -/
lemma ext ⦃A B : GL n R⦄ (h : ∀ i j, (A : matrix n n R) i j = (B : matrix n n R) i j) :
  A = B :=
units.ext $ matrix.ext h

section coe_lemmas

variables (A B : GL n R)

@[simp] lemma coe_fn_eq_coe : ⇑A = (↑A : matrix n n R) := rfl

@[simp] lemma coe_mul : ↑(A * B) = (↑A : matrix n n R) ⬝ (↑B : matrix n n R) := rfl

@[simp] lemma coe_one : ↑(1 : GL n R) = (1 : matrix n n R) := rfl

lemma coe_inv : ↑(A⁻¹) = (↑A : matrix n n R)⁻¹ :=
begin
  letI := A.invertible,
  exact inv_eq_nonsing_inv_of_invertible (↑A : matrix n n R),
end

end coe_lemmas

end general_linear_group

namespace special_linear_group

variables {n : Type u} [decidable_eq n] [fintype n] {R : Type v} [comm_ring R]

instance has_coe_to_general_linear_group : has_coe (special_linear_group n R) (GL n R) :=
⟨λ A, ⟨↑A, ↑(A⁻¹), congr_arg coe (mul_right_inv A), congr_arg coe (mul_left_inv A)⟩⟩

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
end

section has_neg

variables {n : Type u} {R : Type v} [decidable_eq n] [fintype n] [linear_ordered_comm_ring R ]
[fact (even (fintype.card n))]

/-- Formal operation of negation on general linear group on even cardinality `n` given by negating
each element. -/
instance : has_neg (GL_pos n R) :=
⟨λ g,
   ⟨- g,
  begin
    simp only [mem_GL_pos, general_linear_group.coe_det_apply, units.coe_neg],
    have := det_smul g (-1),
    simp only [general_linear_group.coe_fn_eq_coe, one_smul, coe_fn_coe_base', neg_smul] at this,
    rw this,
    simp [nat.neg_one_pow_of_even (fact.out (even (fintype.card n)))],
    have gdet := g.property,
    simp only [mem_GL_pos, general_linear_group.coe_det_apply, subtype.val_eq_coe] at gdet,
    exact gdet,
  end⟩⟩

@[simp] lemma GL_pos_coe_neg (g : GL_pos n R) : ↑(- g) = - (↑g : matrix n n R) :=
rfl

@[simp]lemma GL_pos_neg_elt (g : GL_pos n R): ∀ i j, ( ↑(-g): matrix n n R) i j= - (g i j):=
begin
  simp [coe_fn_coe_base'],
end

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

end special_linear_group
end matrix
