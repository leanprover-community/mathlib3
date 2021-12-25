/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.quaternion_basis
import data.complex.module
import linear_algebra.clifford_algebra.conjugation
import linear_algebra.quadratic_form.prod

/-!
# Other constructions isomorphic to Clifford Algebras

This file contains isomorphisms showing that other types are equivalent to some `clifford_algebra`.

## Rings

* `clifford_algebra_ring.equiv`: any ring is equivalent to a `clifford_algebra` over a
  zero-dimensional vector space.

## Complex numbers

* `clifford_algebra_complex.equiv`: the `complex` numbers are equivalent as an `ℝ`-algebra to a
  `clifford_algebra` over a one-dimensional vector space with a quadratic form that satisfies
  `Q (ι Q 1) = -1`.
* `clifford_algebra_complex.to_complex`: the forward direction of this equiv
* `clifford_algebra_complex.of_complex`: the reverse direction of this equiv

We show additionally that this equivalence sends `complex.conj` to `clifford_algebra.involute` and
vice-versa:

* `clifford_algebra_complex.to_complex_involute`
* `clifford_algebra_complex.of_complex_conj`

Note that in this algebra `clifford_algebra.reverse` is the identity and so the clifford conjugate
is the same as `clifford_algebra.involute`.

## Quaternion algebras

* `clifford_algebra_quaternion.equiv`: a `quaternion_algebra` over `R` is equivalent as an
  `R`-algebra to a clifford algebra over `R × R`, sending `i` to `(0, 1)` and `j` to `(1, 0)`.
* `clifford_algebra_quaternion.to_quaternion`: the forward direction of this equiv
* `clifford_algebra_quaternion.of_quaternion`: the reverse direction of this equiv

We show additionally that this equivalence sends `quaternion_algebra.conj` to the clifford conjugate
and vice-versa:

* `clifford_algebra_quaternion.to_quaternion_involute_reverse`
* `clifford_algebra_quaternion.of_quaternion_conj`

-/

open clifford_algebra

/-! ### The clifford algebra isomorphic to a ring -/
namespace clifford_algebra_ring
open_locale complex_conjugate

variables {R : Type*} [comm_ring R]

@[simp]
lemma ι_eq_zero : ι (0 : quadratic_form R unit) = 0 :=
subsingleton.elim _ _

/-- Since the vector space is empty the ring is commutative. -/
instance : comm_ring (clifford_algebra (0 : quadratic_form R unit)) :=
{ mul_comm := λ x y, begin
    induction x using clifford_algebra.induction,
    case h_grade0 : r { apply algebra.commutes, },
    case h_grade1 : x { simp, },
    case h_add : x₁ x₂ hx₁ hx₂ { rw [mul_add, add_mul, hx₁, hx₂], },
    case h_mul : x₁ x₂ hx₁ hx₂ { rw [mul_assoc, hx₂, ←mul_assoc, hx₁, ←mul_assoc], },
  end,
  ..clifford_algebra.ring _ }

lemma reverse_apply (x : clifford_algebra (0 : quadratic_form R unit)) : x.reverse = x :=
begin
  induction x using clifford_algebra.induction,
  case h_grade0 : r { exact reverse.commutes _},
  case h_grade1 : x { rw [ι_eq_zero, linear_map.zero_apply, reverse.map_zero] },
  case h_mul : x₁ x₂ hx₁ hx₂ { rw [reverse.map_mul, mul_comm, hx₁, hx₂] },
  case h_add : x₁ x₂ hx₁ hx₂ { rw [reverse.map_add, hx₁, hx₂] },
end

@[simp] lemma reverse_eq_id :
  (reverse : clifford_algebra (0 : quadratic_form R unit) →ₗ[R] _) = linear_map.id :=
linear_map.ext reverse_apply

@[simp] lemma involute_eq_id :
  (involute : clifford_algebra (0 : quadratic_form R unit) →ₐ[R] _) = alg_hom.id R _ :=
by { ext, simp }

/-- The clifford algebra over a 0-dimensional vector space is isomorphic to its scalars. -/
protected def equiv : clifford_algebra (0 : quadratic_form R unit) ≃ₐ[R] R :=
alg_equiv.of_alg_hom
  (clifford_algebra.lift (0 : quadratic_form R unit) $
    ⟨0, λ m : unit, (zero_mul (0 : R)).trans (algebra_map R _).map_zero.symm⟩)
  (algebra.of_id R _)
  (by { ext x, exact (alg_hom.commutes _ x), })
  (by { ext : 1, rw [ι_eq_zero, linear_map.comp_zero, linear_map.comp_zero], })

end clifford_algebra_ring

/-! ### The clifford algebra isomorphic to the complex numbers -/
namespace clifford_algebra_complex
open_locale complex_conjugate

/-- The quadratic form sending elements to the negation of their square. -/
def Q : quadratic_form ℝ ℝ := -quadratic_form.sq

@[simp]
lemma Q_apply (r : ℝ) : Q r = - (r * r) := rfl

/-- Intermediate result for `clifford_algebra_complex.equiv`: clifford algebras over
`clifford_algebra_complex.Q` above can be converted to `ℂ`. -/
def to_complex : clifford_algebra Q →ₐ[ℝ] ℂ :=
clifford_algebra.lift Q ⟨linear_map.to_span_singleton _ _ complex.I, λ r, begin
  dsimp [linear_map.to_span_singleton, linear_map.id],
  rw mul_mul_mul_comm,
  simp,
end⟩

@[simp]
lemma to_complex_ι (r : ℝ) : to_complex (ι Q r) = r • complex.I :=
clifford_algebra.lift_ι_apply _ _ r

/-- `clifford_algebra.involute` is analogous to `complex.conj`. -/
@[simp] lemma to_complex_involute (c : clifford_algebra Q) :
  to_complex (c.involute) = conj (to_complex c) :=
begin
  have : to_complex (involute (ι Q 1)) = conj (to_complex (ι Q 1)),
  { simp only [involute_ι, to_complex_ι, alg_hom.map_neg, one_smul, complex.conj_I] },
  suffices : to_complex.comp involute = complex.conj_ae.to_alg_hom.comp to_complex,
  { exact alg_hom.congr_fun this c },
  ext : 2,
  exact this
end

/-- Intermediate result for `clifford_algebra_complex.equiv`: `ℂ` can be converted to
`clifford_algebra_complex.Q` above can be converted to. -/
def of_complex : ℂ →ₐ[ℝ] clifford_algebra Q :=
complex.lift ⟨
  clifford_algebra.ι Q 1,
  by rw [clifford_algebra.ι_sq_scalar, Q_apply, one_mul, ring_hom.map_neg, ring_hom.map_one]⟩

@[simp]
lemma of_complex_I : of_complex complex.I = ι Q 1 :=
complex.lift_aux_apply_I _ _

@[simp] lemma to_complex_comp_of_complex : to_complex.comp of_complex = alg_hom.id ℝ ℂ :=
begin
  ext1,
  dsimp only [alg_hom.comp_apply, subtype.coe_mk, alg_hom.id_apply],
  rw [of_complex_I, to_complex_ι, one_smul],
end

@[simp] lemma to_complex_of_complex (c : ℂ) : to_complex (of_complex c) = c :=
alg_hom.congr_fun to_complex_comp_of_complex c

@[simp] lemma of_complex_comp_to_complex :
  of_complex.comp to_complex = alg_hom.id ℝ (clifford_algebra Q) :=
begin
  ext,
  dsimp only [linear_map.comp_apply, subtype.coe_mk, alg_hom.id_apply,
    alg_hom.to_linear_map_apply, alg_hom.comp_apply],
  rw [to_complex_ι, one_smul, of_complex_I],
end

@[simp] lemma of_complex_to_complex (c : clifford_algebra Q) : of_complex (to_complex c) = c :=
alg_hom.congr_fun of_complex_comp_to_complex c

/-- The clifford algebras over `clifford_algebra_complex.Q` is isomorphic as an `ℝ`-algebra to
`ℂ`. -/
@[simps]
protected def equiv : clifford_algebra Q ≃ₐ[ℝ] ℂ :=
alg_equiv.of_alg_hom to_complex of_complex to_complex_comp_of_complex of_complex_comp_to_complex

/-- The clifford algebra is commutative since it is isomorphic to the complex numbers.

TODO: prove this is true for all `clifford_algebra`s over a 1-dimensional vector space. -/
instance : comm_ring (clifford_algebra Q) :=
{ mul_comm := λ x y, clifford_algebra_complex.equiv.injective $
    by rw [alg_equiv.map_mul, mul_comm, alg_equiv.map_mul],
  .. clifford_algebra.ring _ }

/-- `reverse` is a no-op over `clifford_algebra_complex.Q`. -/
lemma reverse_apply (x : clifford_algebra Q) : x.reverse = x :=
begin
  induction x using clifford_algebra.induction,
  case h_grade0 : r { exact reverse.commutes _},
  case h_grade1 : x { rw [reverse_ι] },
  case h_mul : x₁ x₂ hx₁ hx₂ { rw [reverse.map_mul, mul_comm, hx₁, hx₂] },
  case h_add : x₁ x₂ hx₁ hx₂ { rw [reverse.map_add, hx₁, hx₂] },
end

@[simp]
lemma reverse_eq_id : (reverse : clifford_algebra Q →ₗ[ℝ] _) = linear_map.id :=
linear_map.ext reverse_apply

/-- `complex.conj` is analogous to `clifford_algebra.involute`. -/
@[simp] lemma of_complex_conj (c : ℂ) : of_complex (conj c) = (of_complex c).involute :=
clifford_algebra_complex.equiv.injective $
  by rw [equiv_apply, equiv_apply, to_complex_involute, to_complex_of_complex,
    to_complex_of_complex]

-- this name is too short for us to want it visible after `open clifford_algebra_complex`
attribute [protected] Q

end clifford_algebra_complex

/-! ### The clifford algebra isomorphic to the quaternions -/
namespace clifford_algebra_quaternion

open_locale quaternion
open quaternion_algebra

variables {R : Type*} [comm_ring R] (c₁ c₂ : R)

/-- `Q c₁ c₂` is a quadratic form over `R × R` such that `clifford_algebra (Q c₁ c₂)` is isomorphic
as an `R`-algebra to `ℍ[R,c₁,c₂]`. -/
def Q : quadratic_form R (R × R) :=
(c₁ • quadratic_form.sq).prod (c₂ • quadratic_form.sq)

@[simp]
lemma Q_apply (v : R × R) : Q c₁ c₂ v = c₁ * (v.1 * v.1) + c₂ * (v.2 * v.2) := rfl

/-- The quaternion basis vectors within the algebra. -/
@[simps i j k]
def quaternion_basis : quaternion_algebra.basis (clifford_algebra (Q c₁ c₂)) c₁ c₂ :=
{ i := ι (Q c₁ c₂) (1, 0),
  j := ι (Q c₁ c₂) (0, 1),
  k := ι (Q c₁ c₂) (1, 0) * ι (Q c₁ c₂) (0, 1),
  i_mul_i := begin
    rw [ι_sq_scalar, Q_apply, ←algebra.algebra_map_eq_smul_one],
    simp,
  end,
  j_mul_j := begin
    rw [ι_sq_scalar, Q_apply, ←algebra.algebra_map_eq_smul_one],
    simp,
  end,
  i_mul_j := rfl,
  j_mul_i := begin
    rw [eq_neg_iff_add_eq_zero, ι_mul_ι_add_swap, quadratic_form.polar],
    simp,
  end }

variables {c₁ c₂}

/-- Intermediate result of `clifford_algebra_quaternion.equiv`: clifford algebras over
`clifford_algebra_quaternion.Q` can be converted to `ℍ[R,c₁,c₂]`. -/
def to_quaternion : clifford_algebra (Q c₁ c₂) →ₐ[R] ℍ[R,c₁,c₂] :=
clifford_algebra.lift (Q c₁ c₂) ⟨
  { to_fun := λ v, (⟨0, v.1, v.2, 0⟩ : ℍ[R,c₁,c₂]),
    map_add' := λ v₁ v₂, by simp,
    map_smul' := λ r v, by ext; simp },
  λ v, begin
    dsimp,
    ext,
    all_goals {dsimp, ring},
  end⟩

@[simp]
lemma to_quaternion_ι (v : R × R) :
  to_quaternion (ι (Q c₁ c₂) v) = (⟨0, v.1, v.2, 0⟩ : ℍ[R,c₁,c₂]) :=
clifford_algebra.lift_ι_apply _ _ v

/-- The "clifford conjugate" (aka `involute ∘ reverse = reverse ∘ involute`) maps to the quaternion
conjugate. -/
lemma to_quaternion_involute_reverse (c : clifford_algebra (Q c₁ c₂)) :
  to_quaternion (involute (reverse c)) = quaternion_algebra.conj (to_quaternion c) :=
begin
  induction c using clifford_algebra.induction,
  case h_grade0 : r
  { simp only [reverse.commutes, alg_hom.commutes, quaternion_algebra.coe_algebra_map,
      quaternion_algebra.conj_coe], },
  case h_grade1 : x
  { rw [reverse_ι, involute_ι, to_quaternion_ι, alg_hom.map_neg, to_quaternion_ι,
      quaternion_algebra.neg_mk, conj_mk, neg_zero], },
  case h_mul : x₁ x₂ hx₁ hx₂
  { simp only [reverse.map_mul, alg_hom.map_mul, hx₁, hx₂, quaternion_algebra.conj_mul] },
  case h_add : x₁ x₂ hx₁ hx₂
  { simp only [reverse.map_add, alg_hom.map_add, hx₁, hx₂, quaternion_algebra.conj_add] },
end

/-- Map a quaternion into the clifford algebra. -/
def of_quaternion : ℍ[R,c₁,c₂] →ₐ[R] clifford_algebra (Q c₁ c₂) :=
(quaternion_basis c₁ c₂).lift_hom

@[simp] lemma of_quaternion_mk (a₁ a₂ a₃ a₄ : R) :
  of_quaternion (⟨a₁, a₂, a₃, a₄⟩ : ℍ[R,c₁,c₂])
    = algebra_map R _ a₁
    + a₂ • ι (Q c₁ c₂) (1, 0)
    + a₃ • ι (Q c₁ c₂) (0, 1)
    + a₄ • (ι (Q c₁ c₂) (1, 0) * ι (Q c₁ c₂) (0, 1)) := rfl

@[simp]
lemma of_quaternion_comp_to_quaternion :
  of_quaternion.comp to_quaternion = alg_hom.id R (clifford_algebra (Q c₁ c₂)) :=
begin
  ext : 1,
  dsimp, -- before we end up with two goals and have to do this twice
  ext,
  all_goals
  { dsimp,
    rw to_quaternion_ι,
    dsimp,
    simp only [to_quaternion_ι, zero_smul, one_smul, zero_add, add_zero, ring_hom.map_zero], },
end

@[simp] lemma of_quaternion_to_quaternion (c : clifford_algebra (Q c₁ c₂)) :
  of_quaternion (to_quaternion c) = c :=
alg_hom.congr_fun
  (of_quaternion_comp_to_quaternion : _ = alg_hom.id R (clifford_algebra (Q c₁ c₂))) c

@[simp]
lemma to_quaternion_comp_of_quaternion :
  to_quaternion.comp of_quaternion = alg_hom.id R ℍ[R,c₁,c₂] :=
begin
  apply quaternion_algebra.lift.symm.injective,
  ext1; dsimp [quaternion_algebra.basis.lift]; simp,
end

@[simp] lemma to_quaternion_of_quaternion (q : ℍ[R,c₁,c₂]) : to_quaternion (of_quaternion q) = q :=
alg_hom.congr_fun (to_quaternion_comp_of_quaternion : _ = alg_hom.id R ℍ[R,c₁,c₂]) q

/-- The clifford algebra over `clifford_algebra_quaternion.Q c₁ c₂` is isomorphic as an `R`-algebra
to `ℍ[R,c₁,c₂]`. -/
@[simps]
protected def equiv : clifford_algebra (Q c₁ c₂) ≃ₐ[R] ℍ[R,c₁,c₂] :=
alg_equiv.of_alg_hom to_quaternion of_quaternion
  to_quaternion_comp_of_quaternion
  of_quaternion_comp_to_quaternion

/-- The quaternion conjugate maps to the "clifford conjugate" (aka
`involute ∘ reverse = reverse ∘ involute`). -/
@[simp] lemma of_quaternion_conj (q : ℍ[R,c₁,c₂]) :
  of_quaternion (q.conj) = (of_quaternion q).reverse.involute :=
clifford_algebra_quaternion.equiv.injective $
  by rw [equiv_apply, equiv_apply, to_quaternion_involute_reverse, to_quaternion_of_quaternion,
    to_quaternion_of_quaternion]

-- this name is too short for us to want it visible after `open clifford_algebra_quaternion`
attribute [protected] Q

end clifford_algebra_quaternion
