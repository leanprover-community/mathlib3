/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra.conjugation
import linear_algebra.clifford_algebra.even
import linear_algebra.quadratic_form.prod
/-!
# Isomorphisms with the even subalgebra of a Clifford algebra

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides some notable isomorphisms regarding the even subalgebra, `clifford_algebra.even`.

## Main definitions

* `clifford_algebra.equiv_even`: Every Clifford algebra is isomorphic as an algebra to the even
  subalgebra of a Clifford algebra with one more dimension.
  * `clifford_algebra.even_equiv.Q'`: The quadratic form used by this "one-up" algebra.
  * `clifford_algebra.to_even`: The simp-normal form of the forward direction of this isomorphism.
  * `clifford_algebra.of_even`: The simp-normal form of the reverse direction of this isomorphism.

* `clifford_algebra.even_equiv_even_neg`: Every even subalgebra is isomorphic to the even subalgebra
  of the Clifford algebra with negated quadratic form.
  * `clifford_algebra.even_to_neg`: The simp-normal form of each direction of this isomorphism.

## Main results

* `clifford_algebra.coe_to_even_reverse_involute`: the behavior of `clifford_algebra.to_even` on the
  "Clifford conjugate", that is `clifford_algebra.reverse` composed with
  `clifford_algebra.involute`.
-/

namespace clifford_algebra

variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]
variables (Q : quadratic_form R M)

/-! ### Constructions needed for `clifford_algebra.equiv_even` -/

namespace equiv_even

/-- The quadratic form on the augmented vector space `M × R` sending `v + r•e0` to `Q v - r^2`. -/
@[reducible]
def Q' : quadratic_form R (M × R) := (Q.prod $ -@quadratic_form.sq R _)

lemma Q'_apply (m : M × R) : Q' Q m = Q m.1 - m.2 * m.2 := (sub_eq_add_neg _ _).symm

/-- The unit vector in the new dimension -/
def e0 : clifford_algebra (Q' Q) := ι (Q' Q) (0, 1)

/-- The embedding from the existing vector space -/
def v : M →ₗ[R] clifford_algebra (Q' Q) := (ι (Q' Q)) ∘ₗ linear_map.inl _ _ _

lemma ι_eq_v_add_smul_e0 (m : M) (r : R) : ι (Q' Q) (m, r) = v Q m + r • e0 Q :=
by rw [e0, v, linear_map.comp_apply, linear_map.inl_apply, ←linear_map.map_smul, prod.smul_mk,
  smul_zero, smul_eq_mul, mul_one, ←linear_map.map_add, prod.mk_add_mk, zero_add, add_zero]

lemma e0_mul_e0 : e0 Q * e0 Q = -1 :=
(ι_sq_scalar _ _).trans $ by simp

lemma v_sq_scalar (m : M) : v Q m * v Q m = algebra_map _ _ (Q m) :=
(ι_sq_scalar _ _).trans $ by simp

lemma neg_e0_mul_v (m : M) : -(e0 Q * v Q m) = v Q m * e0 Q :=
begin
  refine neg_eq_of_add_eq_zero_right ((ι_mul_ι_add_swap _ _).trans _),
  dsimp [quadratic_form.polar],
  simp only [add_zero, mul_zero, mul_one, zero_add, neg_zero, quadratic_form.map_zero,
    add_sub_cancel, sub_self, map_zero, zero_sub],
end

lemma neg_v_mul_e0 (m : M) : -(v Q m * e0 Q) = e0 Q * v Q m :=
begin
  rw neg_eq_iff_eq_neg,
  exact (neg_e0_mul_v _ m).symm
end

@[simp] lemma e0_mul_v_mul_e0 (m : M) : e0 Q * v Q m * e0 Q = v Q m :=
by rw [←neg_v_mul_e0, ←neg_mul, mul_assoc, e0_mul_e0, mul_neg_one, neg_neg]

@[simp] lemma reverse_v (m : M) : reverse (v Q m) = v Q m := reverse_ι _
@[simp] lemma involute_v (m : M) : involute (v Q m) = -v Q m := involute_ι _

@[simp] lemma reverse_e0 : reverse (e0 Q) = e0 Q := reverse_ι _
@[simp] lemma involute_e0 : involute (e0 Q) = -e0 Q := involute_ι _

end equiv_even

open equiv_even

/-- The embedding from the smaller algebra into the new larger one. -/
def to_even : clifford_algebra Q →ₐ[R] clifford_algebra.even (Q' Q) :=
begin
  refine clifford_algebra.lift Q ⟨_, λ m, _⟩,
  { refine linear_map.cod_restrict _ _ (λ m, submodule.mem_supr_of_mem ⟨2, rfl⟩ _),
    exact (linear_map.mul_left R $ e0 Q).comp (v Q),
    rw [subtype.coe_mk, pow_two],
    exact submodule.mul_mem_mul (linear_map.mem_range_self _ _) (linear_map.mem_range_self _ _), },
  { ext1,
    dsimp only [subalgebra.coe_mul, linear_map.cod_restrict_apply, linear_map.comp_apply,
      linear_map.mul_left_apply, linear_map.inl_apply, subalgebra.coe_algebra_map],
    rw [←mul_assoc, e0_mul_v_mul_e0, v_sq_scalar] }
end

@[simp]
lemma to_even_ι (m : M) : (to_even Q (ι Q m) : clifford_algebra (Q' Q)) = e0 Q * v Q m :=
begin
  rw [to_even, clifford_algebra.lift_ι_apply, linear_map.cod_restrict_apply],
  refl,
end

/-- The embedding from the even subalgebra with an extra dimension into the original algebra. -/
def of_even : clifford_algebra.even (Q' Q) →ₐ[R] clifford_algebra Q :=
begin
  /-
  Recall that we need:
   * `f ⟨0,1⟩ ⟨x,0⟩ = ι x`
   * `f ⟨x,0⟩ ⟨0,1⟩ = -ι x`
   * `f ⟨x,0⟩ ⟨y,0⟩ = ι x * ι y`
   * `f ⟨0,1⟩ ⟨0,1⟩ = -1`
  -/
  let f : (M × R) →ₗ[R] (M × R) →ₗ[R] clifford_algebra Q :=
  ((algebra.lmul R (clifford_algebra Q)).to_linear_map.comp
    $ ((ι Q).comp (linear_map.fst _ _ _)) +
      (algebra.linear_map R _).comp (linear_map.snd _ _ _)).compl₂
    (((ι Q).comp (linear_map.fst _ _ _)) - (algebra.linear_map R _).comp (linear_map.snd _ _ _)),
  have f_apply :
    ∀ x y, f x y = (ι Q x.1 + algebra_map R _ x.2) * (ι Q y.1 - algebra_map R _ y.2) :=
    λ x y, rfl,
  have hc : ∀ (r : R) (x : clifford_algebra Q), commute (algebra_map _ _ r) x := algebra.commutes,
  have hm : ∀ m : M × R,
    ι Q m.1 * ι Q m.1 - algebra_map R _ m.2 * algebra_map R _ m.2 = algebra_map R _ (Q' Q m),
  { intro m,
    rw [ι_sq_scalar, ←ring_hom.map_mul, ←ring_hom.map_sub,
      sub_eq_add_neg, Q'_apply, sub_eq_add_neg] },
  refine even.lift (Q' Q) ⟨f, _, _⟩; simp_rw [f_apply],
  { intro m,
    rw [←(hc _ _).symm.mul_self_sub_mul_self_eq, hm] },
  { intros m₁ m₂ m₃,
    rw [←mul_smul_comm, ←mul_assoc, mul_assoc(_ + _), ←(hc _ _).symm.mul_self_sub_mul_self_eq',
      algebra.smul_def, ←mul_assoc, hm] },
end

lemma of_even_ι (x y : M × R) :
  of_even Q ((even.ι _).bilin x y) =
    (ι Q x.1 + algebra_map R _ x.2) * (ι Q y.1 - algebra_map R _ y.2) :=
even.lift_ι _ _ _ _

lemma to_even_comp_of_even : (to_even Q).comp (of_even Q) = alg_hom.id R _ :=
even.alg_hom_ext (Q' Q) $ even_hom.ext _ _ $ linear_map.ext $ λ m₁, linear_map.ext $ λ m₂,
  subtype.ext $
  let ⟨m₁, r₁⟩ := m₁, ⟨m₂, r₂⟩ := m₂ in
  calc  ↑(to_even Q (of_even Q ((even.ι (Q' Q)).bilin (m₁, r₁) (m₂, r₂))))
      = (e0 Q * v Q m₁ + algebra_map R _ r₁) * (e0 Q * v Q m₂ - algebra_map R _ r₂) :
        by rw [of_even_ι, alg_hom.map_mul, alg_hom.map_add, alg_hom.map_sub, alg_hom.commutes,
             alg_hom.commutes, subalgebra.coe_mul, subalgebra.coe_add, subalgebra.coe_sub,
             to_even_ι, to_even_ι, subalgebra.coe_algebra_map, subalgebra.coe_algebra_map]
  ... = e0 Q * v Q m₁ * (e0 Q * v Q m₂) + r₁ • e0 Q * v Q m₂ - r₂ • e0 Q * v Q m₁
          - algebra_map R _ (r₁ * r₂) :
        by rw [mul_sub, add_mul, add_mul, ←algebra.commutes, ←algebra.smul_def, ←map_mul,
               ←algebra.smul_def, sub_add_eq_sub_sub, smul_mul_assoc, smul_mul_assoc]
  ... = v Q m₁ * v Q m₂ + r₁ • e0 Q * v Q m₂ + v Q m₁ * r₂ • e0 Q + (r₁ • e0 Q) * r₂ • e0 Q :
        have h1 : e0 Q * v Q m₁ * (e0 Q * v Q m₂) = v Q m₁ * v Q m₂,
          by rw [←mul_assoc, e0_mul_v_mul_e0],
        have h2 : -(r₂ • e0 Q * v Q m₁) = v Q m₁ * r₂ • e0 Q,
          by rw [mul_smul_comm, smul_mul_assoc, ←smul_neg, neg_e0_mul_v],
        have h3 : - algebra_map R _ (r₁ * r₂) = (r₁ • e0 Q) * r₂ • e0 Q,
          by rw [algebra.algebra_map_eq_smul_one, smul_mul_smul, e0_mul_e0, smul_neg],
        by rw [sub_eq_add_neg, sub_eq_add_neg, h1, h2, h3]
  ... = ι _ (m₁, r₁) * ι _ (m₂, r₂) :
        by rw [ι_eq_v_add_smul_e0, ι_eq_v_add_smul_e0, mul_add, add_mul, add_mul, add_assoc]

lemma of_even_comp_to_even :
  (of_even Q).comp (to_even Q) = alg_hom.id R _ :=
clifford_algebra.hom_ext $ linear_map.ext $ λ m,
  calc  of_even Q (to_even Q (ι Q m))
      = of_even Q ⟨_, (to_even Q (ι Q m)).prop⟩ : by rw subtype.coe_eta
  ... = (ι Q 0 + algebra_map R _ 1) * (ι Q m - algebra_map R _ 0) : begin
          simp_rw to_even_ι,
          exact of_even_ι Q _ _,
        end
  ... = ι Q m : by rw [map_one, map_zero, map_zero, sub_zero, zero_add, one_mul]

/-- Any clifford algebra is isomorphic to the even subalgebra of a clifford algebra with an extra
dimension (that is, with vector space `M × R`), with a quadratic form evaluating to `-1` on that new
basis vector. -/
@[simps]
def equiv_even : clifford_algebra Q ≃ₐ[R] clifford_algebra.even (Q' Q) :=
alg_equiv.of_alg_hom
  (to_even Q)
  (of_even Q)
  (to_even_comp_of_even Q)
  (of_even_comp_to_even Q)

/-- The representation of the clifford conjugate (i.e. the reverse of the involute) in the even
subalgebra is just the reverse of the representation. -/
lemma coe_to_even_reverse_involute (x : clifford_algebra Q) :
  ↑(to_even Q (reverse (involute x))) = reverse (to_even Q x : clifford_algebra (Q' Q)) :=
begin
  induction x using clifford_algebra.induction,
  case h_grade0 : r { simp only [alg_hom.commutes, subalgebra.coe_algebra_map, reverse.commutes] },
  case h_grade1 : m
  { simp only [involute_ι, subalgebra.coe_neg, to_even_ι, reverse.map_mul,
      reverse_v, reverse_e0, reverse_ι, neg_e0_mul_v, map_neg] },
  case h_mul : x y hx hy { simp only [map_mul, subalgebra.coe_mul, reverse.map_mul, hx, hy] },
  case h_add : x y hx hy { simp only [map_add, subalgebra.coe_add, hx, hy] },
end

/-! ### Constructions needed for `clifford_algebra.even_equiv_even_neg` -/

/-- One direction of `clifford_algebra.even_equiv_even_neg` -/
def even_to_neg (Q' : quadratic_form R M) (h : Q' = -Q) :
  clifford_algebra.even Q →ₐ[R] clifford_algebra.even Q' :=
even.lift Q
  { bilin := -(even.ι Q' : _).bilin,
    contract := λ m, by simp_rw [linear_map.neg_apply, even_hom.contract, h,
                                 quadratic_form.neg_apply, map_neg, neg_neg],
    contract_mid := λ m₁ m₂ m₃,
      by simp_rw [linear_map.neg_apply, neg_mul_neg, even_hom.contract_mid, h,
                  quadratic_form.neg_apply, smul_neg, neg_smul] }

@[simp] lemma even_to_neg_ι (Q' : quadratic_form R M) (h : Q' = -Q) (m₁ m₂ : M) :
  even_to_neg Q Q' h ((even.ι Q).bilin m₁ m₂) = -(even.ι Q').bilin m₁ m₂ :=
even.lift_ι _ _ m₁ m₂

lemma even_to_neg_comp_even_to_neg (Q' : quadratic_form R M)
  (h : Q' = -Q) (h' : Q = -Q') :
  (even_to_neg Q' Q h').comp (even_to_neg Q Q' h) = alg_hom.id R _ :=
begin
  ext m₁ m₂ : 4,
  dsimp only [even_hom.compr₂_bilin, linear_map.compr₂_apply, alg_hom.to_linear_map_apply,
              alg_hom.comp_apply, alg_hom.id_apply],
  rw [even_to_neg_ι, map_neg, even_to_neg_ι, neg_neg]
end

/-- The even subalgebras of the algebras with quadratic form `Q` and `-Q` are isomorphic.

Stated another way, `𝒞ℓ⁺(p,q,r)` and `𝒞ℓ⁺(q,p,r)` are isomorphic. -/
@[simps]
def even_equiv_even_neg : clifford_algebra.even Q ≃ₐ[R] clifford_algebra.even (-Q) :=
alg_equiv.of_alg_hom
  (even_to_neg Q _ rfl)
  (even_to_neg (-Q) _ (neg_neg _).symm)
  (even_to_neg_comp_even_to_neg _ _ _ _)
  (even_to_neg_comp_even_to_neg _ _ _ _)

end clifford_algebra
