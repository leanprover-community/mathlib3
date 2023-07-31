/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import linear_algebra.exterior_algebra.basic
import linear_algebra.clifford_algebra.fold
import linear_algebra.clifford_algebra.conjugation

/-!
# Contraction in Clifford Algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains some of the results from [grinberg_clifford_2016][].
The key result is `clifford_algebra.equiv_exterior`.

## Main definitions

* `clifford_algebra.contract_left`: contract a multivector by a `module.dual R M` on the left.
* `clifford_algebra.contract_right`: contract a multivector by a `module.dual R M` on the right.
* `clifford_algebra.change_form`: convert between two algebras of different quadratic form, sending
  vectors to vectors. The difference of the quadratic forms must be a bilinear form.
* `clifford_algebra.equiv_exterior`: in characteristic not-two, the `clifford_algebra Q` is
  isomorphic as a module to the exterior algebra.

## Implementation notes

This file somewhat follows [grinberg_clifford_2016][], although we are missing some of the induction
principles needed to prove many of the results. Here, we avoid the quotient-based approach described
in [grinberg_clifford_2016][], instead directly constructing our objects using the universal
property.

Note that [grinberg_clifford_2016][] concludes that its contents are not novel, and are in fact just
a rehash of parts of [bourbaki2007][]; we should at some point consider swapping our references to
refer to the latter.

Within this file, we use the local notation
* `x ⌊ d` for `contract_right x d`
* `d ⌋ x` for `contract_left d x`

-/

universes u1 u2 u3

variables {R : Type u1} [comm_ring R]
variables {M : Type u2} [add_comm_group M] [module R M]
variables (Q : quadratic_form R M)

namespace clifford_algebra

section contract_left

variables (d d' : module.dual R M)

/-- Auxiliary construction for `clifford_algebra.contract_left` -/
@[simps]
def contract_left_aux (d : module.dual R M) :
  M →ₗ[R] clifford_algebra Q × clifford_algebra Q →ₗ[R] clifford_algebra Q :=
begin
  have v_mul := (algebra.lmul R (clifford_algebra Q)).to_linear_map ∘ₗ (ι Q),
  exact d.smul_right (linear_map.fst _ (clifford_algebra Q) (clifford_algebra Q)) -
        v_mul.compl₂ (linear_map.snd _ (clifford_algebra Q) _),
end

lemma contract_left_aux_contract_left_aux (v : M) (x : clifford_algebra Q)
  (fx : clifford_algebra Q) :
  contract_left_aux Q d v (ι Q v * x, contract_left_aux Q d v (x, fx)) = Q v • fx :=
begin
  simp only [contract_left_aux_apply_apply],
  rw [mul_sub, ←mul_assoc, ι_sq_scalar, ←algebra.smul_def, ←sub_add, mul_smul_comm, sub_self,
    zero_add],
end

variables {Q}

/-- Contract an element of the clifford algebra with an element `d : module.dual R M` from the left.

Note that $v ⌋ x$ is spelt `contract_left (Q.associated v) x`.

This includes [grinberg_clifford_2016][] Theorem 10.75 -/
def contract_left : module.dual R M →ₗ[R] clifford_algebra Q →ₗ[R] clifford_algebra Q :=
{ to_fun := λ d, foldr' Q (contract_left_aux Q d) (contract_left_aux_contract_left_aux Q d) 0,
  map_add' := λ d₁ d₂, linear_map.ext $ λ x, begin
    rw linear_map.add_apply,
    induction x using clifford_algebra.left_induction with r x y hx hy m x hx,
    { simp_rw [foldr'_algebra_map, smul_zero, zero_add] },
    { rw [map_add, map_add, map_add, add_add_add_comm, hx, hy] },
    { rw [foldr'_ι_mul, foldr'_ι_mul, foldr'_ι_mul, hx],
      dsimp only [contract_left_aux_apply_apply],
      rw [sub_add_sub_comm, mul_add, linear_map.add_apply, add_smul] }
  end,
  map_smul' := λ c d, linear_map.ext $ λ x,  begin
    rw [linear_map.smul_apply, ring_hom.id_apply],
    induction x using clifford_algebra.left_induction with r x y hx hy m x hx,
    { simp_rw [foldr'_algebra_map, smul_zero] },
    { rw [map_add, map_add, smul_add, hx, hy] },
    { rw [foldr'_ι_mul, foldr'_ι_mul, hx],
      dsimp only [contract_left_aux_apply_apply],
      rw [linear_map.smul_apply, smul_assoc, mul_smul_comm, smul_sub], }
  end }

/-- Contract an element of the clifford algebra with an element `d : module.dual R M` from the
right.

Note that $x ⌊ v$ is spelt `contract_right x (Q.associated v)`.

This includes [grinberg_clifford_2016][] Theorem 16.75 -/
def contract_right : clifford_algebra Q →ₗ[R] module.dual R M →ₗ[R] clifford_algebra Q :=
linear_map.flip (linear_map.compl₂ (linear_map.compr₂ contract_left reverse) reverse)

lemma contract_right_eq (x : clifford_algebra Q) :
  contract_right x d = reverse (contract_left d $ reverse x) := rfl

local infix `⌋`:70 := contract_left
local infix `⌊`:70 := contract_right

/-- This is [grinberg_clifford_2016][] Theorem 6  -/
lemma contract_left_ι_mul (a : M) (b : clifford_algebra Q) :
  d ⌋ (ι Q a * b) = d a • b - ι Q a * (d ⌋ b) :=
foldr'_ι_mul _ _ _ _ _ _

/-- This is [grinberg_clifford_2016][] Theorem 12  -/
lemma contract_right_mul_ι (a : M) (b : clifford_algebra Q) :
  (b * ι Q a) ⌊ d = d a • b - (b ⌊ d) * ι Q a :=
by rw [contract_right_eq, reverse.map_mul, reverse_ι, contract_left_ι_mul, map_sub, map_smul,
    reverse_reverse, reverse.map_mul, reverse_ι, contract_right_eq]

lemma contract_left_algebra_map_mul (r : R) (b : clifford_algebra Q) :
  d ⌋ (algebra_map _ _ r * b) = algebra_map _ _ r * (d ⌋ b) :=
by rw [←algebra.smul_def, map_smul, algebra.smul_def]

lemma contract_left_mul_algebra_map (a : clifford_algebra Q) (r : R) :
  d ⌋ (a * algebra_map _ _ r) = (d ⌋ a) * algebra_map _ _ r :=
by rw [←algebra.commutes, contract_left_algebra_map_mul, algebra.commutes]

lemma contract_right_algebra_map_mul (r : R) (b : clifford_algebra Q) :
  (algebra_map _ _ r * b) ⌊ d = algebra_map _ _ r * (b ⌊ d) :=
by rw [←algebra.smul_def, linear_map.map_smul₂, algebra.smul_def]

lemma contract_right_mul_algebra_map (a : clifford_algebra Q) (r : R) :
  (a * algebra_map _ _ r) ⌊ d = (a ⌊ d) * algebra_map _ _ r :=
by rw [←algebra.commutes, contract_right_algebra_map_mul, algebra.commutes]

variables (Q)

@[simp] lemma contract_left_ι (x : M) : d ⌋ ι Q x = algebra_map R _ (d x) :=
(foldr'_ι _ _ _ _ _).trans $
  by simp_rw [contract_left_aux_apply_apply, mul_zero, sub_zero, algebra.algebra_map_eq_smul_one]

@[simp] lemma contract_right_ι (x : M) : ι Q x ⌊ d = algebra_map R _ (d x) :=
by rw [contract_right_eq, reverse_ι, contract_left_ι, reverse.commutes]

@[simp] lemma contract_left_algebra_map (r : R) :
  d ⌋ (algebra_map R (clifford_algebra Q) r) = 0 :=
(foldr'_algebra_map _ _ _ _ _).trans $ smul_zero _

@[simp] lemma contract_right_algebra_map (r : R) :
  (algebra_map R (clifford_algebra Q) r) ⌊ d = 0 :=
by rw [contract_right_eq, reverse.commutes, contract_left_algebra_map, map_zero]

@[simp] lemma contract_left_one : d ⌋ (1 : clifford_algebra Q) = 0 :=
by simpa only [map_one] using contract_left_algebra_map Q d 1

@[simp] lemma contract_right_one : (1 : clifford_algebra Q) ⌊ d = 0 :=
by simpa only [map_one] using contract_right_algebra_map Q d 1

variables {Q}

/-- This is [grinberg_clifford_2016][] Theorem 7 -/
lemma contract_left_contract_left (x : clifford_algebra Q) :
  d ⌋ (d ⌋ x) = 0 :=
begin
  induction x using clifford_algebra.left_induction with r x y hx hy m x hx,
  { simp_rw [contract_left_algebra_map, map_zero] },
  { rw [map_add, map_add, hx, hy, add_zero] },
  { rw [contract_left_ι_mul, map_sub, contract_left_ι_mul, hx, linear_map.map_smul, mul_zero,
      sub_zero, sub_self], }
end

/-- This is [grinberg_clifford_2016][] Theorem 13 -/
lemma contract_right_contract_right (x : clifford_algebra Q) :
  (x ⌊ d) ⌊ d = 0 :=
by rw [contract_right_eq, contract_right_eq, reverse_reverse, contract_left_contract_left,
  map_zero]

/-- This is [grinberg_clifford_2016][] Theorem 8 -/
lemma contract_left_comm (x : clifford_algebra Q) : d ⌋ (d' ⌋ x) = -(d' ⌋ (d ⌋ x)) :=
begin
  induction x using clifford_algebra.left_induction with r x y hx hy m x hx,
  { simp_rw [contract_left_algebra_map, map_zero, neg_zero] },
  { rw [map_add, map_add, map_add, map_add, hx, hy, neg_add] },
  { simp only [contract_left_ι_mul, map_sub, linear_map.map_smul],
    rw [neg_sub, sub_sub_eq_add_sub, hx, mul_neg, ←sub_eq_add_neg] }
end

/-- This is [grinberg_clifford_2016][] Theorem 14 -/
lemma contract_right_comm (x : clifford_algebra Q) : (x ⌊ d) ⌊ d' = -((x ⌊ d') ⌊ d) :=
by rw [contract_right_eq, contract_right_eq, contract_right_eq, contract_right_eq,
  reverse_reverse, reverse_reverse, contract_left_comm, map_neg]

/- TODO:
lemma contract_right_contract_left (x : clifford_algebra Q) : (d ⌋ x) ⌊ d' = d ⌋ (x ⌊ d') :=
-/

end contract_left

local infix `⌋`:70 := contract_left
local infix `⌊`:70 := contract_right

/-- Auxiliary construction for `clifford_algebra.change_form` -/
@[simps]
def change_form_aux (B : bilin_form R M) : M →ₗ[R] clifford_algebra Q →ₗ[R] clifford_algebra Q :=
begin
  have v_mul := (algebra.lmul R (clifford_algebra Q)).to_linear_map ∘ₗ ι Q,
  exact v_mul - (contract_left ∘ₗ B.to_lin) ,
end

lemma change_form_aux_change_form_aux (B : bilin_form R M) (v : M) (x : clifford_algebra Q) :
  change_form_aux Q B v (change_form_aux Q B v x) = (Q v - B v v) • x :=
begin
  simp only [change_form_aux_apply_apply],
  rw [mul_sub, ←mul_assoc, ι_sq_scalar, map_sub, contract_left_ι_mul, ←sub_add, sub_sub_sub_comm,
    ←algebra.smul_def, bilin_form.to_lin_apply, sub_self, sub_zero, contract_left_contract_left,
    add_zero, sub_smul],
end

variables {Q}

variables {Q' Q'' : quadratic_form R M} {B B' : bilin_form R M}
variables (h : B.to_quadratic_form = Q' - Q) (h' : B'.to_quadratic_form = Q'' - Q')

/-- Convert between two algebras of different quadratic form, sending vector to vectors, scalars to
scalars, and adjusting products by a contraction term.

This is $\lambda_B$ from [bourbaki2007][] $9 Lemma 2. -/
def change_form (h : B.to_quadratic_form = Q' - Q) :
  clifford_algebra Q →ₗ[R] clifford_algebra Q' :=
foldr Q (change_form_aux Q' B) (λ m x, (change_form_aux_change_form_aux Q' B m x).trans $
  begin
    dsimp [←bilin_form.to_quadratic_form_apply],
    rw [h, quadratic_form.sub_apply, sub_sub_cancel],
  end) 1

/-- Auxiliary lemma used as an argument to `clifford_algebra.change_form` -/
lemma change_form.zero_proof : (0 : bilin_form R M).to_quadratic_form = Q - Q :=
(sub_self _).symm

/-- Auxiliary lemma used as an argument to `clifford_algebra.change_form` -/
lemma change_form.add_proof : (B + B').to_quadratic_form = Q'' - Q :=
(congr_arg2 (+) h h').trans $ sub_add_sub_cancel' _ _ _

/-- Auxiliary lemma used as an argument to `clifford_algebra.change_form` -/
lemma change_form.neg_proof : (-B).to_quadratic_form = Q - Q' :=
(congr_arg has_neg.neg h).trans $ neg_sub _ _

lemma change_form.associated_neg_proof [invertible (2 : R)] :
  (-Q).associated.to_quadratic_form = 0 - Q :=
by simp [quadratic_form.to_quadratic_form_associated]

@[simp]
lemma change_form_algebra_map (r : R) : change_form h (algebra_map R _ r) = algebra_map R _ r :=
(foldr_algebra_map _ _ _ _ _).trans $ eq.symm $ algebra.algebra_map_eq_smul_one r

@[simp] lemma change_form_one : change_form h (1 : clifford_algebra Q) = 1 :=
by simpa using change_form_algebra_map h (1 : R)

@[simp]
lemma change_form_ι (m : M) : change_form h (ι _ m) = ι _ m :=
(foldr_ι _ _ _ _ _).trans $ eq.symm $
  by rw [change_form_aux_apply_apply, mul_one, contract_left_one, sub_zero]

lemma change_form_ι_mul (m : M) (x : clifford_algebra Q) :
  change_form h (ι _ m * x) = ι _ m * change_form h x - bilin_form.to_lin B m ⌋ change_form h x :=
(foldr_mul _ _ _ _ _ _).trans $ begin rw foldr_ι, refl, end

lemma change_form_ι_mul_ι (m₁ m₂ : M) :
  change_form h (ι _ m₁ * ι _ m₂) = ι _ m₁ * ι _ m₂ - algebra_map _ _ (B m₁ m₂) :=
by rw [change_form_ι_mul, change_form_ι, contract_left_ι, bilin_form.to_lin_apply]

/-- Theorem 23 of [grinberg_clifford_2016][] -/
lemma change_form_contract_left (d : module.dual R M) (x : clifford_algebra Q) :
  change_form h (d ⌋ x) = d ⌋ change_form h x :=
begin
  induction x using clifford_algebra.left_induction with r x y hx hy m x hx,
  { simp only [contract_left_algebra_map, change_form_algebra_map, map_zero] },
  { rw [map_add, map_add, map_add, map_add, hx, hy] },
  { simp only [contract_left_ι_mul, change_form_ι_mul, map_sub, linear_map.map_smul],
    rw [←hx, contract_left_comm, ←sub_add, sub_neg_eq_add, ←hx] }
end

lemma change_form_self_apply (x : clifford_algebra Q) :
  change_form (change_form.zero_proof) x = x :=
begin
  induction x using clifford_algebra.left_induction with r x y hx hy m x hx,
  { simp_rw [change_form_algebra_map] },
  { rw [map_add, hx, hy] },
  { rw [change_form_ι_mul, hx, map_zero, linear_map.zero_apply, map_zero, linear_map.zero_apply,
        sub_zero] }
end

@[simp]
lemma change_form_self  :
  change_form change_form.zero_proof = (linear_map.id : clifford_algebra Q →ₗ[R] _) :=
linear_map.ext $ change_form_self_apply

/-- This is [bourbaki2007][] $9 Lemma 3. -/
lemma change_form_change_form (x : clifford_algebra Q) :
  change_form h' (change_form h x) = change_form (change_form.add_proof h h') x :=
begin
  induction x using clifford_algebra.left_induction with r x y hx hy m x hx,
  { simp_rw [change_form_algebra_map] },
  { rw [map_add, map_add, map_add, hx, hy] },
  { rw [change_form_ι_mul, map_sub, change_form_ι_mul, change_form_ι_mul, hx, sub_sub, map_add,
    linear_map.add_apply, map_add, linear_map.add_apply, change_form_contract_left, hx,
    add_comm (_ : clifford_algebra Q'')] }
end

lemma change_form_comp_change_form :
  (change_form h').comp (change_form h) = change_form (change_form.add_proof h h') :=
linear_map.ext $ change_form_change_form _ _

/-- Any two algebras whose quadratic forms differ by a bilinear form are isomorphic as modules.

This is $\bar \lambda_B$ from [bourbaki2007][] $9 Proposition 3. -/
@[simps apply]
def change_form_equiv : clifford_algebra Q ≃ₗ[R] clifford_algebra Q' :=
{ to_fun := change_form h,
  inv_fun := change_form (change_form.neg_proof h),
  left_inv := λ x, (change_form_change_form _ _ x).trans $
    by simp_rw [add_right_neg, change_form_self_apply],
  right_inv := λ x, (change_form_change_form _ _ x).trans $
    by simp_rw [add_left_neg, change_form_self_apply],
  ..change_form h }

@[simp]
lemma change_form_equiv_symm :
  (change_form_equiv h).symm = change_form_equiv (change_form.neg_proof h) :=
linear_equiv.ext $ λ x, (rfl : change_form _ x = change_form _ x)

variables (Q)

/-- The module isomorphism to the exterior algebra.

Note that this holds more generally when `Q` is divisible by two, rather than only when `1` is
divisible by two; but that would be more awkward to use. -/
@[simp]
def equiv_exterior [invertible (2 : R)] : clifford_algebra Q ≃ₗ[R] exterior_algebra R M :=
change_form_equiv change_form.associated_neg_proof

end clifford_algebra
