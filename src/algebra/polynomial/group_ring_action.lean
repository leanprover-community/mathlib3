/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import data.polynomial.monic
import data.polynomial.algebra_map
import algebra.group_ring_action
import algebra.group_action_hom


/-!
# Group action on rings applied to polynomials

This file contains instances and definitions relating `mul_semiring_action` to `polynomial`.
-/

variables (M : Type*) [monoid M]

namespace polynomial

variables (R : Type*) [semiring R]

variables {M}

lemma smul_eq_map [mul_semiring_action M R] (m : M) :
  ((•) m) = map (mul_semiring_action.to_ring_hom M R m) :=
begin
  suffices :
    distrib_mul_action.to_add_monoid_hom M (polynomial R) m =
      (map_ring_hom (mul_semiring_action.to_ring_hom M R m)).to_add_monoid_hom,
  { ext1 r, exact add_monoid_hom.congr_fun this r, },
  ext n r : 2,
  change m • monomial n r = map (mul_semiring_action.to_ring_hom M R m) (monomial n r),
  simpa only [polynomial.map_monomial, polynomial.smul_monomial],
end

variables (M)

noncomputable instance [mul_semiring_action M R] : mul_semiring_action M (polynomial R) :=
{ smul := (•),
  smul_one := λ m, (smul_eq_map R m).symm ▸ map_one (mul_semiring_action.to_ring_hom M R m),
  smul_mul := λ m p q, (smul_eq_map R m).symm ▸ map_mul (mul_semiring_action.to_ring_hom M R m),
  ..polynomial.distrib_mul_action }

variables {M R}

variables [mul_semiring_action M R]

@[simp] lemma smul_X (m : M) : (m • X : polynomial R) = X :=
(smul_eq_map R m).symm ▸ map_X _

variables (S : Type*) [comm_semiring S] [mul_semiring_action M S]

theorem smul_eval_smul (m : M) (f : polynomial S) (x : S) :
  (m • f).eval (m • x) = m • f.eval x :=
polynomial.induction_on f
  (λ r, by rw [smul_C, eval_C, eval_C])
  (λ f g ihf ihg, by rw [smul_add, eval_add, ihf, ihg, eval_add, smul_add])
  (λ n r ih, by rw [smul_mul', smul_pow, smul_C, smul_X, eval_mul, eval_C, eval_pow, eval_X,
      eval_mul, eval_C, eval_pow, eval_X, smul_mul', smul_pow])

variables (G : Type*) [group G]

theorem eval_smul' [mul_semiring_action G S] (g : G) (f : polynomial S) (x : S) :
  f.eval (g • x) = g • (g⁻¹ • f).eval x :=
by rw [← smul_eval_smul, smul_inv_smul]

theorem smul_eval [mul_semiring_action G S] (g : G) (f : polynomial S) (x : S) :
  (g • f).eval x = g • f.eval (g⁻¹ • x) :=
by rw [← smul_eval_smul, smul_inv_smul]

end polynomial

section comm_ring

variables (G : Type*) [group G] [fintype G]
variables (R : Type*) [comm_ring R] [mul_semiring_action G R]
open mul_action
open_locale classical

/-- the product of `(X - g • x)` over distinct `g • x`. -/
noncomputable def prod_X_sub_smul (x : R) : polynomial R :=
(finset.univ : finset (quotient_group.quotient $ mul_action.stabilizer G x)).prod $
λ g, polynomial.X - polynomial.C (of_quotient_stabilizer G x g)

theorem prod_X_sub_smul.monic (x : R) : (prod_X_sub_smul G R x).monic :=
polynomial.monic_prod_of_monic _ _ $ λ g _, polynomial.monic_X_sub_C _

theorem prod_X_sub_smul.eval (x : R) : (prod_X_sub_smul G R x).eval x = 0 :=
(monoid_hom.map_prod
  ((polynomial.aeval x).to_ring_hom.to_monoid_hom : polynomial R →* R) _ _).trans $
  finset.prod_eq_zero (finset.mem_univ $ quotient_group.mk 1) $
  by simp

theorem prod_X_sub_smul.smul (x : R) (g : G) :
  g • prod_X_sub_smul G R x = prod_X_sub_smul G R x :=
(smul_prod _ _ _ _ _).trans $ fintype.prod_bijective _ (mul_action.bijective g) _ _
  (λ g', by rw [of_quotient_stabilizer_smul, smul_sub, polynomial.smul_X, polynomial.smul_C])

theorem prod_X_sub_smul.coeff (x : R) (g : G) (n : ℕ) :
  g • (prod_X_sub_smul G R x).coeff n =
  (prod_X_sub_smul G R x).coeff n :=
by rw [← polynomial.coeff_smul, prod_X_sub_smul.smul]

end comm_ring

namespace mul_semiring_action_hom
variables {M}
variables {P : Type*} [comm_semiring P] [mul_semiring_action M P]
variables {Q : Type*} [comm_semiring Q] [mul_semiring_action M Q]
open polynomial

/-- An equivariant map induces an equivariant map on polynomials. -/
protected noncomputable def polynomial (g : P →+*[M] Q) : polynomial P →+*[M] polynomial Q :=
{ to_fun := map g,
  map_smul' := λ m p, polynomial.induction_on p
    (λ b, by rw [smul_C, map_C, coe_fn_coe, g.map_smul, map_C, coe_fn_coe, smul_C])
    (λ p q ihp ihq, by rw [smul_add, polynomial.map_add, ihp, ihq, polynomial.map_add, smul_add])
    (λ n b ih, by rw [smul_mul', smul_C, smul_pow, smul_X, polynomial.map_mul, map_C,
        polynomial.map_pow, map_X, coe_fn_coe, g.map_smul, polynomial.map_mul, map_C,
        polynomial.map_pow, map_X, smul_mul', smul_C, smul_pow, smul_X, coe_fn_coe]),
  map_zero' := polynomial.map_zero g,
  map_add' := λ p q, polynomial.map_add g,
  map_one' := polynomial.map_one g,
  map_mul' := λ p q, polynomial.map_mul g }

@[simp] theorem coe_polynomial (g : P →+*[M] Q) :
  (g.polynomial : polynomial P → polynomial Q) = map g :=
rfl

end mul_semiring_action_hom
