/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/
import linear_algebra.pi
import linear_algebra.quotient

/-!
# Submodule quotients and direct sums

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains some results on the quotient of a module by a direct sum of submodules,
and the direct sum of quotients of modules by submodules.

# Main definitions

 * `submodule.pi_quotient_lift`: create a map out of the direct sum of quotients
 * `submodule.quotient_pi_lift`: create a map out of the quotient of a direct sum
 * `submodule.quotient_pi`: the quotient of a direct sum is the direct sum of quotients.

-/

namespace submodule

open linear_map

variables {ι R : Type*} [comm_ring R]
variables {Ms : ι → Type*} [∀ i, add_comm_group (Ms i)] [∀ i, module R (Ms i)]
variables {N : Type*} [add_comm_group N] [module R N]
variables {Ns : ι → Type*} [∀ i, add_comm_group (Ns i)] [∀ i, module R (Ns i)]

/-- Lift a family of maps to the direct sum of quotients. -/
def pi_quotient_lift [fintype ι] [decidable_eq ι]
  (p : ∀ i, submodule R (Ms i)) (q : submodule R N)
  (f : Π i, Ms i →ₗ[R] N) (hf : ∀ i, p i ≤ q.comap (f i)) :
  (Π i, (Ms i ⧸ p i)) →ₗ[R] (N ⧸ q) :=
lsum R (λ i, (Ms i ⧸ (p i))) R (λ i, (p i).mapq q (f i) (hf i))

@[simp] lemma pi_quotient_lift_mk [fintype ι] [decidable_eq ι]
  (p : ∀ i, submodule R (Ms i)) (q : submodule R N)
  (f : Π i, Ms i →ₗ[R] N) (hf : ∀ i, p i ≤ q.comap (f i)) (x : Π i, Ms i) :
  pi_quotient_lift p q f hf (λ i, quotient.mk (x i)) =
    quotient.mk (lsum _ _ R f x) :=
by rw [pi_quotient_lift, lsum_apply, sum_apply, ← mkq_apply, lsum_apply, sum_apply, _root_.map_sum];
   simp only [coe_proj, mapq_apply, mkq_apply, comp_apply]

@[simp] lemma pi_quotient_lift_single [fintype ι] [decidable_eq ι]
  (p : ∀ i, submodule R (Ms i)) (q : submodule R N)
  (f : Π i, Ms i →ₗ[R] N) (hf : ∀ i, p i ≤ q.comap (f i)) (i) (x : Ms i ⧸ p i) :
  pi_quotient_lift p q f hf (pi.single i x) =
    mapq _ _ (f i) (hf i) x :=
begin
  simp_rw [pi_quotient_lift, lsum_apply, sum_apply,
           comp_apply, proj_apply],
  rw finset.sum_eq_single i,
  { rw pi.single_eq_same },
  { rintros j - hj, rw [pi.single_eq_of_ne hj, _root_.map_zero] },
  { intros, have := finset.mem_univ i, contradiction },
end

/-- Lift a family of maps to a quotient of direct sums. -/
def quotient_pi_lift
  (p : ∀ i, submodule R (Ms i))
  (f : Π i, Ms i →ₗ[R] Ns i) (hf : ∀ i, p i ≤ ker (f i)) :
  ((Π i, Ms i) ⧸ pi set.univ p) →ₗ[R] Π i, Ns i :=
(pi set.univ p).liftq (linear_map.pi (λ i, (f i).comp (proj i))) $
λ x hx, mem_ker.mpr $
by { ext i, simpa using hf i (mem_pi.mp hx i (set.mem_univ i)) }

@[simp] lemma quotient_pi_lift_mk
  (p : ∀ i, submodule R (Ms i))
  (f : Π i, Ms i →ₗ[R] Ns i) (hf : ∀ i, p i ≤ ker (f i)) (x : Π i, Ms i) :
  quotient_pi_lift p f hf (quotient.mk x) = λ i, f i (x i) :=
rfl

/-- The quotient of a direct sum is the direct sum of quotients. -/
@[simps] def quotient_pi [fintype ι] [decidable_eq ι]
  (p : ∀ i, submodule R (Ms i)) :
  ((Π i, Ms i) ⧸ pi set.univ p) ≃ₗ[R] Π i, Ms i ⧸ p i :=
{ to_fun := quotient_pi_lift p (λ i, (p i).mkq) (λ i, by simp),
  inv_fun := pi_quotient_lift p (pi set.univ p)
    single (λ i, le_comap_single_pi p),
  left_inv := λ x, quotient.induction_on' x (λ x',
    by simp_rw [quotient.mk'_eq_mk, quotient_pi_lift_mk, mkq_apply,
                pi_quotient_lift_mk, lsum_single, id_apply]),
  right_inv := begin
    rw [function.right_inverse_iff_comp, ← coe_comp, ← @id_coe R],
    refine congr_arg _ (pi_ext (λ i x, quotient.induction_on' x (λ x', funext $ λ j, _))),
    rw [comp_apply, pi_quotient_lift_single, quotient.mk'_eq_mk, mapq_apply,
        quotient_pi_lift_mk, id_apply],
    by_cases hij : i = j; simp only [mkq_apply, coe_single],
    { subst hij, simp only [pi.single_eq_same] },
    { simp only [pi.single_eq_of_ne (ne.symm hij), quotient.mk_zero] },
  end,
  .. quotient_pi_lift p (λ i, (p i).mkq) (λ i, by simp) }

end submodule
