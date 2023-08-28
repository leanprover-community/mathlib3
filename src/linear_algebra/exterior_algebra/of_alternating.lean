/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import linear_algebra.clifford_algebra.fold
import linear_algebra.exterior_algebra.basic

/-!
# Extending an alternating map to the exterior algebra

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `exterior_algebra.lift_alternating`: construct a linear map out of the exterior algebra
  given alternating maps (corresponding to maps out of the exterior powers).
* `exterior_algebra.lift_alternating_equiv`: the above as a linear equivalence

## Main results

* `exterior_algebra.lhom_ext`: linear maps from the exterior algebra agree if they agree on the
  exterior powers.

-/

variables {R M N N' : Type*}
variables [comm_ring R] [add_comm_group M] [add_comm_group N] [add_comm_group N']
variables [module R M] [module R N] [module R N']

-- This instance can't be found where it's needed if we don't remind lean that it exists.
instance alternating_map.module_add_comm_group {ι : Type*} :
  module R (alternating_map R M N ι) :=
by apply_instance

namespace exterior_algebra
open clifford_algebra (hiding ι)

/-- Build a map out of the exterior algebra given a collection of alternating maps acting on each
exterior power -/
def lift_alternating : (Π i, alternating_map R M N (fin i)) →ₗ[R] exterior_algebra R M →ₗ[R] N :=
begin
  suffices :
    (Π i, alternating_map R M N (fin i))
      →ₗ[R] exterior_algebra R M
      →ₗ[R] (Π i, alternating_map R M N (fin i)),
  { refine linear_map.compr₂ this _,
    refine linear_equiv.to_linear_map _ ∘ₗ linear_map.proj 0,
    exact alternating_map.const_linear_equiv_of_is_empty.symm },
  refine clifford_algebra.foldl _ _ _,
  { refine linear_map.mk₂ R
      (λ m f i, (f i.succ).curry_left m) (λ m₁ m₂ f, _) (λ c m f, _) (λ m f₁ f₂, _) (λ c m f, _),
    all_goals {
      ext i : 1,
      simp only [map_smul, map_add, pi.add_apply, pi.smul_apply, alternating_map.curry_left_add,
        alternating_map.curry_left_smul, map_add, map_smul, linear_map.add_apply,
        linear_map.smul_apply] } },
  { -- when applied twice with the same `m`, this recursive step produces 0
    intros m x,
    dsimp only [linear_map.mk₂_apply, quadratic_form.coe_fn_zero, pi.zero_apply],
    simp_rw zero_smul,
    ext i : 1,
    exact alternating_map.curry_left_same _ _, }
end

@[simp]
lemma lift_alternating_ι (f : Π i, alternating_map R M N (fin i)) (m : M) :
  lift_alternating f (ι R m) = f 1 ![m] :=
begin
  dsimp [lift_alternating],
  rw [foldl_ι, linear_map.mk₂_apply, alternating_map.curry_left_apply_apply],
  congr,
end

lemma lift_alternating_ι_mul (f : Π i, alternating_map R M N (fin i)) (m : M)
  (x : exterior_algebra R M):
  lift_alternating f (ι R m * x) = lift_alternating (λ i, (f i.succ).curry_left m) x :=
begin
  dsimp [lift_alternating],
  rw [foldl_mul, foldl_ι],
  refl,
end

@[simp]
lemma lift_alternating_one (f : Π i, alternating_map R M N (fin i)) :
  lift_alternating f (1 : exterior_algebra R M) = f 0 0 :=
begin
  dsimp [lift_alternating],
  rw foldl_one,
end

@[simp]
lemma lift_alternating_algebra_map (f : Π i, alternating_map R M N (fin i)) (r : R) :
  lift_alternating f (algebra_map _ (exterior_algebra R M) r) = r • f 0 0 :=
by rw [algebra.algebra_map_eq_smul_one, map_smul, lift_alternating_one]

@[simp]
lemma lift_alternating_apply_ι_multi {n : ℕ} (f : Π i, alternating_map R M N (fin i))
  (v : fin n → M) :
  lift_alternating f (ι_multi R n v) = f n v :=
begin
  rw ι_multi_apply,
  induction n with n ih generalizing f v,
  { rw [list.of_fn_zero, list.prod_nil, lift_alternating_one, subsingleton.elim 0 v] },
  { rw [list.of_fn_succ, list.prod_cons, lift_alternating_ι_mul, ih,
      alternating_map.curry_left_apply_apply],
    congr',
    exact matrix.cons_head_tail _ }
end

@[simp]
lemma lift_alternating_comp_ι_multi {n : ℕ} (f : Π i, alternating_map R M N (fin i)) :
  (lift_alternating f).comp_alternating_map (ι_multi R n) = f n :=
alternating_map.ext $ lift_alternating_apply_ι_multi f

@[simp]
lemma lift_alternating_comp (g : N →ₗ[R] N') (f : Π i, alternating_map R M N (fin i)) :
  lift_alternating (λ i, g.comp_alternating_map (f i)) = g ∘ₗ lift_alternating f :=
begin
  ext v,
  rw linear_map.comp_apply,
  induction v using clifford_algebra.left_induction with r x y hx hy x m hx generalizing f,
  { rw [lift_alternating_algebra_map, lift_alternating_algebra_map, map_smul,
      linear_map.comp_alternating_map_apply] },
  { rw [map_add, map_add, map_add, hx, hy] },
  { rw [lift_alternating_ι_mul, lift_alternating_ι_mul, ←hx],
    simp_rw alternating_map.curry_left_comp_alternating_map },
end

@[simp]
lemma lift_alternating_ι_multi :
  lift_alternating (by exact (ι_multi R)) =
    (linear_map.id : exterior_algebra R M →ₗ[R] exterior_algebra R M) :=
begin
  ext v,
  dsimp,
  induction v using clifford_algebra.left_induction with r x y hx hy x m hx,
  { rw [lift_alternating_algebra_map, ι_multi_zero_apply, algebra.algebra_map_eq_smul_one] },
  { rw [map_add, hx, hy] },
  { simp_rw [lift_alternating_ι_mul, ι_multi_succ_curry_left, lift_alternating_comp,
      linear_map.comp_apply, linear_map.mul_left_apply, hx] },
end

/-- `exterior_algebra.lift_alternating` is an equivalence. -/
@[simps apply symm_apply]
def lift_alternating_equiv :
  (Π i, alternating_map R M N (fin i)) ≃ₗ[R] exterior_algebra R M →ₗ[R] N :=
{ to_fun := lift_alternating,
  map_add' := map_add _,
  map_smul' := map_smul _,
  inv_fun := λ F i, F.comp_alternating_map (ι_multi R i),
  left_inv := λ f, funext $ λ i, lift_alternating_comp_ι_multi _,
  right_inv := λ F, (lift_alternating_comp _ _).trans $
    by rw [lift_alternating_ι_multi, linear_map.comp_id]}

/-- To show that two linear maps from the exterior algebra agree, it suffices to show they agree on
the exterior powers.

See note [partially-applied ext lemmas] -/
@[ext]
lemma lhom_ext ⦃f g : exterior_algebra R M →ₗ[R] N⦄
  (h : ∀ i, f.comp_alternating_map (ι_multi R i) = g.comp_alternating_map (ι_multi R i)) : f = g :=
lift_alternating_equiv.symm.injective $ funext h

end exterior_algebra
