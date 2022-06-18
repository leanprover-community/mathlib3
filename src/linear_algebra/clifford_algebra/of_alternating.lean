/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import linear_algebra.clifford_algebra.fold
import linear_algebra.pi_tensor_product

/-!
# Extending an alternating map to the exterior algebra

Note this is currently expressed in terms of `clifford_algebra (0 : quadratic_form R M)` as that
has more API.
-/

variables {R M N : Type*} [comm_ring R] [add_comm_group M] [ring N] [module R M] [module R N]

open_locale direct_sum

instance alternating_map.module_add_comm_group {ι : Type*} [decidable_eq ι] :
  module R (alternating_map R M N ι) :=
by apply_instance

instance direct_sum.alternating_map_add_comm_group :
  add_comm_group (⨁ i, alternating_map R M N (fin i)) :=
@dfinsupp.add_comm_group ℕ (λ i, alternating_map R M N (fin i)) _

instance direct_sum.alternating_map_module :
  module R (⨁ i, alternating_map R M N (fin i)) :=
by apply_instance

namespace exterior_algebra

/-- Build a map out of the exterior algebra given a collection of alternating maps acting on each
exterior power -/
def lift_direct_sum :
  (⨁ i, alternating_map R M N (fin i)) →ₗ[R] clifford_algebra (0 : quadratic_form R M) →ₗ[R] N :=
begin
  suffices :
    (⨁ i, alternating_map R M N (fin i))
      →ₗ[R] clifford_algebra (0 : quadratic_form R M)
      →ₗ[R] (⨁ i, alternating_map R M N (fin i)),
  { refine linear_map.compr₂ this _,
    refine linear_equiv.to_linear_map _ ∘ₗ direct_sum.component R ℕ _ 0,
    exact alternating_map.const_linear_equiv_of_is_empty.symm },
  refine clifford_algebra.foldl _ _ _,
  { -- our recursive step turns `![f₀, f₁, ..., fₙ₋₁, fₙ]` into `![f₁ m, f₂ m, ..., fₙ m, 0]`, where
    -- `f₁ m` here is shorthand for partial application via `f₁.curry_left m`.
    refine linear_map.mk₂ R (λ m f, _)
      (λ m₁ m₂ f, _) (λ c m f, _) (λ m f₁ f₂, _) (λ c m f, _),
    { refine dfinsupp.map_range.linear_map
        (λ i : ℕ, (alternating_map.curry_left_linear_map.flip m
          : alternating_map R M N (fin i.succ) →ₗ[R] alternating_map R M N (fin i)))
          _,
      refine (dfinsupp.comap_domain' nat.succ nat.pred_succ f : _), },
    all_goals { ext i, simp only [dfinsupp.map_range.linear_map_apply, dfinsupp.map_range_apply,
      linear_map.flip_apply, dfinsupp.comap_domain'_apply, dfinsupp.add_apply, dfinsupp.smul_apply,
      linear_map.add_apply, linear_map.smul_apply, map_add, map_smul] }, },
  { -- when applied twice with the same `m`, this recursive step obviously produces 0; either
    -- because we appended zeros on the last two elements, or because of
    -- `alternating_map.curry_left_same`.
    intros m x,
    dsimp only [linear_map.mk₂_apply, quadratic_form.coe_fn_zero, pi.zero_apply],
    simp_rw zero_smul,
    ext i : 1,
    simp_rw [dfinsupp.map_range.linear_map_apply, dfinsupp.map_range_apply,
      dfinsupp.comap_domain'_apply, dfinsupp.map_range_apply, dfinsupp.comap_domain'_apply,
      linear_map.flip_apply, alternating_map.curry_left_linear_map_apply,
      alternating_map.curry_left_same, direct_sum.zero_apply], }
end

@[simp]
lemma lift_direct_sum_of {i : ℕ} (f : alternating_map R M N (fin i))
  (v : fin i → M) :
  lift_direct_sum (direct_sum.of _ i f)
    ((list.of_fn $ λ i, clifford_algebra.ι (0 : quadratic_form R M) (v i))).prod = f v :=
begin
  rw lift_direct_sum,
  dsimp [direct_sum.component],
  induction i generalizing v,
  { dsimp,
    rw [clifford_algebra.foldl_one, direct_sum.of_eq_same, subsingleton.elim 0 v] },
  { rw [list.of_fn_succ, list.prod_cons, clifford_algebra.foldl_mul,
      clifford_algebra.foldl_ι, linear_map.mk₂_apply, direct_sum.of,
      dfinsupp.single_add_hom_apply, dfinsupp.comap_domain'_single, dfinsupp.map_range_single,
      linear_map.flip_apply, alternating_map.curry_left_linear_map_apply],
    specialize i_ih (f.curry_left (v 0)) (λ i, v (i.succ)),
    refine i_ih.trans (alternating_map.congr_arg f _),
    exact matrix.cons_head_tail _ }
end

@[simp]
lemma lift_direct_sum_of_one (f : alternating_map R M N (fin 0)) :
  lift_direct_sum (direct_sum.of (λ i, alternating_map R M N (fin i)) 0 f)
    (1 : clifford_algebra (0 : quadratic_form R M)) = f ![] :=
lift_direct_sum_of f ![]

@[simp]
lemma lift_direct_sum_of_algebra_map (f : alternating_map R M N (fin 0)) (r : R) :
  lift_direct_sum (direct_sum.of (λ i, alternating_map R M N (fin i)) 0 f)
    (algebra_map _ (clifford_algebra (0 : quadratic_form R M)) r) = r • f ![] :=
by rw [algebra.algebra_map_eq_smul_one, map_smul, lift_direct_sum_of_one]

@[simp]
lemma lift_direct_sum_of_ι (f : alternating_map R M N (fin 1)) (m : M) :
  lift_direct_sum (direct_sum.of (λ i, alternating_map R M N (fin i)) 1 f)
    (clifford_algebra.ι (0 : quadratic_form R M) m) = f ![m] :=
begin
  convert lift_direct_sum_of f ![m] using 2,
  rw [list.of_fn_succ, list.of_fn_zero, list.prod_singleton, matrix.cons_val_fin_one],
end

end exterior_algebra

/-- TODO: reimplement this with `exterior_algebra.lift_direct_sum`. -/
@[simp]
def alternating_map.to_exterior_hom {n : ℕ} (f : alternating_map R M N (fin n)) :
  clifford_algebra (0 : quadratic_form R M) →ₗ[R] N :=
exterior_algebra.lift_direct_sum $ direct_sum.of _ n f
