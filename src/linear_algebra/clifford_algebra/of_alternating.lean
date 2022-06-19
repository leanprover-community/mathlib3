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

namespace exterior_algebra

/-- Build a map out of the exterior algebra given a collection of alternating maps acting on each
exterior power -/
def lift_alternating :
  (Π i, alternating_map R M N (fin i)) →ₗ[R] clifford_algebra (0 : quadratic_form R M) →ₗ[R] N :=
begin
  suffices :
    (Π i, alternating_map R M N (fin i))
      →ₗ[R] clifford_algebra (0 : quadratic_form R M)
      →ₗ[R] (Π i, alternating_map R M N (fin i)),
  { refine linear_map.compr₂ this _,
    refine linear_equiv.to_linear_map _ ∘ₗ linear_map.proj 0,
    exact alternating_map.const_linear_equiv_of_is_empty.symm },
  refine clifford_algebra.foldl _ _ _,
  { -- our recursive step turns `![f₀, f₁, ..., fₙ₋₁, fₙ]` into `![f₁ m, f₂ m, ..., fₙ m, 0]`, where
    -- `f₁ m` here is shorthand for partial application via `f₁.curry_left m`.
    refine linear_map.mk₂ R (λ m f i, (f i.succ).curry_left m)
      (λ m₁ m₂ f, _) (λ c m f, _) (λ m f₁ f₂, _) (λ c m f, _),
    all_goals {
      ext i : 1,
      simp_rw ←alternating_map.curry_left_linear_map_apply,
      simp only [map_smul, map_add, pi.add_apply, pi.smul_apply, linear_map.add_apply,
        linear_map.smul_apply] } },
  { -- when applied twice with the same `m`, this recursive step obviously produces 0; either
    -- because we appended zeros on the last two elements, or because of
    -- `alternating_map.curry_left_same`.
    intros m x,
    dsimp only [linear_map.mk₂_apply, quadratic_form.coe_fn_zero, pi.zero_apply],
    simp_rw zero_smul,
    ext i : 1,
    exact alternating_map.curry_left_same _ _, }
end

@[simp]
lemma lift_alternating_single {i : ℕ} (f : alternating_map R M N (fin i))
  (v : fin i → M) :
  lift_alternating (pi.single i f)
    ((list.of_fn $ λ i, clifford_algebra.ι (0 : quadratic_form R M) (v i))).prod = f v :=
begin
  rw lift_alternating,
  dsimp,
  induction i with i ih generalizing v,
  { rw [list.of_fn_zero, list.prod_nil, clifford_algebra.foldl_one, pi.single_eq_same,
      subsingleton.elim 0 v] },
  { rw [list.of_fn_succ, list.prod_cons, clifford_algebra.foldl_mul,
      clifford_algebra.foldl_ι, linear_map.mk₂_apply],
    -- The elaborator doesn't count the arguments properly if we don't add the `_`s...
    have : ∀ (v0 : M) (i' : ℕ),
      (@pi.single _ (λ k, alternating_map R M N (fin k)) _ _ i.succ f i'.succ).curry_left v0 =
        @pi.single _ _ _ _ i (f.curry_left v0) i',
    { intros v0 i',
      obtain rfl | hii' := decidable.eq_or_ne i' i,
      { rw [pi.single_eq_same, pi.single_eq_same] },
      { rw [pi.single_eq_of_ne hii', pi.single_eq_of_ne (nat.succ_injective.ne hii'),
          ←alternating_map.curry_left_linear_map_apply, linear_map.map_zero₂] } },
    simp_rw this,
    specialize ih (f.curry_left (matrix.vec_head v)) (matrix.vec_tail v),
    rw [alternating_map.curry_left_apply_apply, matrix.cons_head_tail, matrix.vec_head] at ih,
    exact ih }
end

@[simp]
lemma lift_alternating_single_one (f : alternating_map R M N (fin 0)) :
  lift_alternating (pi.single 0 f) (1 : clifford_algebra (0 : quadratic_form R M)) = f ![] :=
lift_alternating_single f ![]

@[simp]
lemma lift_alternating_single_algebra_map (f : alternating_map R M N (fin 0)) (r : R) :
  lift_alternating (pi.single 0 f)
    (algebra_map _ (clifford_algebra (0 : quadratic_form R M)) r) = r • f ![] :=
by rw [algebra.algebra_map_eq_smul_one, map_smul, lift_alternating_single_one]

@[simp]
lemma lift_alternating_single_ι (f : alternating_map R M N (fin 1)) (m : M) :
  lift_alternating (pi.single 1 f) (clifford_algebra.ι (0 : quadratic_form R M) m) = f ![m] :=
begin
  convert lift_alternating_single f ![m] using 2,
  rw [list.of_fn_succ, list.of_fn_zero, list.prod_singleton, matrix.cons_val_fin_one],
end

end exterior_algebra

/-- TODO: reimplement this with `exterior_algebra.lift_alternating`. -/
@[simp]
def alternating_map.to_exterior_hom {n : ℕ} (f : alternating_map R M N (fin n)) :
  clifford_algebra (0 : quadratic_form R M) →ₗ[R] N :=
exterior_algebra.lift_alternating $ pi.single n f
