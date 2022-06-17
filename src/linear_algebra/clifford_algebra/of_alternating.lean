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

variables {R M A : Type*} [field R] [add_comm_group M] [ring A] [module R M] [algebra R A]

def alternating_map.to_exterior_hom {n : ℕ} (f : alternating_map R M A (fin n)) :
  clifford_algebra (0 : quadratic_form R M) →ₗ[R] A :=
begin
  letI : Π (i : fin n.succ), module R (alternating_map R M A (fin ↑i)) :=
    λ i, alternating_map.module,
  letI : module R (Π i : fin n.succ, alternating_map R M A (fin i)) :=
    @pi.module (fin n.succ) (λ i, alternating_map R M A (fin i)) R _ _ (by apply_instance),
  suffices :
    clifford_algebra (0 : quadratic_form R M)
      →ₗ[R] (Π i : fin n.succ, alternating_map R M A (fin i)),
  { refine _ ∘ₗ linear_map.proj (0 : fin n.succ) ∘ₗ this,
    refine linear_equiv.to_linear_map _,
    haveI : is_empty (fin ↑(0 : fin n.succ)) := fin.is_empty,
    refine alternating_map.const_linear_equiv_of_is_empty.symm },
  refine clifford_algebra.foldr (0 : quadratic_form R M) _ _ _,
  { refine linear_map.mk₂ R (λ m f, _)
      (λ m₁ m₂ f, _) (λ c m f, _) (λ m f₁ f₂, _) (λ c m f, _),
    refine fin.snoc (λ i, _) 0,
    { have f' := (f (fin.succ i)).dom_dom_congr (fin.cast $ fin.coe_succ _).to_equiv,
      refine f'.curry_left m },
      all_goals { ext i : 1, refine fin.last_cases _ _ i; clear i; [skip, intro i];
        simp only [pi.add_apply, pi.smul_apply, fin.snoc_last, fin.snoc_cast_succ, zero_add,
          smul_zero, map_add, map_smul]; refl },
       },
  { intros m x,
    dsimp only [linear_map.mk₂_apply, quadratic_form.coe_fn_zero, pi.zero_apply],
    simp_rw zero_smul,
    ext i : 1,
    refine fin.last_cases _ _ i; clear i; dsimp only [pi.zero_apply],
    { rw [fin.snoc_last] },
    intro i,
    simp_rw [fin.snoc_cast_succ],
    generalize_proofs _ hi',
    revert hi',
    generalize hi'' : fin.succ i = i'',
    revert hi'',
    refine fin.last_cases _ (λ i''', _) i''; intros hi' hi'',
    { rw [fin.snoc_last], ext i, exact eq.refl (0 : A) },
    change (i''' : ℕ) = i + 1 at hi'',
    simp_rw [fin.snoc_cast_succ],
    dsimp,
    rw [←alternating_map.curry_left_dom_dom_congr_fin_cast, alternating_map.curry_left_same],
    rw hi'' },
  exact pi.single (fin.last _) f,
end

@[simp]
lemma alternating_map.to_exterior_hom_algebra_map (f : alternating_map R M A (fin 0)) (r : R) :
  f.to_exterior_hom (algebra_map _ _ r) = r • f ![] :=
begin
  dsimp [alternating_map.to_exterior_hom],
  rw clifford_algebra.foldr_algebra_map,
  simp,
  congr' 1,
end

@[simp]
lemma alternating_map.to_exterior_hom_ι (f : alternating_map R M A (fin 1)) (m : M) :
  f.to_exterior_hom (clifford_algebra.ι _ m) = f ![m] :=
begin
  dsimp [alternating_map.to_exterior_hom],
  rw clifford_algebra.foldr_ι,
  dsimp,
  rw fin.snoc,
  simp,
  congr' 1,
end
