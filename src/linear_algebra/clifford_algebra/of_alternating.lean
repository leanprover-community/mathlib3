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

/-- Build a map out of the exterior algebra given a collection of alternating maps acting on each
exterior power -/
def exterior_algebra.lift_direct_sum :
  (⨁ i, alternating_map R M N (fin i)) →ₗ[R] clifford_algebra (0 : quadratic_form R M) →ₗ[R] N :=
begin
  suffices :
    (⨁ i, alternating_map R M N (fin i))
      →ₗ[R] clifford_algebra (0 : quadratic_form R M)
      →ₗ[R] (⨁ i, alternating_map R M N (fin i)),
  { refine linear_map.compr₂ this _,
    refine linear_equiv.to_linear_map _ ∘ₗ direct_sum.component R ℕ _ 0,
    exact alternating_map.const_linear_equiv_of_is_empty.symm },
  refine clifford_algebra.foldr _ _ _,
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
lemma exterior_algebra.lift_direct_sum_of (i : ℕ) (f : alternating_map R M N (fin i))
  (v : fin i → M) :
  exterior_algebra.lift_direct_sum (direct_sum.of _ i f)
    ((list.of_fn v).map (clifford_algebra.ι (0 : quadratic_form R M))).prod = f v :=
begin
  rw exterior_algebra.lift_direct_sum,
  dsimp [direct_sum.component],
  induction i generalizing v,
  sorry { dsimp,
    rw [clifford_algebra.foldr_one, direct_sum.of_eq_same, subsingleton.elim 0 v] },
  rw [list.of_fn_succ', list.map_concat, list.prod_concat, clifford_algebra.foldr_mul,
    clifford_algebra.foldr_ι, linear_map.mk₂_apply, dfinsupp.comap_domain'_apply],
  have := i_ih (f.curry_left (v 0)) (λ i, v (nat.succ i)),
  -- rw [list.of_fn_succ, list.map_cons, list.prod_cons, clifford_algebra.foldr_mul,
  --   clifford_algebra.foldr_ι, linear_map.mk₂_apply, dfinsupp.map_range_apply,
  --   dfinsupp.comap_domain'_apply, linear_map.flip_apply,
  --   alternating_map.curry_left_linear_map_apply,
  --   alternating_map.curry_left_apply_apply, matrix.zero_empty],
  -- have := i_ih (f.curry_left (v 0)) (λ i, v (nat.succ i)),
  -- simp at this,
  -- dsimp,
  -- rw clifford_algebra.foldr_algebra_map,
  -- simp,
  -- congr' 1,
end


/-- TODO: reimplement this with `exterior_algebra.lift_direct_sum`. -/
def alternating_map.to_exterior_hom {n : ℕ} (f : alternating_map R M N (fin n)) :
  clifford_algebra (0 : quadratic_form R M) →ₗ[R] N :=
begin
  -- start by reminding lean how to find instances under binders
  letI : Π (i : fin n.succ), module R (alternating_map R M N (fin ↑i)) :=
    λ i, alternating_map.module,
  letI : module R (Π i : fin n.succ, alternating_map R M N (fin i)) :=
    @pi.module (fin n.succ) (λ i, alternating_map R M N (fin i)) R _ _ (by apply_instance),
  -- We'll recurse over sequences of `n + 1` alternating maps, taking between `0` and `n` (incusive)
  -- arguments. Our final result will be the value of the map taking 0 arguments.
  suffices :
    clifford_algebra (0 : quadratic_form R M)
      →ₗ[R] (Π i : fin n.succ, alternating_map R M N (fin i)),
  { refine _ ∘ₗ linear_map.proj (0 : fin n.succ) ∘ₗ this,
    refine linear_equiv.to_linear_map _,
    haveI : is_empty (fin ↑(0 : fin n.succ)) := fin.is_empty,
    refine alternating_map.const_linear_equiv_of_is_empty.symm },
  refine clifford_algebra.foldr (0 : quadratic_form R M) _ _ _,
  { -- our recursive step turns `![f₀, f₁, ..., fₙ₋₁, fₙ]` into `![f₁ m, f₂ m, ..., fₙ m, 0]`, where
    -- `f₁ m` here is shorthand for partial application via `f₁.curry_left m`. The slight snag is we
    -- have to cast our arity from `succ ↑i` to `↑i.succ`, which makes our later proof awful.
    refine linear_map.mk₂ R (λ m f, _)
      (λ m₁ m₂ f, _) (λ c m f, _) (λ m f₁ f₂, _) (λ c m f, _),
    refine fin.snoc (λ i, _) 0,
    { have f' := (f (fin.succ i)).dom_dom_congr (fin.cast $ fin.coe_succ _).to_equiv,
      refine f'.curry_left m },
    -- prove that map is linear
    all_goals { ext i : 1, refine fin.last_cases _ _ i; clear i; [skip, intro i];
      simp only [pi.add_apply, pi.smul_apply, fin.snoc_last, fin.snoc_cast_succ, zero_add,
        smul_zero, map_add, map_smul]; refl } },
  { -- when applied twice with the same `m`, this recursive step obviously produces 0; either
    -- because we appended zeros on the last two elements, or because of
    -- `alternating_map.curry_left_same`.
    intros m x,
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
    { rw [fin.snoc_last], ext i, exact eq.refl (0 : N) },
    change (i''' : ℕ) = i + 1 at hi'',
    simp_rw [fin.snoc_cast_succ],
    dsimp,
    rw [←alternating_map.curry_left_dom_dom_congr_fin_cast, alternating_map.curry_left_same],
    rw hi'' },
  exact pi.single (fin.last _) f,
end

@[simp]
lemma alternating_map.to_exterior_hom_algebra_map (f : alternating_map R M N (fin 0)) (r : R) :
  f.to_exterior_hom (algebra_map _ _ r) = r • f ![] :=
begin
  dsimp [alternating_map.to_exterior_hom],
  rw clifford_algebra.foldr_algebra_map,
  simp,
  congr' 1,
end

@[simp]
lemma alternating_map.to_exterior_hom_ι (f : alternating_map R M N (fin 1)) (m : M) :
  f.to_exterior_hom (clifford_algebra.ι _ m) = f ![m] :=
begin
  dsimp [alternating_map.to_exterior_hom],
  rw clifford_algebra.foldr_ι,
  dsimp,
  rw fin.snoc,
  simp,
  congr' 1,
end
