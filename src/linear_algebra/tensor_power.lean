/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import linear_algebra.pi_tensor_product
import data.equiv.fin
import algebra.direct_sum.algebra
import data.fin.pi

/-!
# Tensor power of a semimodule over a commutative semirings

We define the `n`th tensor power of `M` as the n-ary tensor product indexed by `fin n` of `M`,
`⨂[R] (i : fin n), M`. This is a special case of `pi_tensor_product`
-/

open_locale tensor_product

/-- Homogenous tensor powers $M^{\otimes n}$. `⨂[R]^n M` is a shorthand for
`⨂[R] (i : fin n), M`. -/
protected abbreviation tensor_power (R : Type*) (n : ℕ) (M : Type*)
  [comm_semiring R] [add_comm_monoid M] [module R M] : Type* :=
⨂[R] (i : fin n), M

variables {R : Type*} {M : Type*} [comm_semiring R] [add_comm_monoid M] [module R M]

localized "notation `⨂[`:100 R `]^`:80 n:max := tensor_power R n"
  in tensor_product

namespace tensor_power
open_locale tensor_product
open pi_tensor_product

/-- The canonical map from `R` to `⨂[R]^0 M` corresponding to the algebra_map of the tensor
algebra. -/
def algebra_map : R ≃ₗ[R] ⨂[R]^0 M :=
((reindex R M fin_zero_equiv').trans pempty_equiv.{u_1 u_2 u_1}).symm

lemma algebra_map_eq_smul_tprod (r : R) :
  algebra_map r = r • tprod R (λ i : fin 0, (i.elim0 : M)) :=
begin
  simp [algebra_map],
  congr,
end

def one : ⨂[R]^0 M := algebra_map 1

/---/
def mul_equiv {n m : ℕ} : (⨂[R]^n M) ⊗[R] (⨂[R]^m M) ≃ₗ[R] ⨂[R]^(n + m) M :=
(tmul_equiv R M).trans (reindex R M fin_sum_fin_equiv)

def mul {n m : ℕ} : (⨂[R]^n M) →ₗ[R] (⨂[R]^m M) →ₗ[R] ⨂[R]^(n + m) M :=
begin
  refine linear_map.compr₂ _ _,
  rotate 3,
  refine tensor_product.mk R _ _,
  apply linear_equiv.to_linear_map,
  exact mul_equiv,
end

lemma tprod_mul_tprod {na nb} (a : fin na → M) (b : fin nb → M) :
  mul (tprod R a) (tprod R b) = (tprod R $ fin.append' a b) :=
begin
  dsimp [mul, mul_equiv],
  rw [tmul_equiv_apply R M a b],
  refine reindex_tprod _ _,
end

lemma algebra_map_mul {n} (r : R) (a : ⨂[R]^n M) :
  reindex R M (equiv.cast $ by rw zero_add) (mul (algebra_map r) a) = r • a :=
begin
  -- eliminate `r` and replace `a` with `tprod R a`
  rw [algebra_map_eq_smul_tprod, ←linear_equiv.coe_coe _, ←linear_map.compr₂_apply,
    linear_map.map_smul, linear_map.smul_apply, ←linear_map.map_smul],
  refine linear_map.congr_fun (_ : _ = linear_map.id) (r • a),
  clear r a,
  ext a,
  show (reindex R M (equiv.cast _)) (mul (tprod R (fin.elim0 : fin 0 → M)) (tprod R a)) = tprod R a,
  rw [tprod_mul_tprod, reindex_tprod],
  congr' 1 with i,
  rw fin.elim0_append',
  refine congr_arg a (fin.ext _),
  simp,
end

lemma one_mul {n} (a : ⨂[R]^n M) : reindex R M (equiv.cast $ by rw zero_add) (mul one a) = a :=
by rw [one, algebra_map_mul, one_smul]

lemma mul_algebra_map {n} (r : R) (a : ⨂[R]^n M) :
  reindex R M (equiv.cast $ by rw add_zero) (mul a (algebra_map r)) = r • a :=
begin
  unfold mul one mul_equiv,
  rw [algebra_map_eq_smul_tprod, linear_map.map_smul, linear_equiv.map_smul,
    ←linear_map.flip_apply, ←linear_equiv.coe_coe _, ←linear_map.llcomp_apply],
  congr' 1,
  refine linear_map.congr_fun (_ : _ = linear_map.id) a,
  clear r a,
  ext a,
  show (reindex R M (equiv.cast _)) (mul (tprod R a) (tprod R (fin.elim0 : fin 0 → M))) = tprod R a,
  rw [tprod_mul_tprod, reindex_tprod],
  congr' 1 with i,
  rw fin.append'_elim0,
  refine congr_arg a (fin.ext _),
  simp,
end

lemma algebra_map_mul_algebra_map (r s : R) :
  reindex R M (equiv.cast $ by rw add_zero) (mul (algebra_map r) (algebra_map s)) =
    algebra_map (r * s) :=
begin
  rw [←smul_eq_mul, linear_equiv.map_smul],
  exact algebra_map_mul r (@algebra_map R M _ _ _ s),
end

lemma mul_one {n} (a : ⨂[R]^n M) : reindex R M (equiv.cast $ by rw add_zero) (mul a one) = a :=
by rw [one, mul_algebra_map, one_smul]

lemma mul_assoc {na nb nc} (a : ⨂[R]^na M) (b : ⨂[R]^nb M)  (c : ⨂[R]^nc M) :
  reindex R M (equiv.cast $ by rw add_assoc) (mul (mul a b) c) = (mul a $ mul b c) :=
begin
  let e : ⨂[R]^(na + nb + nc) M ≃ₗ[R] ⨂[R]^(na + (nb + nc)) M :=
    reindex R M (equiv.cast $ by rw add_assoc),
  let lhs : (⨂[R]^na M) →ₗ[R] (⨂[R]^nb M) →ₗ[R] (⨂[R]^nc M) →ₗ[R] (⨂[R]^(na + (nb + nc)) M) :=
    (linear_map.llcomp R _ _ _ ((@mul R M _ _ _ _ nc).compr₂ e.to_linear_map)).comp
      (@mul R M _ _ _ na nb),
  have lhs_eq : ∀ a b c, lhs a b c = e (mul (mul a b) c) := λ _ _ _, rfl,
  let rhs : (⨂[R]^na M) →ₗ[R] (⨂[R]^nb M) →ₗ[R] (⨂[R]^nc M) →ₗ[R] (⨂[R]^(na + (nb + nc)) M) :=
    (linear_map.llcomp R _ _ _ (linear_map.lflip R _ _ _) $
      (linear_map.llcomp R _ _ _ (@mul R M _ _ _ na _).flip).comp (@mul R M _ _ _ nb nc)).flip,
  have rhs_eq : ∀ a b c, rhs a b c = (mul a $ mul b c) := λ _ _ _, rfl,
    -- (linear_map.lcomp (@mul R M _ _ _ na nb)).comp (@mul R M _ _ _ (na + nb) nc),
  suffices : lhs = rhs,
  from linear_map.congr_fun (linear_map.congr_fun (linear_map.congr_fun this a) b) c,
  ext a b c,
  simp only [linear_map.comp_multilinear_map_apply, lhs_eq, rhs_eq, tprod_mul_tprod, e,
    reindex_tprod],
  congr' with j,
  rw fin.append'_assoc,
  refine congr_arg (fin.append' a (fin.append' b c)) (fin.ext _),
  simp,
  sorry,
end

instance gmonoid : graded_monoid.gmonoid (λ i, ⨂[R]^i M) :=
{ mul := λ i j a b, mul a b,
  one := one,
  one_mul := λ a, sigma_eq_of_reindex_cast (zero_add _) (one_mul _),
  mul_one := λ a, sigma_eq_of_reindex_cast (add_zero _) (mul_one _),
  mul_assoc := λ a b c, sigma_eq_of_reindex_cast (add_assoc _ _ _) (mul_assoc _ _ _),
  gnpow := sorry,
  gnpow_zero' := sorry,
  gnpow_succ' := sorry }

instance gsemiring : direct_sum.gsemiring (λ i, ⨂[R]^i M) :=
{ mul_zero := λ i j a, linear_map.map_zero _,
  zero_mul := λ i j b, linear_map.map_zero₂ _ _,
  mul_add := λ i j a b₁ b₂, linear_map.map_add _ _ _,
  add_mul := λ i j a₁ a₂ b, linear_map.map_add₂ _ _ _ _,
  ..tensor_power.gmonoid }

instance galgebra : direct_sum.galgebra R (λ i, ⨂[R]^i M) :=
{ to_fun := (tensor_power.algebra_map : R ≃ₗ[R] ⨂[R]^0 M) .to_linear_map.to_add_monoid_hom,
  map_one := rfl,
  map_mul := λ r s, sigma_eq_of_reindex_cast rfl begin
    rw [←linear_equiv.eq_symm_apply],
    have := algebra_map_mul_algebra_map r s,
    exact this.symm,
  end,
  commutes := λ r x, sigma_eq_of_reindex_cast (add_comm _ _) begin
    have := (algebra_map_mul r x.snd).trans (mul_algebra_map r x.snd).symm,
    rw [←linear_equiv.eq_symm_apply, reindex_symm, equiv.cast_symm],
    rw [←linear_equiv.eq_symm_apply, reindex_symm, reindex_reindex, equiv.cast_symm,
      equiv.cast_trans] at this,
    exact this,
  end,
  smul_def := λ r x, sigma_eq_of_reindex_cast (zero_add x.fst).symm begin
    rw [←linear_equiv.eq_symm_apply, reindex_symm],
    exact (algebra_map_mul r x.snd).symm,
  end }

open_locale direct_sum

/-- While this is an instance, lean is incapable of finding it. -/
instance semiring : semiring (⨁ n : ℕ, ⨂[R]^n M) := by apply_instance

/-- TODO: show this is isomorphic to the `tensor_algebra R M`. -/
instance algebra : algebra R (⨁ n : ℕ, ⨂[R]^n M) := by apply_instance

end tensor_power
