/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import linear_algebra.pi_tensor_product
import data.equiv.fin
import algebra.direct_sum.algebra

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
((reindex R M fin_zero_equiv').trans pempty_equiv).symm

lemma algebra_map_eq_smul_tprod (r : R) :
  algebra_map r = r • tprod R (λ i : fin 0, (i.elim0 : M)) :=
begin
  simp [algebra_map],
  congr,
end

def one : ⨂[R]^0 M := algebra_map 1

-- TODO: remove after #6243 is merged
instance {α : pempty → Type*} : unique (Π x, α x) :=
⟨⟨λ x, pempty.elim x⟩, λ f, funext $ λ x, pempty.elim x ⟩

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

def _root_.fin.concat {α} {na nb} (a : fin na → α) (b : fin nb → α) : fin (na + nb) → α :=
sum.elim a b ∘ fin_sum_fin_equiv.symm

instance fin.pi_graded_monoid : graded_monoid.gmonoid (λ n, fin n → M) :=
{ mul := λ i j, fin.concat,
  one := fin.elim0,
  one_mul := λ a, sigma.ext (zero_add _) $ function.hfunext (congr_arg _ (zero_add _)) $ λ a b h,
  begin
    dsimp [(*), has_one.one],
    cases h : fin_sum_fin_equiv.symm a,
  end,
  mul_one := _,
  mul_assoc := _,
  gnpow := _,
  gnpow_zero' := _,
  gnpow_succ' := _ }

#exit

lemma tprod_mul_tprod {na nb} (a : fin na → M) (b : fin nb → M) :
  mul (tprod R a) (tprod R b) = (tprod R $ λ i, sum.elim a b (fin_sum_fin_equiv.symm i)) :=
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
  generalize_proofs hi,
  cases h : fin_sum_fin_equiv.symm ((equiv.cast hi).symm i),
  { exact val.elim0, },
  { refine congr_arg a (fin.ext _),
    rw [equiv.symm_apply_eq, fin_sum_fin_equiv_apply_right, fin.ext_iff] at h,
    simpa using h.symm, }
  -- simp [mul, one, mul_equiv, linear_equiv.trans_apply],
  -- change (reindex R M _).to_linear_map.compr₂ mul one a = a,
  -- unfold mul one mul_equiv,
  -- rw [algebra_map_eq_smul_tprod, one_smul],
  -- apply pi_tensor_product.induction_on a,
  -- { intros r a',
  --   simp only [linear_equiv.map_smul,
  --     tensor_product.tmul_smul,
  --     linear_equiv.trans_apply,
  --     tmul_equiv_apply,
  --     reindex_tprod],
  --   congr',
  --   ext,
  --   simp [sum_fin_sum_equiv, equiv.cast], },
  -- { rintros a' b' ha hb,
  --   simp only [linear_equiv.map_add,
  --     tensor_product.tmul_add,
  --     linear_equiv.trans_apply,
  --     tmul_equiv_apply,
  --     reindex_tprod] at *,
  --   rw [ha, hb], },
end

lemma one_mul {n} (a : ⨂[R]^n M) : reindex R M (equiv.cast $ by rw zero_add) (mul one a) = a :=
by rw [one, algebra_map_mul, one_smul]

lemma mul_algebra_map {n} (r : R) (a : ⨂[R]^n M) :
  reindex R M (equiv.cast $ by rw add_zero) (mul a (algebra_map r)) = r • a :=
begin
  unfold mul one mul_equiv,
  rw [algebra_map_eq_smul_tprod, linear_map.map_smul, linear_equiv.map_smul],
  congr' 1,
  show (reindex R M (equiv.refl (fin (n + 0))))
    (reindex R M fin_sum_fin_equiv (tmul_equiv R M (a ⊗ₜ[R] tprod R fin.elim0))) = a,
  apply pi_tensor_product.induction_on a,
  { intros r a',
    change Π i : fin n, M at a',
    rw ←tensor_product.smul_tmul' r (tprod R a') _, swap, apply_instance,
    simp only [linear_equiv.map_smul],
    rw [tmul_equiv_apply, reindex_tprod, reindex_refl, linear_equiv.refl_apply],
    dsimp only,
    congr',
    ext,
    conv_rhs {rw ← (fin_sum_fin_equiv : _ ≃ fin (n + 0)).apply_symm_apply x},
    cases h : (fin_sum_fin_equiv.symm : fin (n + 0) ≃ _) x,
    { rw [fin_sum_fin_equiv_apply_left, sum.elim_inl],
      congr,
      ext,
      refl, },
    { exact val.elim0, }, },
  { rintros a' b' ha hb,
    simp only [linear_equiv.map_add, tensor_product.add_tmul],
    rw [ha, hb], },
end

lemma linear_equiv.apply_eq_iff_eq_symm_apply {R M N} [semiring R] [add_comm_monoid M] [add_comm_monoid N]
  [module R M] [module R N] (e : M ≃ₗ[R] N) {x : M} {y : N} : e x = y ↔ x = e.symm y :=
e.to_equiv.apply_eq_iff_eq_symm_apply

section
set_option pp.implicit true

lemma algebra_map_mul_algebra_map (r s : R) :
  reindex R M (equiv.cast $ by rw add_zero) (mul (algebra_map r) (algebra_map s)) =
    algebra_map (r * s) :=
begin
  have := algebra_map_mul r (@algebra_map R M _ _ _ s),
  rw linear_equiv.apply_eq_iff_eq_symm_apply at this,
  rw [this, ←linear_equiv.trans_apply, reindex_symm, reindex_trans, ←smul_eq_mul,
    linear_equiv.map_smul, linear_equiv.map_smul, equiv.cast_symm, equiv.cast_trans,
    equiv.cast_refl, reindex_refl, linear_equiv.refl_apply],
  refine congr_arg _ _,
  sorry  -- what the heck? This is refl!

end
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
  cases hja : (fin_sum_fin_equiv.symm j) with ja jbc,
  { rw sum.elim_inl, sorry },
  { rw sum.elim_inr,
    cases hjbc : (fin_sum_fin_equiv.symm jbc) with jb jc,
    { rw sum.elim_inl, sorry },
    { rw sum.elim_inr, sorry }, },
end

#check sum.elim


#check vector2
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

instance galgebra : @direct_sum.galgebra _ R (λ i, ⨂[R]^i M) _ _ _ _ _ tensor_power.gsemiring :=
{ to_fun := (tensor_power.algebra_map : R ≃ₗ[R] ⨂[R]^0 M) .to_linear_map.to_add_monoid_hom,
  map_one := rfl,
  map_mul := λ r s, sigma_eq_of_reindex_cast rfl begin
    rw [linear_equiv.apply_eq_iff_eq_symm_apply],
    have := algebra_map_mul_algebra_map r s,
    exact this.symm,
  end,
  commutes := λ r x, sigma_eq_of_reindex_cast (add_comm _ _) begin
    have := (algebra_map_mul r x.snd).trans (mul_algebra_map r x.snd).symm,
    rw [linear_equiv.apply_eq_iff_eq_symm_apply, reindex_symm, equiv.cast_symm],
    rw [linear_equiv.apply_eq_iff_eq_symm_apply, reindex_symm, ←linear_equiv.trans_apply,
      reindex_trans, equiv.cast_symm, equiv.cast_trans] at this,
    exact this,
  end,
  smul_def := λ r x, sigma_eq_of_reindex_cast (zero_add x.fst).symm begin
    rw [linear_equiv.apply_eq_iff_eq_symm_apply, reindex_symm],
    exact (algebra_map_mul r x.snd).symm,
  end }

end tensor_power
