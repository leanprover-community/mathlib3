/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import linear_algebra.tensor_product
import ring_theory.tensor_product
import representation_theory.monoid_algebra_basis

/-!
# The `k[G]`-linear isomorphism `k[Gⁿ⁺¹] ≅ k[G] ⊗[k] k[Gⁿ]`

## Main definitions

  *
## Implementation notes

-/

universes v u
noncomputable theory

variables (k : Type u) [comm_ring k] (G : Type u) [group G]
open_locale tensor_product

variables (M : Type u) [add_comm_group M] [distrib_mul_action G M] (n : ℕ)
variables {G n}

def to_prod (f : fin n → G) : fin (n + 1) → G :=
λ i, ((list.of_fn f).take i).prod

lemma to_prod_zero (f : fin n → G) :
  to_prod f 0 = 1 :=
begin
  unfold to_prod,
  simp only [fin.coe_zero, list.take_zero, list.prod_nil],
end

lemma to_prod_succ (f : fin n → G) (j : fin n) :
  to_prod f j.succ = to_prod f j.cast_succ * (f j) :=
begin
  unfold to_prod,
  simp only [fin.coe_succ, fin.coe_cast_succ],
  rw list.take_succ,
  simp only [mul_right_inj, list.prod_append, list.nth_of_fn],
  rw [list.of_fn_nth_val, dif_pos j.is_lt, fin.eta],
  erw option.to_list_some,
  rw list.prod_singleton
end

lemma to_prod_succ' (f : fin (n + 1) → G) (j : fin (n + 1)) :
  to_prod f j.succ = f 0 * to_prod (fin.tail f) j :=
begin
  unfold to_prod,
  simp only [mul_right_inj, fin.coe_eq_cast_succ, list.take, fin.coe_succ,
    fin.coe_cast_succ, list.of_fn_succ, list.prod_cons],
  refl,
end

variables (G n)

namespace Rep

@[simps] def to_tensor_aux : mul_action_to_Rep k G (fin (n + 1) → G) →ₗ[k] monoid_algebra k G
  ⊗[k] mul_action_to_Rep k G (fin n → G) :=
finsupp.lift (monoid_algebra k G ⊗[k] mul_action_to_Rep k G (fin n → G)) k (fin (n + 1) → G)
  (λ x, finsupp.single (x 0) 1 ⊗ₜ[k] finsupp.single (λ i, (x i)⁻¹ * x i.succ) 1)

lemma to_tensor_single (f : fin (n + 1) → G) (m : k) :
  to_tensor_aux k G n (finsupp.single f m) =
    (finsupp.single (f 0) m) ⊗ₜ (finsupp.single (λ i, (f i)⁻¹ * f i.succ) 1) :=
begin
  erw [finsupp.lift_apply, finsupp.sum_single_index, tensor_product.smul_tmul'],
  { simp },
  { simp },
end

def to_tensor : mul_action_to_Rep k G (fin (n + 1) → G) →ₗ[monoid_algebra k G] monoid_algebra k G
  ⊗[k] mul_action_to_Rep k G (fin n → G) :=
monoid_algebra.equivariant_of_linear_of_comm (to_tensor_aux k G n) $ λ g x,
begin
  refine map_smul_of_map_smul_of _ _ _ _ _,
  intros h x,
  rw of_smul_of,
  simp only [monoid_algebra.of_apply, single_smul_single, one_smul, one_mul, to_tensor_single],
  dsimp,
  simp only [mul_inv_rev, tensor_product.smul_tmul', smul_eq_mul],
  erw [monoid_algebra.single_mul_single, one_mul],
  congr,
  ext,
  assoc_rw inv_mul_cancel_left,
end

def of_tensor_aux :
  monoid_algebra k G ⊗[k] mul_action_to_Rep k G (fin n → G)
    →ₗ[k] mul_action_to_Rep k G (fin (n + 1) → G) :=
tensor_product.lift (finsupp.lift _ _ _ $ λ g, finsupp.lift _ _ _
  (λ f, monoid_algebra.of _ (fin (n + 1) → G) (g • to_prod f)))

lemma of_tensor_single (g : G) (m : k) (x : mul_action_to_Rep k G (fin n → G)) :
  of_tensor_aux k G n ((finsupp.single g m) ⊗ₜ x) =
  m • finsupp.lift (mul_action_to_Rep k G (fin (n + 1) → G)) k (fin n → G)
    (λ f, monoid_algebra.of _ _ (g • to_prod f)) x :=
begin
  unfold of_tensor_aux,
  dsimp,
  rw tensor_product.lift.tmul,
  dsimp,
  rw finsupp.sum_single_index,
  refl,
  { rw zero_smul }
end

lemma of_tensor_single' (g : monoid_algebra k G) (x : fin n → G) (r : k) :
  of_tensor_aux k G n (g ⊗ₜ finsupp.single x r) =
    finsupp.lift _ k G (λ a, finsupp.single (a • to_prod x) r) g :=
begin
  dsimp [of_tensor_aux],
  simp,
end

def of_tensor : monoid_algebra k G ⊗[k] mul_action_to_Rep k G (fin n → G)
  →ₗ[monoid_algebra k G] mul_action_to_Rep k G (fin (n + 1) → G) :=
monoid_algebra.equivariant_of_linear_of_comm (of_tensor_aux k G n) $ λ g x,
begin
  refine tensor_product.induction_on x _ _ _,
  { simp only [smul_zero, map_zero] },
  { intros x y,
    rw ←finsupp.sum_single x,
    erw tensor_product.sum_tmul,
    simp only [finset.smul_sum, linear_map.map_sum],
    congr,
    ext1 f,
    rw [tensor_product.smul_tmul', smul_eq_mul, monoid_algebra.single_mul_single, one_mul,
      of_tensor_single, of_tensor_single],
    simp only [←linear_map.map_smul],
    dsimp,
    rw finsupp.smul_sum,
    congr,
    ext1 f, ext1 j,
    rw [smul_comm (_ : monoid_algebra k G), single_smul_single, one_mul, smul_smul],
    apply_instance },
  { intros x y hx hy,
    simp only [smul_add, linear_map.map_add, hx, hy], },
end

lemma equiv_tensor_left_inv_aux (f : fin (n + 1) → G) :
  f 0 • to_prod (λ i : fin n, (f i)⁻¹ * f i.succ) = f :=
begin
  ext,
  cases x with x hn,
  revert hn,
  induction x with x hx,
  { intro hn,
    dsimp,
    rw [to_prod_zero, mul_one] },
  { intro hn,
    dsimp at hx ⊢,
    rw [←fin.succ_mk _ _ (nat.succ_lt_succ_iff.1 hn), to_prod_succ],
    specialize hx (lt_trans (nat.lt_succ_self x) hn),
    erw [←mul_assoc, hx],
    convert mul_inv_cancel_left _ _,
    ext,
    simp only [fin.coe_of_nat_eq_mod, fin.coe_mk, nat.mod_eq_of_lt
      (lt_trans (nat.lt_succ_self _) hn)] }
end

lemma equiv_tensor_right_inv_aux (g : G) (f : fin n → G) (i : fin n) :
  ((g • to_prod f) i)⁻¹ * (g • to_prod f) i.succ = f i :=
begin
  cases i with i hn,
  revert hn,
  induction i with i hi,
  { intro hn,
    dsimp,
    rw [←fin.succ_mk, to_prod_succ],
    simp only [fin.mk_zero, to_prod_zero, mul_one, mul_left_eq_self,
      inv_mul_cancel_left, fin.cast_succ_mk] },
  { intro hn,
    specialize hi (lt_trans (nat.lt_succ_self i) hn),
    simp only [mul_inv_rev, fin.coe_eq_cast_succ, fin.succ_mk, fin.cast_succ_mk,
      smul_eq_mul, pi.smul_apply] at hi ⊢,
    rw [←fin.succ_mk _ _ (lt_trans (nat.lt_succ_self _) hn), ←fin.succ_mk,
      to_prod_succ, to_prod_succ],
    simp only [mul_inv_rev, fin.cast_succ_mk],
    assoc_rw [hi, inv_mul_cancel_left] }
end

open monoid_algebra (lift) (of)

lemma equiv_tensor_left_inv (x : mul_action_to_Rep k G (fin (n + 1) → G)) :
  of_tensor _ _ _ (to_tensor _ _ _ x) = x :=
begin
  refine add_monoid_hom.ext_iff.1 (@finsupp.add_hom_ext _ _ _ _ _
    ((of_tensor k G n).comp (to_tensor k G n)).to_add_monoid_hom (add_monoid_hom.id _) _) x,
  intros x y,
  dsimp,
  erw [to_tensor_single, of_tensor_single],
  rw [finsupp.lift_apply, finsupp.sum_single_index, one_smul, monoid_algebra.of_apply,
    finsupp.smul_single_one, equiv_tensor_left_inv_aux],
  { rw zero_smul }
end

lemma equiv_tensor_right_inv (x : monoid_algebra k G ⊗[k] mul_action_to_Rep k G (fin n → G)) :
  to_tensor _ _ _ (of_tensor _ _ _ x) = x :=
begin
  { refine tensor_product.induction_on x _ _ _,
    { simp only [linear_map.to_fun_eq_coe, map_zero] },
    { intros y z,
      rw ←finsupp.sum_single y,
      erw tensor_product.sum_tmul,
      simp only [finset.smul_sum, linear_map.map_sum],
      congr,
      ext1 f,
      dsimp [of_tensor],
      rw [of_tensor_single, linear_map.map_smul_of_tower, finsupp.lift_apply],
      simp only [mul_one, finsupp.smul_single', monoid_algebra.of_apply, linear_map.map_finsupp_sum],
      unfold to_tensor,
      simp only [monoid_algebra.equivariant_of_linear_of_comm_apply, to_tensor_single,
        equiv_tensor_right_inv_aux],
      dsimp,
      simp only [to_prod_zero, mul_one],
      conv_rhs {rw ←finsupp.sum_single z},
      rw [←finsupp.smul_single_one f, ←tensor_product.smul_tmul'],
      erw tensor_product.tmul_sum,
      refine congr_arg _ (finset.sum_congr rfl _),
      intros g hg,
      rw [←finsupp.smul_single_one g, ←tensor_product.smul_tmul, finsupp.smul_single_one] },
    { intros z w hz hw,
      simp only [map_add, hz, hw] } }
end

def equiv_tensor : mul_action_to_Rep k G (fin (n + 1) → G) ≃ₗ[monoid_algebra k G] monoid_algebra k G
  ⊗[k] mul_action_to_Rep k G (fin n → G) :=
{ inv_fun := of_tensor _ G n,
  left_inv := equiv_tensor_left_inv _ _ _,
  right_inv := equiv_tensor_right_inv _ _ _,
  ..to_tensor k G n }

@[simp] lemma equiv_tensor_apply (x : fin (n + 1) → G) (m : k) :
  equiv_tensor k G n (finsupp.single x m) = (finsupp.single (x 0) m) ⊗ₜ
    (finsupp.single (λ i, (x i)⁻¹ * x i.succ) 1) :=
to_tensor_single _ _ _ _ _

@[simp] lemma equiv_tensor_symm_apply (g : G) (m : k) (x : mul_action_to_Rep k G (fin n → G)) :
  (equiv_tensor _ G n).symm ((finsupp.single g m) ⊗ₜ x) =
  m • finsupp.lift (mul_action_to_Rep k G (fin (n + 1) → G)) k (fin n → G)
    (λ f, monoid_algebra.of _ _ (g • to_prod f)) x :=
of_tensor_single _ _ _ _ _ _

end Rep
