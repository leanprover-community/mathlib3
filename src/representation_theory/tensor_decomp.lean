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

variables {k G : Type u} [comm_ring k] [group G] {n : ℕ}
open_locale tensor_product

namespace Rep

/-- Sends `(g₁, ..., gₙ) ↦ (1, g₁, g₁g₂, ..., g₁...gₙ)` -/
private def to_prod (f : fin n → G) : fin (n + 1) → G :=
λ i, ((list.of_fn f).take i).prod

@[simp] lemma to_prod_zero (f : fin n → G) :
  to_prod f 0 = 1 :=
by simp [to_prod]

lemma to_prod_succ (f : fin n → G) (j : fin n) :
  to_prod f j.succ = to_prod f j.cast_succ * (f j) :=
by simp [to_prod, list.take_succ, list.of_fn_nth_val, dif_pos j.is_lt, ←option.coe_def]

lemma to_prod_succ' (f : fin (n + 1) → G) (j : fin (n + 1)) :
  to_prod f j.succ = f 0 * to_prod (fin.tail f) j :=
by simpa [to_prod]

variables (k G n)

/-- The `k`-linear map from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` sending `(g₀, ..., gₙ)`
to `g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)` -/
def to_tensor_aux : mul_action_to_Rep k G (fin (n + 1) → G) →ₗ[k] monoid_algebra k G
  ⊗[k] mul_action_to_Rep k G (fin n → G) :=
finsupp.lift (monoid_algebra k G ⊗[k] mul_action_to_Rep k G (fin n → G)) k (fin (n + 1) → G)
  (λ x, finsupp.single (x 0) 1 ⊗ₜ[k] finsupp.single (λ i, (x i)⁻¹ * x i.succ) 1)

variables {k G n}

lemma to_tensor_single (f : fin (n + 1) → G) (m : k) :
  to_tensor_aux k G n (finsupp.single f m) =
    (finsupp.single (f 0) m) ⊗ₜ (finsupp.single (λ i, (f i)⁻¹ * f i.succ) 1) :=
begin
  erw [finsupp.lift_apply, finsupp.sum_single_index, tensor_product.smul_tmul'],
  { simp },
  { simp },
end

variables (k G n)

/-- The `k[G]`-linear map from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` sending `(g₀, ..., gₙ)`
to `g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)` -/
def to_tensor : mul_action_to_Rep k G (fin (n + 1) → G) →ₗ[monoid_algebra k G] monoid_algebra k G
  ⊗[k] mul_action_to_Rep k G (fin n → G) :=
monoid_algebra.equivariant_of_linear_of_comm (to_tensor_aux k G n) $ λ g x,
map_smul_of_map_smul_of _ _ (λ h x, by simp [of_smul_of, single_smul_single, to_tensor_single,
  tensor_product.smul_tmul', mul_assoc]) _ _

/-- The `k`-linear map from `k[G] ⊗ₖ k[Gⁿ]` to `k[Gⁿ⁺¹]` sending `g ⊗ (g₁, ..., gₙ)` to
`(g, gg₁, gg₁g₂, ..., gg₁...gₙ)` -/
def of_tensor_aux : monoid_algebra k G ⊗[k] mul_action_to_Rep k G (fin n → G)
    →ₗ[k] mul_action_to_Rep k G (fin (n + 1) → G) :=
tensor_product.lift (finsupp.lift _ _ _ $ λ g, finsupp.lift _ _ _
  (λ f, monoid_algebra.of _ (fin (n + 1) → G) (g • to_prod f)))

variables {k G n}

lemma of_tensor_single (g : G) (m : k) (x : mul_action_to_Rep k G (fin n → G)) :
  of_tensor_aux k G n ((finsupp.single g m) ⊗ₜ x) =
  finsupp.lift (mul_action_to_Rep k G (fin (n + 1) → G)) k (fin n → G)
    (λ f, finsupp.single (g • to_prod f) m) x :=
by simp [of_tensor_aux, finsupp.sum_single_index, finsupp.smul_sum, mul_comm m]

lemma of_tensor_single' (g : monoid_algebra k G) (x : fin n → G) (r : k) :
  of_tensor_aux k G n (g ⊗ₜ finsupp.single x r) =
    finsupp.lift _ k G (λ a, finsupp.single (a • to_prod x) r) g :=
by simp [of_tensor_aux]

variables (k G n)

/-- The `k`-linear map from `k[G] ⊗ₖ k[Gⁿ]` to `k[Gⁿ⁺¹]` sending `g ⊗ (g₁, ..., gₙ)` to
`(g, gg₁, gg₁g₂, ..., gg₁...gₙ)` -/
def of_tensor : monoid_algebra k G ⊗[k] mul_action_to_Rep k G (fin n → G)
  →ₗ[monoid_algebra k G] mul_action_to_Rep k G (fin (n + 1) → G) :=
monoid_algebra.equivariant_of_linear_of_comm (of_tensor_aux k G n) $ λ g x,
begin
  refine tensor_product.induction_on x (by simp) (λ x y, _) (λ y z hz hy, by simp only
    [smul_add, linear_map.map_add, hy, hz]),
  { erw [←finsupp.sum_single x, tensor_product.sum_tmul],
    simp only [finset.smul_sum, linear_map.map_sum],
    refine finset.sum_congr rfl (λ f hf, _),
    simp only [tensor_product.smul_tmul', smul_eq_mul, monoid_algebra.single_mul_single, one_mul,
      of_tensor_single, ←linear_map.map_smul, finsupp.lift_apply, finsupp.smul_sum],
    exact finsupp.sum_congr (λ j hj, by rw [smul_comm (_ : monoid_algebra k G), single_smul_single,
      one_mul, smul_smul]; apply_instance) },
end

variables {k G n}

lemma equiv_tensor_left_inv_aux (f : fin (n + 1) → G) :
  f 0 • to_prod (λ i : fin n, (f i)⁻¹ * f i.succ) = f :=
funext $ λ ⟨x, hn⟩,
begin
  revert hn,
  induction x with x hx,
  { simp },
  { intro hn,
    dsimp at hx ⊢,
    rw [←fin.succ_mk _ _ (nat.succ_lt_succ_iff.1 hn), to_prod_succ],
    erw [←mul_assoc, hx (lt_trans (nat.lt_succ_self x) hn)],
    convert mul_inv_cancel_left _ _,
    ext,
    simp [nat.mod_eq_of_lt (lt_trans (nat.lt_succ_self _) hn)] }
end

lemma equiv_tensor_right_inv_aux (g : G) (f : fin n → G) (i : fin n) :
  ((g • to_prod f) i)⁻¹ * (g • to_prod f) i.succ = f i :=
begin
  cases i with i hn,
  revert hn,
  induction i with i hi,
  { intro hn,
    simp [←fin.succ_mk, to_prod_succ] },
  { intro hn,
    specialize hi (lt_trans (nat.lt_succ_self i) hn),
    simp only [mul_inv_rev, fin.coe_eq_cast_succ, fin.succ_mk, fin.cast_succ_mk,
      smul_eq_mul, pi.smul_apply] at hi ⊢,
    rw [←fin.succ_mk _ _ (lt_trans (nat.lt_succ_self _) hn), ←fin.succ_mk],
    simp only [to_prod_succ, mul_inv_rev, fin.cast_succ_mk],
    assoc_rw [hi, inv_mul_cancel_left] }
end

open monoid_algebra (lift) (of)

lemma equiv_tensor_left_inv (x : mul_action_to_Rep k G (fin (n + 1) → G)) :
  of_tensor _ _ _ (to_tensor _ _ _ x) = x :=
begin
  refine add_monoid_hom.ext_iff.1 (@finsupp.add_hom_ext _ _ _ _ _
    ((of_tensor k G n).comp (to_tensor k G n)).to_add_monoid_hom
    (add_monoid_hom.id _) (λ x y, _)) x,
  dsimp,
  erw [to_tensor_single, of_tensor_single],
  rw [finsupp.lift_apply, finsupp.sum_single_index, one_smul, equiv_tensor_left_inv_aux],
  { rw zero_smul }
end

lemma equiv_tensor_right_inv (x : monoid_algebra k G ⊗[k] mul_action_to_Rep k G (fin n → G)) :
  to_tensor _ _ _ (of_tensor _ _ _ x) = x :=
begin
  refine tensor_product.induction_on x (by simp) (λ y z, _) (λ z w hz hw, by simp [hz, hw]),
  erw [←finsupp.sum_single y, tensor_product.sum_tmul],
  simp only [finset.smul_sum, linear_map.map_sum],
  refine finset.sum_congr rfl (λ f hf, _),
  simp only [of_tensor, of_tensor_single, finsupp.lift_apply, finsupp.smul_single',
    linear_map.map_finsupp_sum, to_tensor, monoid_algebra.equivariant_of_linear_of_comm_apply,
    to_tensor_single, equiv_tensor_right_inv_aux],
  dsimp,
  simp only [to_prod_zero, mul_one],
  conv_rhs {rw ←finsupp.sum_single z},
  erw tensor_product.tmul_sum,
  exact finset.sum_congr rfl (λ g hg, show _ ⊗ₜ _ = _, by
    rw [←finsupp.smul_single', tensor_product.smul_tmul, finsupp.smul_single_one])
end

variables (k G n)

/-- A `k[G]`-linear isomorphism `k[Gⁿ⁺¹] ≅ k[G] ⊗ₖ k[Gⁿ]` -/
def equiv_tensor : mul_action_to_Rep k G (fin (n + 1) → G) ≃ₗ[monoid_algebra k G] monoid_algebra k G
  ⊗[k] mul_action_to_Rep k G (fin n → G) :=
{ inv_fun := of_tensor _ G n,
  left_inv := equiv_tensor_left_inv,
  right_inv := equiv_tensor_right_inv,
  ..to_tensor k G n }

variables {k G n}

@[simp] lemma equiv_tensor_single (x : fin (n + 1) → G) (m : k) :
  equiv_tensor k G n (finsupp.single x m) = (finsupp.single (x 0) m) ⊗ₜ
    (finsupp.single (λ i, (x i)⁻¹ * x i.succ) 1) :=
to_tensor_single _ _

@[simp] lemma equiv_tensor_symm_apply (g : G) (m : k) (x : mul_action_to_Rep k G (fin n → G)) :
  (equiv_tensor _ G n).symm ((finsupp.single g m) ⊗ₜ x) =
  finsupp.lift (mul_action_to_Rep k G (fin (n + 1) → G)) k (fin n → G)
    (λ f, finsupp.single (g • to_prod f) m) x :=
of_tensor_single _ _ _

end Rep
