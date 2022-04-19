/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.normed_space.basic
import analysis.normed_space.pi_Lp

/-!
# Matrices as a normed space

In this file we provide the following non-instances on matrices, using the elementwise norm:

* `matrix.semi_normed_group`
* `matrix.normed_group`
* `matrix.normed_space`

These are not declared as instances because there are several natural choices for defining the norm
of a matrix.
-/

noncomputable theory

open_locale nnreal

namespace finset
lemma prod_sup_mul_le_mul_sup_of_nonneg {ι κ α} [linear_ordered_semiring α] [order_bot α]
  {a : ι → α} {b : κ → α} (s : finset ι) (t : finset κ)
  (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ t, 0 ≤ b i)  :
  (s.product t).sup (λ p, a p.1 * b p.2) ≤ s.sup a * t.sup b :=
finset.sup_le $ λ i hi,
  let ⟨hs, ht⟩ := finset.mem_product.mp hi in
    mul_le_mul (le_sup hs) (le_sup ht) (hb _ ht) ((ha _ hs).trans $ le_sup hs)

end finset

namespace matrix

variables {R l n m α : Type*} [fintype n] [fintype m] [fintype l]

section semi_normed_group
variables [semi_normed_group α]

/-- Seminormed group instance (using sup norm of sup norm) for matrices over a seminormed ring. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def semi_normed_group : semi_normed_group (matrix n m α) :=
pi.semi_normed_group

local attribute [instance] matrix.semi_normed_group

lemma norm_le_iff {r : ℝ} (hr : 0 ≤ r) {A : matrix n m α} :
  ∥A∥ ≤ r ↔ ∀ i j, ∥A i j∥ ≤ r :=
by simp [pi_norm_le_iff hr]

lemma nnnorm_le_iff {r : ℝ≥0} {A : matrix n m α} :
  ∥A∥₊ ≤ r ↔ ∀ i j, ∥A i j∥₊ ≤ r :=
by simp [pi_nnnorm_le_iff]

lemma norm_lt_iff {r : ℝ} (hr : 0 < r) {A : matrix n m α} :
  ∥A∥ < r ↔ ∀ i j, ∥A i j∥ < r :=
by simp [pi_norm_lt_iff hr]

lemma nnnorm_lt_iff {r : ℝ≥0} (hr : 0 < r) {A : matrix n m α} :
  ∥A∥₊ < r ↔ ∀ i j, ∥A i j∥₊ < r :=
by simp [pi_nnnorm_lt_iff hr]

lemma norm_entry_le_entrywise_sup_norm (A : matrix n m α) {i : n} {j : m} :
  ∥A i j∥ ≤ ∥A∥ :=
(norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)

lemma nnnorm_entry_le_entrywise_sup_nnorm (A : matrix n m α) {i : n} {j : m} :
  ∥A i j∥₊ ≤ ∥A∥₊ :=
(nnnorm_le_pi_nnnorm (A i) j).trans (nnnorm_le_pi_nnnorm A i)

end semi_normed_group

/-- Normed group instance (using sup norm of sup norm) for matrices over a normed ring.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def normed_group [normed_group α] : normed_group (matrix n m α) :=
pi.normed_group

section normed_space
local attribute [instance] matrix.semi_normed_group

variables [normed_field R] [semi_normed_group α] [normed_space R α]

/-- Normed space instance (using sup norm of sup norm) for matrices over a normed field.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def normed_space : normed_space R (matrix n m α) :=
pi.normed_space

end normed_space

section l0_linf

instance l0_linf_semi_normed_group [semi_normed_group α] :
  semi_normed_group (matrix m n α) :=
(by apply_instance : semi_normed_group (m → pi_Lp 1 (λ j : n, α)))

instance l0_linf_normed_group [normed_group α] :
  normed_group (matrix m n α) :=
(by apply_instance : normed_group (m → pi_Lp 1 (λ j : n, α)))

instance l0_linf_normed_space [normed_field R] [semi_normed_group α] [normed_space R α] :
  normed_space R (matrix m n α) :=
(by apply_instance : normed_space R (m → pi_Lp 1 (λ j : n, α)))

open_locale nnreal big_operators

lemma l0_linf_norm_def [semi_normed_group α] (A : matrix m n α) :
  ∥A∥ = ((finset.univ : finset m).sup (λ i : m, ∑ j : n, ∥A i j∥₊) : ℝ≥0) :=
begin
  dunfold has_norm.norm,
  simp_rw [pi_Lp.nnnorm_eq, div_one, nnreal.rpow_one],
end

lemma l0_linf_nnnorm_def [semi_normed_group α] (A : matrix m n α) :
  ∥A∥₊ = (finset.univ : finset m).sup (λ i : m, ∑ j : n, ∥A i j∥₊) :=
subtype.ext $ l0_linf_norm_def A

open_locale matrix

lemma nnorm_mul_vec [semi_normed_ring α] (A : matrix l m α) (v : m → α) :
  ∥matrix.mul_vec A v∥₊ ≤ ∥A∥₊ * ∥v∥₊ :=
begin
  change subtype.mk (coe _) _ ≤ _ *  subtype.mk (coe _) _,
  erw [subtype.eta, subtype.eta],
  simp_rw [l0_linf_nnnorm_def, matrix.mul_vec, matrix.dot_product],
  calc finset.univ.sup (λ b, ∥∑ i, A b i * v i∥₊)
    ≤ finset.univ.sup (λ b, ∑ i, ∥A b i∥₊ * ∥v i∥₊) :
      finset.sup_mono_fun (λ i hi, (nnnorm_sum_le _ _).trans $
        finset.sum_le_sum $ λ j hj, nnnorm_mul_le _ _)
  ... ≤ finset.univ.sup (λ i, ∑ j, ∥A i j∥₊ * finset.univ.sup (λ b, ∥v b∥₊)) :
    finset.sup_mono_fun (λ i hi,
      finset.sum_le_sum $ λ j hj,
        mul_le_mul_of_nonneg_left (finset.le_sup hj) (nnreal.coe_nonneg _))
  ... = finset.univ.sup (λ i, ∑ j, ∥A i j∥₊) * finset.univ.sup (λ b, ∥v b∥₊) :
    by rw finset_sup_mul,
end

lemma l0_linf_nnnorm_mul [semi_normed_ring α] (A : matrix l m α) (B : matrix m n α) :
  ∥A ⬝ B∥₊ ≤ ∥A∥₊ * ∥B∥₊ :=
begin
  simp_rw [l0_linf_nnnorm_def, matrix.mul_apply],
  transitivity finset.univ.sup (λ (i : l), ∑ (k : n), ∑ (j : m), ∥A i j∥₊ * ∥B j k∥₊),
  { refine finset.sup_mono_fun (λ x hx, finset.sum_le_sum (λ i hi, _)),
    apply (nnnorm_sum_le _ _).trans (finset.sum_le_sum (λ j hj, _)),
    exact nnnorm_mul_le _ _ },
  simp_rw [@finset.sum_comm _ m n],
  refine le_trans _ (finset.prod_sup_mul_le_mul_sup_of_nonneg finset.univ finset.univ
    (λ i hi, nnreal.zero_le_coe) (λ i hi, nnreal.zero_le_coe)),
  rw finset.sup_product_left,
  refine finset.sup_mono_fun (λ i hi, _),
  simp_rw [ finset.sum_mul, ← finset.mul_sum],
  casesI is_empty_or_nonempty m,
  { simp },
  inhabit m,
  refine le_trans _ (finset.le_sup $ finset.mem_univ (_ : m)),
  swap,

  -- transitivity finset.univ.sup (λ (i : l), ∑ (x : m), ∥A i x∥₊ * ∑ (x_1 : n), ∥B x x_1∥₊),
  -- refine (finset.sup_mul_le_mul_sup_of_nonneg _ _ _).trans _,
  -- transitivity ∑ (i : n) (a : m), ∥A x a∥₊ * ∥B a i∥₊,
  -- refine le_trans _ (finset.prod_sup_mul_le_mul_sup_of_nonneg finset.univ finset.univ
  --   (λ i hi, nnreal.zero_le_coe) (λ i hi, nnreal.zero_le_coe)),
  -- simp_rw [finset.sum_mul_sum, finset.sup_product_left, finset.sum_product_right],
  -- refine finset.sup_mono_fun (λ x hx, _),
  -- refine (finset.sum_le_sum (λ i hi, _)).trans _,
  -- rotate 1,
  -- { exact nnnorm_sum_le _ _ },
  -- transitivity ∑ (i : n) (a : m), ∥A x a∥₊ * ∥B a i∥₊,
  -- { refine finset.sum_le_sum (λ i hi, finset.sum_le_sum (λ j hj, nnnorm_mul_le _ _)) },
  -- rw finset.sup_add
  -- casesI is_empty_or_nonempty m,
  -- { simp },
  -- inhabit m,
  -- refine le_trans _ (finset.le_sup $ finset.mem_univ (default : m)),
  -- refine (finset.sum_le_sum (λ i hi, finset.sum_le_sum $ λ j hj, nnnorm_mul_le _ _)).trans _,
  -- refine le_trans _ (finset.le_sup hx),
  -- apply finset.le_sup
  -- refine (λ x, ∑ j : m × n, ∥A x.1 j.1 * B x.2 j.2∥₊),
  -- rotate 1,
  -- refine finset.sum_le_sum (λ i hi, nnnorm_mul_le _ _),
  -- rw [←finset.univ_product_univ, finset.sup_product_left],
  -- refine
  -- refine le_trans _ (nnnorm_mul_le _ _),
  -- refine (finset.sup_mono_fun $ λ x hx, finset.sum_le_sum $ λ i hi, _).trans _,
  -- rw finset.sup_mul_le_mul_sup_of_nonneg,
  -- rw [←nnreal.mul_rpow],
  -- simp_rw [matrix.mul_apply],
  -- rw @finset.sum_comm _ n m,
  -- rw [finset.sum_mul_sum, finset.sum_product],
  -- refine nnreal.rpow_le_rpow _ one_half_pos.le,
  -- refine finset.sum_le_sum (λ i hi, finset.sum_le_sum $ λ j hj, _),
  -- rw [← nnreal.rpow_le_rpow_iff one_half_pos, ← nnreal.rpow_mul,
  --   mul_div_cancel' (1 : ℝ) two_ne_zero, nnreal.rpow_one, nnreal.mul_rpow,
  --     ←pi_Lp.nnorm_eq, ←pi_Lp.nnorm_eq],
  -- dsimp,
  -- let a : pi_Lp 2 _ := A i,
  -- let a' : pi_Lp 2 _ := λ j, star (a j),
  -- let b : pi_Lp 2 _ := λ k, B k j,
  -- letI : inner_product_space α (pi_Lp 2 (λ i : m, α)) := pi_Lp.inner_product_space _,
  -- change ∥∑ k, a k * b k∥₊ ≤ ∥a∥₊ * ∥b∥₊,
  -- convert nnorm_inner_le_nnorm a' b using 2,
  -- { simp,
  --   simp_rw [star_ring_end_apply, star_star], },
  -- simp [pi_Lp.nnorm_eq, a'],
  -- simp_rw [star_ring_end_apply, nnorm_star],
end

-- /-- Matrices are a normed ring wrt the `L1-to-L∞` norm. -/
-- def matrix.normed_ring : normed_ring (matrix n n 𝕜) :=
-- { norm_mul := sorry,
--   .. matrix.ring,
--   .. matrix.normed_group' 𝕜 n n }

end l0_linf

end matrix
