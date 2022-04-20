/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Eric Wieser
-/
import analysis.normed_space.basic
import analysis.normed_space.pi_Lp

/-!
# Matrices as a normed space

In this file we provide the non-instances for norms on matrices:

* the elementwise norm:
  * `matrix.semi_normed_group`
  * `matrix.normed_group`
  * `matrix.normed_space`

* The `L₁-L∞` norm:

  * `matrix.l1_linf_semi_normed_group`
  * `matrix.l1_linf_normed_group`
  * `matrix.l1_linf_normed_space`
  * `matrix.l1_linf_semi_normed_ring`
  * `matrix.l1_linf_normed_ring`
  * `matrix.l1_linf_normed_algebra`

These are not declared as instances because there are several natural choices for defining the norm
of a matrix.
-/

noncomputable theory

open_locale nnreal

namespace finset

lemma product_sup_mul_le_mul_sup_of_nonneg {ι κ α} [linear_ordered_semiring α] [order_bot α]
  {a : ι → α} {b : κ → α} (s : finset ι) (t : finset κ)
  (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ t, 0 ≤ b i)  :
  (s.product t).sup (λ p, a p.1 * b p.2) ≤ s.sup a * t.sup b :=
finset.sup_le $ λ i hi,
  let ⟨hs, ht⟩ := finset.mem_product.mp hi in
    mul_le_mul (le_sup hs) (le_sup ht) (hb _ ht) ((ha _ hs).trans $ le_sup hs)

end finset

namespace matrix

variables {R l m n α : Type*} [fintype l] [fintype m] [fintype n]

section semi_normed_group
variables [semi_normed_group α]

/-- Seminormed group instance (using sup norm of sup norm) for matrices over a seminormed group. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def semi_normed_group : semi_normed_group (matrix m n α) :=
pi.semi_normed_group

local attribute [instance] matrix.semi_normed_group

lemma norm_le_iff {r : ℝ} (hr : 0 ≤ r) {A : matrix m n α} :
  ∥A∥ ≤ r ↔ ∀ i j, ∥A i j∥ ≤ r :=
by simp [pi_norm_le_iff hr]

lemma nnnorm_le_iff {r : ℝ≥0} {A : matrix m n α} :
  ∥A∥₊ ≤ r ↔ ∀ i j, ∥A i j∥₊ ≤ r :=
by simp [pi_nnnorm_le_iff]

lemma norm_lt_iff {r : ℝ} (hr : 0 < r) {A : matrix m n α} :
  ∥A∥ < r ↔ ∀ i j, ∥A i j∥ < r :=
by simp [pi_norm_lt_iff hr]

lemma nnnorm_lt_iff {r : ℝ≥0} (hr : 0 < r) {A : matrix m n α} :
  ∥A∥₊ < r ↔ ∀ i j, ∥A i j∥₊ < r :=
by simp [pi_nnnorm_lt_iff hr]

lemma norm_entry_le_entrywise_sup_norm (A : matrix m n α) {i : m} {j : n} :
  ∥A i j∥ ≤ ∥A∥ :=
(norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)

lemma nnnorm_entry_le_entrywise_sup_nnorm (A : matrix m n α) {i : m} {j : n} :
  ∥A i j∥₊ ≤ ∥A∥₊ :=
(nnnorm_le_pi_nnnorm (A i) j).trans (nnnorm_le_pi_nnnorm A i)

end semi_normed_group

/-- Normed group instance (using sup norm of sup norm) for matrices over a normed group. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def normed_group [normed_group α] : normed_group (matrix m n α) :=
pi.normed_group

section normed_space
local attribute [instance] matrix.semi_normed_group

variables [normed_field R] [semi_normed_group α] [normed_space R α]

/-- Normed space instance (using sup norm of sup norm) for matrices over a normed space. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def normed_space : normed_space R (matrix m n α) :=
pi.normed_space

end normed_space

section l1_linf

/-- Seminormed group instance (using sup norm of L1 norm) for matrices over a seminormed group. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def l1_linf_semi_normed_group [semi_normed_group α] :
  semi_normed_group (matrix m n α) :=
(by apply_instance : semi_normed_group (m → pi_Lp 1 (λ j : n, α)))

/-- Normed group instance (using sup norm of L1 norm) for matrices over a normed ring.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def l1_linf_normed_group [normed_group α] :
  normed_group (matrix m n α) :=
(by apply_instance : normed_group (m → pi_Lp 1 (λ j : n, α)))

local attribute [instance] matrix.l1_linf_semi_normed_group matrix.l1_linf_normed_group

/-- Normed space instance (using sup norm of L1 norm) for matrices over a normed space.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def l1_linf_normed_space [normed_field R] [semi_normed_group α] [normed_space R α] :
  normed_space R (matrix m n α) :=
(by apply_instance : normed_space R (m → pi_Lp 1 (λ j : n, α)))

local attribute [instance] matrix.l1_linf_normed_space

open_locale nnreal big_operators

lemma l1_linf_norm_def [semi_normed_group α] (A : matrix m n α) :
  ∥A∥ = ((finset.univ : finset m).sup (λ i : m, ∑ j : n, ∥A i j∥₊) : ℝ≥0) :=
by simp_rw [pi.norm_def, pi_Lp.nnnorm_eq, div_one, nnreal.rpow_one]

lemma l1_linf_nnnorm_def [semi_normed_group α] (A : matrix m n α) :
  ∥A∥₊ = (finset.univ : finset m).sup (λ i : m, ∑ j : n, ∥A i j∥₊) :=
subtype.ext $ l1_linf_norm_def A

open_locale matrix

@[simp] lemma l1_linf_nnnorm_col [semi_normed_group α] (v : m → α) :
  ∥col v∥₊ = ∥v∥₊ :=
begin
  rw [l1_linf_nnnorm_def, pi.nnnorm_def],
  simp,
end

@[simp] lemma l1_linf_norm_col [semi_normed_group α] (v : m → α) :
  ∥col v∥ = ∥v∥ :=
congr_arg coe $ l1_linf_nnnorm_col v

@[simp] lemma l1_linf_nnnorm_row [semi_normed_group α] (v : n → α) :
  ∥row v∥₊ = ∑ i, ∥v i∥₊ :=
by simp [l1_linf_nnnorm_def]

@[simp] lemma l1_linf_norm_row [semi_normed_group α] (v : n → α) :
  ∥row v∥ = ∑ i, ∥v i∥ :=
(congr_arg coe $ l1_linf_nnnorm_row v).trans $ by simp [nnreal.coe_sum]

@[simp]
lemma l1_linf_nnnorm_diagonal [semi_normed_group α] [decidable_eq m] (v : m → α) :
  ∥diagonal v∥₊ = ∥v∥₊ :=
begin
  rw [l1_linf_nnnorm_def, pi.nnnorm_def],
  congr' 1 with i : 1,
  refine (finset.sum_eq_single_of_mem _ (finset.mem_univ i) $ λ j hj hij, _).trans _,
  { rw [diagonal_apply_ne' hij, nnnorm_zero] },
  { rw [diagonal_apply_eq] },
end

@[simp]
lemma l1_linf_norm_diagonal [semi_normed_group α] [decidable_eq m] (v : m → α) :
  ∥diagonal v∥ = ∥v∥ :=
congr_arg coe $ l1_linf_nnnorm_diagonal v

lemma l1_linf_nnnorm_mul_vec [semi_normed_ring α] (A : matrix l m α) (v : m → α) :
  ∥matrix.mul_vec A v∥₊ ≤ ∥A∥₊ * ∥v∥₊ :=
begin
  simp_rw [l1_linf_nnnorm_def, pi.nnnorm_def, matrix.mul_vec, matrix.dot_product],
  calc finset.univ.sup (λ b, ∥∑ i, A b i * v i∥₊)
    ≤ finset.univ.sup (λ b, ∑ i, ∥A b i∥₊ * ∥v i∥₊) :
      finset.sup_mono_fun (λ i hi, (nnnorm_sum_le _ _).trans $
        finset.sum_le_sum $ λ j hj, nnnorm_mul_le _ _)
  ... ≤ finset.univ.sup (λ i, ∑ j, ∥A i j∥₊ * finset.univ.sup (λ b, ∥v b∥₊)) :
    finset.sup_mono_fun (λ i hi,
      finset.sum_le_sum $ λ j hj,
        mul_le_mul_of_nonneg_left (finset.le_sup hj) (nnreal.coe_nonneg _))
  ... = finset.univ.sup (λ i, ∑ j, ∥A i j∥₊) * finset.univ.sup (λ b, ∥v b∥₊) :
    by simp_rw [nnreal.finset_sup_mul, finset.sum_mul],
end

lemma l1_linf_norm_mul_vec [semi_normed_ring α] (A : matrix l m α) (v : m → α) :
  ∥matrix.mul_vec A v∥ ≤ ∥A∥ * ∥v∥ :=
l1_linf_nnnorm_mul_vec _ _

lemma l1_linf_nnnorm_mul [semi_normed_ring α] (A : matrix l m α) (B : matrix m n α) :
  ∥A ⬝ B∥₊ ≤ ∥A∥₊ * ∥B∥₊ :=
begin
  simp_rw [l1_linf_nnnorm_def, matrix.mul_apply],
  calc finset.univ.sup (λ i, ∑ k, ∥∑ j, A i j * B j k∥₊)
      ≤ finset.univ.sup (λ i, ∑ k j, ∥A i j∥₊ * ∥B j k∥₊) :
    finset.sup_mono_fun $ λ i hi, finset.sum_le_sum $ λ k hk, by
        { apply (nnnorm_sum_le _ _).trans (finset.sum_le_sum (λ j hj, _)),
          exact nnnorm_mul_le _ _ }
  ... = finset.univ.sup (λ i, ∑ j, (∥A i j∥₊ * ∑ k, ∥B j k∥₊)) :
    by simp_rw [@finset.sum_comm _ m n, finset.mul_sum]
  ... ≤ finset.univ.sup (λ i, ∑ j, ∥A i j∥₊ * finset.univ.sup (λ i, ∑ j, ∥B i j∥₊)) :
    finset.sup_mono_fun $ λ i hi, finset.sum_le_sum $ λ j hj,
      mul_le_mul_of_nonneg_left (finset.le_sup hj) (zero_le _)
  ... ≤ finset.univ.sup (λ i, ∑ j, ∥A i j∥₊) * finset.univ.sup (λ i, ∑ j, ∥B i j∥₊) :
    by simp_rw [←finset.sum_mul, ←nnreal.finset_sup_mul],
end

#check m

/-- Seminormed ring instance (using sup norm of L1 norm) for matrices over a semi normed ring.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def l1_linf_semi_normed_ring [semi_normed_ring α] [decidable_eq n] :
  semi_normed_ring (matrix n n α) :=
{ norm_mul := l1_linf_nnnorm_mul,
  .. matrix.l1_linf_semi_normed_group,
  .. matrix.ring }

/-- Normed ring instance (using sup norm of L1 norm) for matrices over a normed ring.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def l1_linf_normed_ring [normed_ring α] [decidable_eq n] :
  normed_ring (matrix n n α) :=
{ ..matrix.l1_linf_semi_normed_ring }

local attribute [instance] matrix.l1_linf_semi_normed_ring matrix.l1_linf_normed_ring

/-- Normed algebra instance (using sup norm of L1 norm) for matrices over a normed algebra. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def l1_linf_normed_algebra [normed_field R] [semi_normed_ring α] [normed_algebra R α]
  [decidable_eq n] [nonempty n] :
  normed_algebra R (matrix n n α) :=
{ norm_algebra_map_eq := λ r, by
    rw [algebra_map_eq_diagonal, l1_linf_norm_diagonal, norm_algebra_map_eq (n → α) r] }

end l1_linf

end matrix
