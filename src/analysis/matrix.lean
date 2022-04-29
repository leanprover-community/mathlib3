/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Eric Wieser
-/
import analysis.normed_space.basic
import analysis.normed_space.pi_Lp

/-!
# Matrices as a normed space

In this file we provide the following non-instances for norms on matrices:

* The elementwise norm:

  * `matrix.semi_normed_group`
  * `matrix.normed_group`
  * `matrix.normed_space`

* The $L^\infty$ operator norm:

  * `matrix.linfty_op_semi_normed_group`
  * `matrix.linfty_op_normed_group`
  * `matrix.linfty_op_normed_space`
  * `matrix.linfty_op_non_unital_semi_normed_ring`
  * `matrix.linfty_op_semi_normed_ring`
  * `matrix.linfty_op_non_unital_normed_ring`
  * `matrix.linfty_op_normed_ring`
  * `matrix.linfty_op_normed_algebra`

These are not declared as instances because there are several natural choices for defining the norm
of a matrix.
-/

noncomputable theory

open_locale big_operators nnreal matrix

namespace matrix

variables {R l m n α β : Type*} [fintype l] [fintype m] [fintype n]


/-! ### The elementwise supremum norm -/

section linf_linf

section semi_normed_group
variables [semi_normed_group α] [semi_normed_group β]

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

@[simp] lemma nnnorm_transpose (A : matrix m n α) : ∥Aᵀ∥₊ = ∥A∥₊ :=
by { simp_rw [pi.nnnorm_def], exact finset.sup_comm _ _ _ }
@[simp] lemma norm_transpose (A : matrix m n α) : ∥Aᵀ∥ = ∥A∥ := congr_arg coe $ nnnorm_transpose A

@[simp] lemma nnnorm_map_eq (A : matrix m n α) (f : α → β) (hf : ∀ a, ∥f a∥₊ = ∥a∥₊) :
  ∥A.map f∥₊ = ∥A∥₊ :=
by simp_rw [pi.nnnorm_def, matrix.map, hf]
@[simp] lemma norm_map_eq (A : matrix m n α) (f : α → β) (hf : ∀ a, ∥f a∥ = ∥a∥) :
  ∥A.map f∥ = ∥A∥ :=
(congr_arg (coe : ℝ≥0 → ℝ) $ nnnorm_map_eq A f $ λ a, subtype.ext $ hf a : _)

@[simp] lemma nnnorm_col (v : m → α) : ∥col v∥₊ = ∥v∥₊ := by simp [pi.nnnorm_def]
@[simp] lemma norm_col (v : m → α) : ∥col v∥ = ∥v∥ := congr_arg coe $ nnnorm_col v

@[simp] lemma nnnorm_row (v : n → α) : ∥row v∥₊ = ∥v∥₊ := by simp [pi.nnnorm_def]
@[simp] lemma norm_row (v : n → α) : ∥row v∥ = ∥v∥ := congr_arg coe $ nnnorm_row v

@[simp] lemma nnnorm_diagonal [decidable_eq n] (v : n → α) : ∥diagonal v∥₊ = ∥v∥₊ :=
begin
  simp_rw pi.nnnorm_def,
  congr' 1 with i : 1,
  refine le_antisymm (finset.sup_le $ λ j hj, _) _,
  { obtain rfl | hij := eq_or_ne i j,
    { rw diagonal_apply_eq },
    { rw [diagonal_apply_ne _ hij, nnnorm_zero],
      exact zero_le _ }, },
  { refine eq.trans_le _ (finset.le_sup (finset.mem_univ i)),
    rw diagonal_apply_eq }
end

@[simp] lemma norm_diagonal [decidable_eq n] (v : n → α) : ∥diagonal v∥ = ∥v∥ :=
congr_arg coe $ nnnorm_diagonal v

/-- Note this is safe as an instance as it carries no data. -/
instance [nonempty n] [decidable_eq n] [has_one α] [norm_one_class α] :
  norm_one_class (matrix n n α) :=
⟨(norm_diagonal _).trans $ norm_one⟩

end semi_normed_group

/-- Normed group instance (using sup norm of sup norm) for matrices over a normed group.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def normed_group [normed_group α] : normed_group (matrix m n α) :=
pi.normed_group

section normed_space
local attribute [instance] matrix.semi_normed_group

variables [normed_field R] [semi_normed_group α] [normed_space R α]

/-- Normed space instance (using sup norm of sup norm) for matrices over a normed space.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def normed_space : normed_space R (matrix m n α) :=
pi.normed_space

end normed_space

end linf_linf

/-! ### The $L_\infty$ operator norm

This section defines the matrix norm $\|A\|_\infty = \operatorname{sup}_i (\sum_j \|A_{ij}\|)$.

Note that this is equivalent to the operator norm, considering $A$ as a linear map between two
$L^\infty$ spaces.
-/
section linfty_op

/-- Seminormed group instance (using sup norm of L1 norm) for matrices over a seminormed group. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
local attribute [instance]
protected def linfty_op_semi_normed_group [semi_normed_group α] :
  semi_normed_group (matrix m n α) :=
(by apply_instance : semi_normed_group (m → pi_Lp 1 (λ j : n, α)))

/-- Normed group instance (using sup norm of L1 norm) for matrices over a normed ring.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
local attribute [instance]
protected def linfty_op_normed_group [normed_group α] :
  normed_group (matrix m n α) :=
(by apply_instance : normed_group (m → pi_Lp 1 (λ j : n, α)))

/-- Normed space instance (using sup norm of L1 norm) for matrices over a normed space.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
local attribute [instance]
protected def linfty_op_normed_space [normed_field R] [semi_normed_group α] [normed_space R α] :
  normed_space R (matrix m n α) :=
(by apply_instance : normed_space R (m → pi_Lp 1 (λ j : n, α)))

section semi_normed_group
variables [semi_normed_group α]

lemma linfty_op_norm_def (A : matrix m n α) :
  ∥A∥ = ((finset.univ : finset m).sup (λ i : m, ∑ j : n, ∥A i j∥₊) : ℝ≥0) :=
by simp_rw [pi.norm_def, pi_Lp.nnnorm_eq, div_one, nnreal.rpow_one]

lemma linfty_op_nnnorm_def (A : matrix m n α) :
  ∥A∥₊ = (finset.univ : finset m).sup (λ i : m, ∑ j : n, ∥A i j∥₊) :=
subtype.ext $ linfty_op_norm_def A

@[simp] lemma linfty_op_nnnorm_col (v : m → α) :
  ∥col v∥₊ = ∥v∥₊ :=
begin
  rw [linfty_op_nnnorm_def, pi.nnnorm_def],
  simp,
end

@[simp] lemma linfty_op_norm_col (v : m → α) :
  ∥col v∥ = ∥v∥ :=
congr_arg coe $ linfty_op_nnnorm_col v

@[simp] lemma linfty_op_nnnorm_row (v : n → α) :
  ∥row v∥₊ = ∑ i, ∥v i∥₊ :=
by simp [linfty_op_nnnorm_def]

@[simp] lemma linfty_op_norm_row (v : n → α) :
  ∥row v∥ = ∑ i, ∥v i∥ :=
(congr_arg coe $ linfty_op_nnnorm_row v).trans $ by simp [nnreal.coe_sum]

@[simp]
lemma linfty_op_nnnorm_diagonal [decidable_eq m] (v : m → α) :
  ∥diagonal v∥₊ = ∥v∥₊ :=
begin
  rw [linfty_op_nnnorm_def, pi.nnnorm_def],
  congr' 1 with i : 1,
  refine (finset.sum_eq_single_of_mem _ (finset.mem_univ i) $ λ j hj hij, _).trans _,
  { rw [diagonal_apply_ne' hij, nnnorm_zero] },
  { rw [diagonal_apply_eq] },
end

@[simp]
lemma linfty_op_norm_diagonal [decidable_eq m] (v : m → α) :
  ∥diagonal v∥ = ∥v∥ :=
congr_arg coe $ linfty_op_nnnorm_diagonal v

end semi_normed_group

section non_unital_semi_normed_ring
variables [non_unital_semi_normed_ring α]

lemma linfty_op_nnnorm_mul (A : matrix l m α) (B : matrix m n α) : ∥A ⬝ B∥₊ ≤ ∥A∥₊ * ∥B∥₊ :=
begin
  simp_rw [linfty_op_nnnorm_def, matrix.mul_apply],
  calc finset.univ.sup (λ i, ∑ k, ∥∑ j, A i j * B j k∥₊)
      ≤ finset.univ.sup (λ i, ∑ k j, ∥A i j∥₊ * ∥B j k∥₊) :
    finset.sup_mono_fun $ λ i hi, finset.sum_le_sum $ λ k hk, nnnorm_sum_le_of_le _ $ λ j hj,
      nnnorm_mul_le _ _
  ... = finset.univ.sup (λ i, ∑ j, (∥A i j∥₊ * ∑ k, ∥B j k∥₊)) :
    by simp_rw [@finset.sum_comm _ m n, finset.mul_sum]
  ... ≤ finset.univ.sup (λ i, ∑ j, ∥A i j∥₊ * finset.univ.sup (λ i, ∑ j, ∥B i j∥₊)) :
    finset.sup_mono_fun $ λ i hi, finset.sum_le_sum $ λ j hj,
      mul_le_mul_of_nonneg_left (finset.le_sup hj) (zero_le _)
  ... ≤ finset.univ.sup (λ i, ∑ j, ∥A i j∥₊) * finset.univ.sup (λ i, ∑ j, ∥B i j∥₊) :
    by simp_rw [←finset.sum_mul, ←nnreal.finset_sup_mul],
end

lemma linfty_op_norm_mul (A : matrix l m α) (B : matrix m n α) : ∥A ⬝ B∥ ≤ ∥A∥ * ∥B∥ :=
linfty_op_nnnorm_mul _ _

lemma linfty_op_nnnorm_mul_vec (A : matrix l m α) (v : m → α) : ∥A.mul_vec v∥₊ ≤ ∥A∥₊ * ∥v∥₊ :=
begin
  rw [←linfty_op_nnnorm_col (A.mul_vec v), ←linfty_op_nnnorm_col v],
  exact linfty_op_nnnorm_mul A (col v),
end

lemma linfty_op_norm_mul_vec (A : matrix l m α) (v : m → α) : ∥matrix.mul_vec A v∥ ≤ ∥A∥ * ∥v∥ :=
linfty_op_nnnorm_mul_vec _ _

end non_unital_semi_normed_ring

/-- Seminormed non-unital ring instance (using sup norm of L1 norm) for matrices over a semi normed
non-unital ring. Not declared as an instance because there are several natural choices for defining
the norm of a matrix. -/
local attribute [instance]
protected def linfty_op_non_unital_semi_normed_ring [non_unital_semi_normed_ring α] :
  non_unital_semi_normed_ring (matrix n n α) :=
{ norm_mul := linfty_op_norm_mul,
  .. matrix.linfty_op_semi_normed_group,
  .. matrix.non_unital_ring }

/-- The `L₁-L∞` norm preserves one on non-empty matrices. Note this is safe as an instance, as it
carries no data. -/
instance linfty_op_norm_one_class [semi_normed_ring α] [norm_one_class α] [decidable_eq n]
  [nonempty n] : norm_one_class (matrix n n α) :=
{ norm_one := (linfty_op_norm_diagonal _).trans norm_one }

/-- Seminormed ring instance (using sup norm of L1 norm) for matrices over a semi normed ring.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
local attribute [instance]
protected def linfty_op_semi_normed_ring [semi_normed_ring α] [decidable_eq n] :
  semi_normed_ring (matrix n n α) :=
{ .. matrix.linfty_op_non_unital_semi_normed_ring,
  .. matrix.ring }

/-- Normed non-unital ring instance (using sup norm of L1 norm) for matrices over a normed
non-unital ring. Not declared as an instance because there are several natural choices for defining
the norm of a matrix. -/
local attribute [instance]
protected def linfty_op_non_unital_normed_ring [non_unital_normed_ring α] :
  non_unital_normed_ring (matrix n n α) :=
{ ..matrix.linfty_op_non_unital_semi_normed_ring }

/-- Normed ring instance (using sup norm of L1 norm) for matrices over a normed ring.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
local attribute [instance]
protected def linfty_op_normed_ring [normed_ring α] [decidable_eq n] :
  normed_ring (matrix n n α) :=
{ ..matrix.linfty_op_semi_normed_ring }

/-- Normed algebra instance (using sup norm of L1 norm) for matrices over a normed algebra. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
local attribute [instance]
protected def linfty_op_normed_algebra [normed_field R] [semi_normed_ring α] [normed_algebra R α]
  [decidable_eq n] :
  normed_algebra R (matrix n n α) :=
{ ..matrix.linfty_op_normed_space }

end linfty_op

end matrix
