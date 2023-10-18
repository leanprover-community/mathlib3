/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Eric Wieser
-/
import analysis.normed_space.basic
import analysis.normed_space.pi_Lp
import analysis.inner_product_space.pi_L2

/-!
# Matrices as a normed space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we provide the following non-instances for norms on matrices:

* The elementwise norm:

  * `matrix.seminormed_add_comm_group`
  * `matrix.normed_add_comm_group`
  * `matrix.normed_space`

* The Frobenius norm:

  * `matrix.frobenius_seminormed_add_comm_group`
  * `matrix.frobenius_normed_add_comm_group`
  * `matrix.frobenius_normed_space`
  * `matrix.frobenius_normed_ring`
  * `matrix.frobenius_normed_algebra`

* The $L^\infty$ operator norm:

  * `matrix.linfty_op_seminormed_add_comm_group`
  * `matrix.linfty_op_normed_add_comm_group`
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

section seminormed_add_comm_group
variables [seminormed_add_comm_group α] [seminormed_add_comm_group β]

/-- Seminormed group instance (using sup norm of sup norm) for matrices over a seminormed group. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def seminormed_add_comm_group : seminormed_add_comm_group (matrix m n α) :=
pi.seminormed_add_comm_group

local attribute [instance] matrix.seminormed_add_comm_group

lemma norm_le_iff {r : ℝ} (hr : 0 ≤ r) {A : matrix m n α} :
  ‖A‖ ≤ r ↔ ∀ i j, ‖A i j‖ ≤ r :=
by simp [pi_norm_le_iff_of_nonneg hr]

lemma nnnorm_le_iff {r : ℝ≥0} {A : matrix m n α} :
  ‖A‖₊ ≤ r ↔ ∀ i j, ‖A i j‖₊ ≤ r :=
by simp [pi_nnnorm_le_iff]

lemma norm_lt_iff {r : ℝ} (hr : 0 < r) {A : matrix m n α} :
  ‖A‖ < r ↔ ∀ i j, ‖A i j‖ < r :=
by simp [pi_norm_lt_iff hr]

lemma nnnorm_lt_iff {r : ℝ≥0} (hr : 0 < r) {A : matrix m n α} :
  ‖A‖₊ < r ↔ ∀ i j, ‖A i j‖₊ < r :=
by simp [pi_nnnorm_lt_iff hr]

lemma norm_entry_le_entrywise_sup_norm (A : matrix m n α) {i : m} {j : n} :
  ‖A i j‖ ≤ ‖A‖ :=
(norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)

lemma nnnorm_entry_le_entrywise_sup_nnnorm (A : matrix m n α) {i : m} {j : n} :
  ‖A i j‖₊ ≤ ‖A‖₊ :=
(nnnorm_le_pi_nnnorm (A i) j).trans (nnnorm_le_pi_nnnorm A i)

@[simp] lemma nnnorm_map_eq (A : matrix m n α) (f : α → β) (hf : ∀ a, ‖f a‖₊ = ‖a‖₊) :
  ‖A.map f‖₊ = ‖A‖₊ :=
by simp_rw [pi.nnnorm_def, matrix.map_apply, hf]
@[simp] lemma norm_map_eq (A : matrix m n α) (f : α → β) (hf : ∀ a, ‖f a‖ = ‖a‖) :
  ‖A.map f‖ = ‖A‖ :=
(congr_arg (coe : ℝ≥0 → ℝ) $ nnnorm_map_eq A f $ λ a, subtype.ext $ hf a : _)

@[simp] lemma nnnorm_transpose (A : matrix m n α) : ‖Aᵀ‖₊ = ‖A‖₊ :=
by { simp_rw [pi.nnnorm_def], exact finset.sup_comm _ _ _ }
@[simp] lemma norm_transpose (A : matrix m n α) : ‖Aᵀ‖ = ‖A‖ := congr_arg coe $ nnnorm_transpose A

@[simp] lemma nnnorm_conj_transpose [star_add_monoid α] [normed_star_group α] (A : matrix m n α) :
  ‖Aᴴ‖₊ = ‖A‖₊ :=
(nnnorm_map_eq _ _ nnnorm_star).trans A.nnnorm_transpose
@[simp] lemma norm_conj_transpose [star_add_monoid α] [normed_star_group α] (A : matrix m n α) :
  ‖Aᴴ‖ = ‖A‖ :=
congr_arg coe $ nnnorm_conj_transpose A

instance [star_add_monoid α] [normed_star_group α] : normed_star_group (matrix m m α) :=
⟨norm_conj_transpose⟩

@[simp] lemma nnnorm_col (v : m → α) : ‖col v‖₊ = ‖v‖₊ := by simp [pi.nnnorm_def]
@[simp] lemma norm_col (v : m → α) : ‖col v‖ = ‖v‖ := congr_arg coe $ nnnorm_col v

@[simp] lemma nnnorm_row (v : n → α) : ‖row v‖₊ = ‖v‖₊ := by simp [pi.nnnorm_def]
@[simp] lemma norm_row (v : n → α) : ‖row v‖ = ‖v‖ := congr_arg coe $ nnnorm_row v

@[simp] lemma nnnorm_diagonal [decidable_eq n] (v : n → α) : ‖diagonal v‖₊ = ‖v‖₊ :=
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

@[simp] lemma norm_diagonal [decidable_eq n] (v : n → α) : ‖diagonal v‖ = ‖v‖ :=
congr_arg coe $ nnnorm_diagonal v

/-- Note this is safe as an instance as it carries no data. -/
@[nolint fails_quickly]
instance [nonempty n] [decidable_eq n] [has_one α] [norm_one_class α] :
  norm_one_class (matrix n n α) :=
⟨(norm_diagonal _).trans $ norm_one⟩

end seminormed_add_comm_group

/-- Normed group instance (using sup norm of sup norm) for matrices over a normed group.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def normed_add_comm_group [normed_add_comm_group α] :
  normed_add_comm_group (matrix m n α) :=
pi.normed_add_comm_group

section normed_space
local attribute [instance] matrix.seminormed_add_comm_group

variables [normed_field R] [seminormed_add_comm_group α] [normed_space R α]

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
protected def linfty_op_seminormed_add_comm_group [seminormed_add_comm_group α] :
  seminormed_add_comm_group (matrix m n α) :=
(by apply_instance : seminormed_add_comm_group (m → pi_Lp 1 (λ j : n, α)))

/-- Normed group instance (using sup norm of L1 norm) for matrices over a normed ring.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
local attribute [instance]
protected def linfty_op_normed_add_comm_group [normed_add_comm_group α] :
  normed_add_comm_group (matrix m n α) :=
(by apply_instance : normed_add_comm_group (m → pi_Lp 1 (λ j : n, α)))

/-- Normed space instance (using sup norm of L1 norm) for matrices over a normed space.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
local attribute [instance]
protected def linfty_op_normed_space [normed_field R] [seminormed_add_comm_group α]
  [normed_space R α] :
  normed_space R (matrix m n α) :=
(by apply_instance : normed_space R (m → pi_Lp 1 (λ j : n, α)))

section seminormed_add_comm_group
variables [seminormed_add_comm_group α]

lemma linfty_op_norm_def (A : matrix m n α) :
  ‖A‖ = ((finset.univ : finset m).sup (λ i : m, ∑ j : n, ‖A i j‖₊) : ℝ≥0) :=
by simp [pi.norm_def, pi_Lp.nnnorm_eq_sum ennreal.one_ne_top]

lemma linfty_op_nnnorm_def (A : matrix m n α) :
  ‖A‖₊ = (finset.univ : finset m).sup (λ i : m, ∑ j : n, ‖A i j‖₊) :=
subtype.ext $ linfty_op_norm_def A

@[simp] lemma linfty_op_nnnorm_col (v : m → α) :
  ‖col v‖₊ = ‖v‖₊ :=
begin
  rw [linfty_op_nnnorm_def, pi.nnnorm_def],
  simp,
end

@[simp] lemma linfty_op_norm_col (v : m → α) :
  ‖col v‖ = ‖v‖ :=
congr_arg coe $ linfty_op_nnnorm_col v

@[simp] lemma linfty_op_nnnorm_row (v : n → α) :
  ‖row v‖₊ = ∑ i, ‖v i‖₊ :=
by simp [linfty_op_nnnorm_def]

@[simp] lemma linfty_op_norm_row (v : n → α) :
  ‖row v‖ = ∑ i, ‖v i‖ :=
(congr_arg coe $ linfty_op_nnnorm_row v).trans $ by simp [nnreal.coe_sum]

@[simp]
lemma linfty_op_nnnorm_diagonal [decidable_eq m] (v : m → α) :
  ‖diagonal v‖₊ = ‖v‖₊ :=
begin
  rw [linfty_op_nnnorm_def, pi.nnnorm_def],
  congr' 1 with i : 1,
  refine (finset.sum_eq_single_of_mem _ (finset.mem_univ i) $ λ j hj hij, _).trans _,
  { rw [diagonal_apply_ne' _ hij, nnnorm_zero] },
  { rw [diagonal_apply_eq] },
end

@[simp]
lemma linfty_op_norm_diagonal [decidable_eq m] (v : m → α) :
  ‖diagonal v‖ = ‖v‖ :=
congr_arg coe $ linfty_op_nnnorm_diagonal v

end seminormed_add_comm_group

section non_unital_semi_normed_ring
variables [non_unital_semi_normed_ring α]

lemma linfty_op_nnnorm_mul (A : matrix l m α) (B : matrix m n α) : ‖A ⬝ B‖₊ ≤ ‖A‖₊ * ‖B‖₊ :=
begin
  simp_rw [linfty_op_nnnorm_def, matrix.mul_apply],
  calc finset.univ.sup (λ i, ∑ k, ‖∑ j, A i j * B j k‖₊)
      ≤ finset.univ.sup (λ i, ∑ k j, ‖A i j‖₊ * ‖B j k‖₊) :
    finset.sup_mono_fun $ λ i hi, finset.sum_le_sum $ λ k hk, nnnorm_sum_le_of_le _ $ λ j hj,
      nnnorm_mul_le _ _
  ... = finset.univ.sup (λ i, ∑ j, (‖A i j‖₊ * ∑ k, ‖B j k‖₊)) :
    by simp_rw [@finset.sum_comm _ m n, finset.mul_sum]
  ... ≤ finset.univ.sup (λ i, ∑ j, ‖A i j‖₊ * finset.univ.sup (λ i, ∑ j, ‖B i j‖₊)) :
    finset.sup_mono_fun $ λ i hi, finset.sum_le_sum $ λ j hj,
      mul_le_mul_of_nonneg_left (finset.le_sup hj) (zero_le _)
  ... ≤ finset.univ.sup (λ i, ∑ j, ‖A i j‖₊) * finset.univ.sup (λ i, ∑ j, ‖B i j‖₊) :
    by simp_rw [←finset.sum_mul, ←nnreal.finset_sup_mul],
end

lemma linfty_op_norm_mul (A : matrix l m α) (B : matrix m n α) : ‖A ⬝ B‖ ≤ ‖A‖ * ‖B‖ :=
linfty_op_nnnorm_mul _ _

lemma linfty_op_nnnorm_mul_vec (A : matrix l m α) (v : m → α) : ‖A.mul_vec v‖₊ ≤ ‖A‖₊ * ‖v‖₊ :=
begin
  rw [←linfty_op_nnnorm_col (A.mul_vec v), ←linfty_op_nnnorm_col v],
  exact linfty_op_nnnorm_mul A (col v),
end

lemma linfty_op_norm_mul_vec (A : matrix l m α) (v : m → α) : ‖matrix.mul_vec A v‖ ≤ ‖A‖ * ‖v‖ :=
linfty_op_nnnorm_mul_vec _ _

end non_unital_semi_normed_ring

/-- Seminormed non-unital ring instance (using sup norm of L1 norm) for matrices over a semi normed
non-unital ring. Not declared as an instance because there are several natural choices for defining
the norm of a matrix. -/
local attribute [instance]
protected def linfty_op_non_unital_semi_normed_ring [non_unital_semi_normed_ring α] :
  non_unital_semi_normed_ring (matrix n n α) :=
{ norm_mul := linfty_op_norm_mul,
  .. matrix.linfty_op_seminormed_add_comm_group,
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

/-! ### The Frobenius norm

This is defined as $\|A\| = \sqrt{\sum_{i,j} \|A_{ij}\|^2}$.
When the matrix is over the real or complex numbers, this norm is submultiplicative.
-/

section frobenius

open_locale matrix big_operators

/-- Seminormed group instance (using frobenius norm) for matrices over a seminormed group. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
local attribute [instance]
def frobenius_seminormed_add_comm_group [seminormed_add_comm_group α] :
  seminormed_add_comm_group (matrix m n α) :=
(by apply_instance : seminormed_add_comm_group (pi_Lp 2 (λ i : m, pi_Lp 2 (λ j : n, α))))

/-- Normed group instance (using frobenius norm) for matrices over a normed group.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
local attribute [instance]
def frobenius_normed_add_comm_group [normed_add_comm_group α] :
  normed_add_comm_group (matrix m n α) :=
(by apply_instance : normed_add_comm_group (pi_Lp 2 (λ i : m, pi_Lp 2 (λ j : n, α))))

/-- Normed space instance (using frobenius norm) for matrices over a normed space.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
local attribute [instance]
def frobenius_normed_space [normed_field R] [seminormed_add_comm_group α] [normed_space R α] :
  normed_space R (matrix m n α) :=
(by apply_instance : normed_space R (pi_Lp 2 (λ i : m, pi_Lp 2 (λ j : n, α))))

section seminormed_add_comm_group
variables [seminormed_add_comm_group α] [seminormed_add_comm_group β]

lemma frobenius_nnnorm_def (A : matrix m n α) :
  ‖A‖₊ = (∑ i j, ‖A i j‖₊ ^ (2 : ℝ)) ^ (1/2 : ℝ) :=
by simp_rw [pi_Lp.nnnorm_eq_of_L2, nnreal.sq_sqrt, nnreal.sqrt_eq_rpow, nnreal.rpow_two]

lemma frobenius_norm_def (A : matrix m n α) :
  ‖A‖ = (∑ i j, ‖A i j‖ ^ (2 : ℝ)) ^ (1/2 : ℝ) :=
(congr_arg coe (frobenius_nnnorm_def A)).trans $ by simp [nnreal.coe_sum]

@[simp] lemma frobenius_nnnorm_map_eq (A : matrix m n α) (f : α → β) (hf : ∀ a, ‖f a‖₊ = ‖a‖₊) :
  ‖A.map f‖₊ = ‖A‖₊ :=
by simp_rw [frobenius_nnnorm_def, matrix.map_apply, hf]
@[simp] lemma frobenius_norm_map_eq (A : matrix m n α) (f : α → β) (hf : ∀ a, ‖f a‖ = ‖a‖) :
  ‖A.map f‖ = ‖A‖ :=
(congr_arg (coe : ℝ≥0 → ℝ) $ frobenius_nnnorm_map_eq A f $ λ a, subtype.ext $ hf a : _)

@[simp] lemma frobenius_nnnorm_transpose (A : matrix m n α) : ‖Aᵀ‖₊ = ‖A‖₊ :=
by { rw [frobenius_nnnorm_def, frobenius_nnnorm_def, finset.sum_comm], refl }
@[simp] lemma frobenius_norm_transpose (A : matrix m n α) : ‖Aᵀ‖ = ‖A‖ :=
congr_arg coe $ frobenius_nnnorm_transpose A

@[simp] lemma frobenius_nnnorm_conj_transpose [star_add_monoid α] [normed_star_group α]
  (A : matrix m n α) : ‖Aᴴ‖₊ = ‖A‖₊ :=
(frobenius_nnnorm_map_eq _ _ nnnorm_star).trans A.frobenius_nnnorm_transpose
@[simp] lemma frobenius_norm_conj_transpose [star_add_monoid α] [normed_star_group α]
  (A : matrix m n α) : ‖Aᴴ‖ = ‖A‖ :=
congr_arg coe $ frobenius_nnnorm_conj_transpose A

instance frobenius_normed_star_group [star_add_monoid α] [normed_star_group α] :
  normed_star_group (matrix m m α) :=
⟨frobenius_norm_conj_transpose⟩

@[simp] lemma frobenius_norm_row (v : m → α) : ‖row v‖ = ‖(pi_Lp.equiv 2 _).symm v‖ :=
begin
  rw [frobenius_norm_def, fintype.sum_unique, pi_Lp.norm_eq_of_L2, real.sqrt_eq_rpow],
  simp only [row_apply, real.rpow_two, pi_Lp.equiv_symm_apply],
end
@[simp] lemma frobenius_nnnorm_row (v : m → α) : ‖row v‖₊ = ‖(pi_Lp.equiv 2 _).symm v‖₊ :=
subtype.ext $ frobenius_norm_row v

@[simp] lemma frobenius_norm_col (v : n → α) : ‖col v‖ = ‖(pi_Lp.equiv 2 _).symm v‖ :=
begin
  simp_rw [frobenius_norm_def, fintype.sum_unique, pi_Lp.norm_eq_of_L2, real.sqrt_eq_rpow],
  simp only [col_apply, real.rpow_two, pi_Lp.equiv_symm_apply]
end
@[simp] lemma frobenius_nnnorm_col (v : n → α) : ‖col v‖₊ = ‖(pi_Lp.equiv 2 _).symm v‖₊ :=
subtype.ext $ frobenius_norm_col v

@[simp] lemma frobenius_nnnorm_diagonal [decidable_eq n] (v : n → α) :
  ‖diagonal v‖₊ = ‖(pi_Lp.equiv 2 _).symm v‖₊ :=
begin
  simp_rw [frobenius_nnnorm_def, ←finset.sum_product', finset.univ_product_univ,
    pi_Lp.nnnorm_eq_of_L2],
  let s := (finset.univ : finset n).map ⟨λ i : n, (i, i), λ i j h, congr_arg prod.fst h⟩,
  rw ←finset.sum_subset (finset.subset_univ s) (λ i hi his, _),
  { rw [finset.sum_map, nnreal.sqrt_eq_rpow],
    dsimp,
    simp_rw [diagonal_apply_eq, nnreal.rpow_two] },
  { suffices : i.1 ≠ i.2,
    { rw [diagonal_apply_ne _ this, nnnorm_zero, nnreal.zero_rpow two_ne_zero], },
    intro h,
    exact finset.mem_map.not.mp his ⟨i.1, finset.mem_univ _, prod.ext rfl h⟩ }
end
@[simp] lemma frobenius_norm_diagonal [decidable_eq n] (v : n → α) :
  ‖diagonal v‖ = ‖(pi_Lp.equiv 2 _).symm v‖ :=
(congr_arg coe $ frobenius_nnnorm_diagonal v : _).trans rfl

end seminormed_add_comm_group

lemma frobenius_nnnorm_one [decidable_eq n] [seminormed_add_comm_group α] [has_one α] :
  ‖(1 : matrix n n α)‖₊ = nnreal.sqrt (fintype.card n) * ‖(1 : α)‖₊:=
begin
  refine (frobenius_nnnorm_diagonal _).trans _,
  simp_rw [pi_Lp.nnnorm_equiv_symm_const ennreal.two_ne_top, nnreal.sqrt_eq_rpow],
  simp only [ennreal.to_real_div, ennreal.one_to_real, ennreal.to_real_bit0],
end

section is_R_or_C
variables [is_R_or_C α]

lemma frobenius_nnnorm_mul (A : matrix l m α) (B : matrix m n α) : ‖A ⬝ B‖₊ ≤ ‖A‖₊ * ‖B‖₊ :=
begin
  simp_rw [frobenius_nnnorm_def, matrix.mul_apply],
  rw [←nnreal.mul_rpow, @finset.sum_comm _ n m, finset.sum_mul_sum, finset.sum_product],
  refine nnreal.rpow_le_rpow _ one_half_pos.le,
  refine finset.sum_le_sum (λ i hi, finset.sum_le_sum $ λ j hj, _),
  rw [← nnreal.rpow_le_rpow_iff one_half_pos, ← nnreal.rpow_mul,
    mul_div_cancel' (1 : ℝ) two_ne_zero, nnreal.rpow_one, nnreal.mul_rpow],
  dsimp only,
  have := @nnnorm_inner_le_nnnorm α _ _ _ _
    ((pi_Lp.equiv 2 (λ i, α)).symm (λ j, star (A i j)))
    ((pi_Lp.equiv 2 (λ i, α)).symm (λ k, B k j)),
  simpa only [pi_Lp.equiv_symm_apply, pi_Lp.inner_apply,
      is_R_or_C.inner_apply, star_ring_end_apply, pi.nnnorm_def, pi_Lp.nnnorm_eq_of_L2,
      star_star, nnnorm_star, nnreal.sqrt_eq_rpow, nnreal.rpow_two] using this,
end

lemma frobenius_norm_mul (A : matrix l m α) (B : matrix m n α) : ‖A ⬝ B‖ ≤ ‖A‖ * ‖B‖ :=
frobenius_nnnorm_mul A B

/-- Normed ring instance (using frobenius norm) for matrices over `ℝ` or `ℂ`.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
local attribute [instance]
def frobenius_normed_ring [decidable_eq m] : normed_ring (matrix m m α) :=
{ norm := has_norm.norm,
  norm_mul := frobenius_norm_mul,
  ..matrix.frobenius_seminormed_add_comm_group }

/-- Normed algebra instance (using frobenius norm) for matrices over `ℝ` or `ℂ`.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
local attribute [instance]
def frobenius_normed_algebra [decidable_eq m] [normed_field R] [normed_algebra R α] :
  normed_algebra R (matrix m m α) :=
{ ..matrix.frobenius_normed_space }

end is_R_or_C

end frobenius

end matrix
