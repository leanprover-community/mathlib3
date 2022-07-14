import algebra.lie.classical
import data.real.basic
import linear_algebra.matrix.determinant

open_locale matrix

variables {l : Type*}

open lie_algebra.symplectic


section J_matrix_lemmas

namespace matrix

variables (l) [decidable_eq l] [fintype l]

lemma neg_one : (-1 : matrix l l ℝ)  = (-1 : ℝ) • 1  := by simp only [neg_smul, one_smul]

lemma neg_one_transpose : (-1 : matrix l l ℝ)ᵀ = -1 := by rw [transpose_neg, transpose_one]

lemma pm_one_unit {S : Type*} [ring S] {x : S} (h : x = 1 ∨ x = -1) : is_unit x :=
begin
  cases h,
  {simp only [h, is_unit_one],},
  { use -1,
    simp only [h, units.coe_neg_one]}
end

lemma minus_powers (n : ℕ) : (-1 : ℝ)^(n + n) = 1 :=
begin
  rw neg_one_pow_eq_one_iff_even,
  exact even_add_self n,
  norm_num,
end

@[simp] lemma J_transpose : (J l ℝ)ᵀ = - (J l ℝ) :=
begin
  unfold J,
  rw [from_blocks_transpose, ←neg_one_smul ℝ (from_blocks _ _ _ _), from_blocks_smul,
      matrix.transpose_zero, matrix.transpose_one,  neg_one_transpose],
  simp [from_blocks],
end

lemma J_squared : (J l ℝ) ⬝ (J l ℝ) = -1 :=
begin
  unfold J,
  rw from_blocks_multiply,
  simp only [matrix.zero_mul, matrix.neg_mul, zero_add, neg_zero', matrix.one_mul, add_zero],
  rw [← neg_zero, ← matrix.from_blocks_neg,← from_blocks_one],
end

lemma J_inv : (J l ℝ)⁻¹ = -(J l ℝ) :=
begin
  refine matrix.inv_eq_right_inv _,
  rw [matrix.mul_neg, J_squared],
  exact neg_neg 1,
end

lemma J_det : det (J l ℝ) = 1 ∨ det (J l ℝ) = - 1:=
begin
  have H : (det (J l ℝ)) * (det (J l ℝ)) = 1 := by {
    rw [←det_mul, J_squared, neg_one, det_smul],
    simp only [fintype.card_sum, det_one, mul_one],
    rw minus_powers,
  },
  have H2 : (det (J l ℝ))^2 = 1 := by {
    unfold pow, -- MP: What to do with these?
    unfold monoid.npow,
    unfold ring.npow,
    unfold comm_ring.npow,
    unfold npow_rec,
    rw mul_one,
    exact H,
  } ,
  rw ←sq_eq_one_iff,
  exact H2,
end

lemma J_det_unit : is_unit (det (J l ℝ)) := pm_one_unit (J_det l)

end matrix

end J_matrix_lemmas









open lie_algebra.symplectic matrix

variables (l) [decidable_eq l] [fintype l]

def symplectic_group : submonoid (matrix (l ⊕ l) (l ⊕ l)  ℝ) :=
{ carrier := { A | A ⬝ (J l ℝ) ⬝ Aᵀ = J l ℝ},
  mul_mem' :=
  begin
    intros a b ha hb,
    simp only [mul_eq_mul, set.mem_set_of_eq, transpose_mul] at *,
    rw [←matrix.mul_assoc, a.mul_assoc, a.mul_assoc, hb],
    exact ha,
  end,
  one_mem' := by simp }

variables {l}

namespace symplectic_group

lemma mem_iff {A : matrix (l ⊕ l) (l ⊕ l)  ℝ} :
  A ∈ symplectic_group l ↔ A ⬝ (J l ℝ) ⬝ Aᵀ = J l ℝ :=
by simp [symplectic_group]

instance coe_matrix : has_coe (symplectic_group l) (matrix (l ⊕ l) (l ⊕ l)  ℝ) := ⟨subtype.val⟩

instance coe_fun : has_coe_to_fun (symplectic_group l) (λ _, (l ⊕ l) → (l ⊕ l) → ℝ) :=
{ coe := λ A, A.val }









section coe_lemmas

variables (A B : symplectic_group l)

@[simp] lemma mul_val : ↑(A * B) = A ⬝ B := rfl

@[simp] lemma mul_apply : ⇑(A * B) = (A ⬝ B) := rfl

@[simp] lemma one_val : ↑(1 : symplectic_group l) = (1 : matrix (l ⊕ l) (l ⊕ l)  ℝ) := rfl

@[simp] lemma one_apply : ⇑(1 : symplectic_group l) = (1 : matrix (l ⊕ l) (l ⊕ l)  ℝ) := rfl

lemma mul_mem {A B : matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ symplectic_group l) (hB : B ∈ symplectic_group l) :
A ⬝ B ∈ symplectic_group l :=
submonoid.mul_mem _ hA hB

end coe_lemmas









section symplectic_J

variables (l)

lemma J_mem : (J l ℝ) ∈ symplectic_group l :=
begin
  rw mem_iff,
  unfold J,
  rw [from_blocks_multiply, from_blocks_transpose, from_blocks_multiply],
  simp,
end

def sym_J : symplectic_group l := ⟨J l ℝ, J_mem l⟩

variables {l}

@[simp] lemma coe_J : ↑(sym_J l) = J l ℝ := rfl

@[simp] lemma J_apply : ⇑(sym_J l) = J l ℝ := rfl

end symplectic_J








variables {A : matrix (l ⊕ l) (l ⊕ l) ℝ}

lemma symplectic_det (hA : A ∈ symplectic_group l) : is_unit $ det A :=
begin
  rw mem_iff at hA,
  apply_fun det at hA,
  simp only [det_mul, det_transpose] at hA,
  have H := J_det l,
  cases H,
  { rw [H, mul_one, ←sq, sq_eq_one_iff] at hA,
    exact pm_one_unit hA },
  { rw H at hA,
  simp only [mul_neg, mul_one, neg_mul, neg_inj] at hA,
  rw [←sq, sq_eq_one_iff] at hA,
  exact pm_one_unit hA },
end

lemma transpose_mem (hA : A ∈ symplectic_group l) : Aᵀ ∈ symplectic_group l :=
begin
  rw mem_iff at ⊢ hA,
  rw transpose_transpose,
  have huA := symplectic_det hA,
  have huAT : is_unit (Aᵀ).det :=
  begin
    rw matrix.det_transpose,
    exact huA,
  end,
  calc Aᵀ ⬝ J l ℝ ⬝ A
      = - Aᵀ ⬝ (J l ℝ)⁻¹ ⬝ A  : by {rw J_inv, simp}
  ... = - Aᵀ ⬝ (A ⬝ J l ℝ ⬝ Aᵀ)⁻¹ ⬝ A : by rw hA
  ... = - (Aᵀ ⬝ (Aᵀ⁻¹ ⬝ (J l ℝ)⁻¹)) ⬝ A⁻¹ ⬝ A : by simp only [matrix.mul_inv_rev, matrix.mul_assoc, matrix.neg_mul]
  ... = - (J l ℝ)⁻¹ : by rw [mul_nonsing_inv_cancel_left _ _ huAT, nonsing_inv_mul_cancel_right _ _ huA]
  ... = (J l ℝ) : by simp [J_inv]
end

lemma neg_mem (h : A ∈ symplectic_group l) : -A ∈ symplectic_group l :=
begin
  rw mem_iff at h ⊢,
  simp [h],
end

lemma transpose_mem_iff : Aᵀ ∈ symplectic_group l ↔ A ∈ symplectic_group l :=
⟨λ hA, by simpa using transpose_mem hA , transpose_mem⟩

lemma mem_iff' : A ∈ symplectic_group l ↔ Aᵀ ⬝ (J l ℝ) ⬝ A = J l ℝ :=
by rw [←transpose_mem_iff, mem_iff, transpose_transpose]

instance : has_inv (symplectic_group l) := {
  inv := λ A, ⟨- (J l ℝ) ⬝ Aᵀ ⬝ (J l ℝ),
    mul_mem (mul_mem (neg_mem $ J_mem l) $ transpose_mem A.2) $ J_mem _⟩,
}

@[simp] lemma coe_inv (A : symplectic_group l): (↑(A⁻¹) : matrix _ _ _) = - (J l ℝ) ⬝ Aᵀ ⬝ (J l ℝ) := rfl

@[simp] lemma inv_apply (A : symplectic_group l): ⇑(A⁻¹) = - (J l ℝ) ⬝ Aᵀ ⬝ (J l ℝ) := rfl

lemma inv_left_mul_aux {A : matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ symplectic_group l) :
  -(J l ℝ ⬝ Aᵀ ⬝ J l ℝ ⬝ A) = 1 :=
calc -(J l ℝ ⬝ Aᵀ ⬝ J l ℝ ⬝ A)
    = - J l ℝ ⬝ (Aᵀ ⬝ J l ℝ ⬝ A) : by simp only [matrix.mul_assoc, matrix.neg_mul]
... = - J l ℝ ⬝ J l ℝ : by {rw mem_iff' at hA, rw hA}
... = (-1 : ℝ) • (J l ℝ ⬝ J l ℝ) : by simp only [matrix.neg_mul, neg_smul, one_smul]
... = (-1 : ℝ) • -1 : by rw J_squared
... = 1 : by simp only [neg_smul_neg, one_smul]

instance : group (symplectic_group l) := {
  mul_left_inv :=
  begin
    intro A,
    apply subtype.ext,
    simp only [mul_val, inv_apply, matrix.neg_mul, one_val],
    exact inv_left_mul_aux A.2,
  end,
  .. symplectic_group.has_inv,
  .. submonoid.to_monoid _
}

end symplectic_group
