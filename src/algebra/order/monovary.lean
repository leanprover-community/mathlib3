/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.order.mathlib
import algebra.order.monoid.min_max
import order.monotone.monovary

/-!
# Monovarying functions and algebraic operations

This file characterises the interaction of ordered algebraic structures with monovariance
of functions.

## See also

`algebra.order.rearrangement` for the n-ary rearrangement inequality
-/

variables {ι α β : Type*}

/-! ### Algebraic operations on monovarying functions -/

section ordered_comm_group
variables [ordered_comm_group α] [ordered_comm_group β] {s : set ι} {f f₁ f₂ : ι → α}
  {g g₁ g₂ : ι → β}

@[simp, to_additive] lemma monovary_on_inv_left : monovary_on f⁻¹ g s ↔ antivary_on f g s :=
by simp [monovary_on, antivary_on]

@[simp, to_additive] lemma antivary_on_inv_left : antivary_on f⁻¹ g s ↔ monovary_on f g s :=
by simp [monovary_on, antivary_on]

@[simp, to_additive] lemma monovary_on_inv_right : monovary_on f g⁻¹ s ↔ antivary_on f g s :=
by simpa [monovary_on, antivary_on] using forall₂_swap

@[simp, to_additive] lemma antivary_on_inv_right : antivary_on f g⁻¹ s ↔ monovary_on f g s :=
by simpa [monovary_on, antivary_on] using forall₂_swap

@[simp, to_additive] lemma monovary_inv_left : monovary f⁻¹ g ↔ antivary f g :=
by simp [monovary, antivary]

@[simp, to_additive] lemma antivary_inv_left : antivary f⁻¹ g ↔ monovary f g :=
by simp [monovary, antivary]

@[simp, to_additive] lemma monovary_inv_right : monovary f g⁻¹ ↔ antivary f g :=
by simpa [monovary, antivary] using forall_swap

@[simp, to_additive] lemma antivary_inv_right : antivary f g⁻¹ ↔ monovary f g :=
by simpa [monovary, antivary] using forall_swap

alias monovary_on_inv_left ↔ monovary_on.of_inv_left antivary_on.inv_left
alias antivary_on_inv_left ↔ antivary_on.of_inv_left monovary_on.inv_left
alias monovary_on_inv_right ↔ monovary_on.of_inv_right antivary_on.inv_right
alias antivary_on_inv_right ↔ antivary_on.of_inv_right monovary_on.inv_right
alias monovary_inv_left ↔ monovary.of_inv_left antivary.inv_left
alias antivary_inv_left ↔ antivary.of_inv_left monovary.inv_left
alias monovary_inv_right ↔ monovary.of_inv_right antivary.inv_right
alias antivary_inv_right ↔ antivary.of_inv_right monovary.inv_right

attribute [to_additive]
  monovary_on.of_inv_left antivary_on.inv_left
  antivary_on.of_inv_left monovary_on.inv_left
  monovary_on.of_inv_right antivary_on.inv_right
  antivary_on.of_inv_right monovary_on.inv_right
  monovary.of_inv_left antivary.inv_left
  antivary.of_inv_left monovary.inv_left
  monovary.of_inv_right antivary.inv_right
  antivary.of_inv_right monovary.inv_right

@[to_additive] lemma monovary_on.mul_left (h₁ : monovary_on f₁ g s) (h₂ : monovary_on f₂ g s) :
  monovary_on (f₁ * f₂) g s :=
λ i hi j hj hij, mul_le_mul' (h₁ hi hj hij) $ h₂ hi hj hij

@[to_additive] lemma antivary_on.mul_left (h₁ : antivary_on f₁ g s) (h₂ : antivary_on f₂ g s) :
  antivary_on (f₁ * f₂) g s :=
λ i hi j hj hij, mul_le_mul' (h₁ hi hj hij) $ h₂ hi hj hij

@[to_additive] lemma monovary_on.div_left (h₁ : monovary_on f₁ g s) (h₂ : antivary_on f₂ g s) :
  monovary_on (f₁ / f₂) g s :=
λ i hi j hj hij, div_le_div'' (h₁ hi hj hij) $ h₂ hi hj hij

@[to_additive] lemma antivary_on.div_left (h₁ : antivary_on f₁ g s) (h₂ : monovary_on f₂ g s) :
  antivary_on (f₁ / f₂) g s :=
λ i hi j hj hij, div_le_div'' (h₁ hi hj hij) $ h₂ hi hj hij

@[to_additive] lemma monovary.mul_left (h₁ : monovary f₁ g) (h₂ : monovary f₂ g) :
  monovary (f₁ * f₂) g :=
λ i j hij, mul_le_mul' (h₁ hij) $ h₂ hij

@[to_additive] lemma antivary.mul_left (h₁ : antivary f₁ g) (h₂ : antivary f₂ g) :
  antivary (f₁ * f₂) g :=
λ i j hij, mul_le_mul' (h₁ hij) $ h₂ hij

@[to_additive] lemma monovary.div_left (h₁ : monovary f₁ g) (h₂ : antivary f₂ g) :
  monovary (f₁ / f₂) g :=
λ i j hij, div_le_div'' (h₁ hij) $ h₂ hij

@[to_additive] lemma antivary.div_left (h₁ : antivary f₁ g) (h₂ : monovary f₂ g) :
  antivary (f₁ / f₂) g :=
λ i j hij, div_le_div'' (h₁ hij) $ h₂ hij

end ordered_comm_group

section linear_ordered_comm_group
variables [ordered_comm_group α] [linear_ordered_comm_group β] {s : set ι} {f f₁ f₂ : ι → α}
  {g g₁ g₂ : ι → β}

@[to_additive] lemma monovary_on.mul_right (h₁ : monovary_on f g₁ s) (h₂ : monovary_on f g₂ s) :
  monovary_on f (g₁ * g₂) s :=
λ i hi j hj hij, (lt_or_lt_of_mul_lt_mul hij).elim (h₁ hi hj) $ h₂ hi hj

@[to_additive] lemma antivary_on.mul_right (h₁ : antivary_on f g₁ s) (h₂ : antivary_on f g₂ s) :
  antivary_on f (g₁ * g₂) s :=
λ i hi j hj hij, (lt_or_lt_of_mul_lt_mul hij).elim (h₁ hi hj) $ h₂ hi hj

@[to_additive] lemma monovary_on.div_right (h₁ : monovary_on f g₁ s) (h₂ : antivary_on f g₂ s) :
  monovary_on f (g₁ / g₂) s :=
λ i hi j hj hij, (lt_or_lt_of_div_lt_div hij).elim (h₁ hi hj) $ h₂ hj hi

@[to_additive] lemma antivary_on.div_right (h₁ : antivary_on f g₁ s) (h₂ : monovary_on f g₂ s) :
  antivary_on f (g₁ / g₂) s :=
λ i hi j hj hij, (lt_or_lt_of_div_lt_div hij).elim (h₁ hi hj) $ h₂ hj hi

@[to_additive] lemma monovary.mul_right (h₁ : monovary f g₁) (h₂ : monovary f g₂) :
  monovary f (g₁ * g₂) :=
λ i j hij, (lt_or_lt_of_mul_lt_mul hij).elim (λ h, h₁ h) $ λ h, h₂ h

@[to_additive] lemma antivary.mul_right (h₁ : antivary f g₁) (h₂ : antivary f g₂) :
  antivary f (g₁ * g₂) :=
λ i j hij, (lt_or_lt_of_mul_lt_mul hij).elim (λ h, h₁ h) $ λ h, h₂ h

@[to_additive] lemma monovary.div_right (h₁ : monovary f g₁) (h₂ : antivary f g₂) :
  monovary f (g₁ / g₂) :=
λ i j hij, (lt_or_lt_of_div_lt_div hij).elim (λ h, h₁ h) $ λ h, h₂ h

@[to_additive] lemma antivary.div_right (h₁ : antivary f g₁) (h₂ : monovary f g₂) :
  antivary f (g₁ / g₂) :=
λ i j hij, (lt_or_lt_of_div_lt_div hij).elim (λ h, h₁ h) $ λ h, h₂ h

end linear_ordered_comm_group

/-! ### Rearrangement inequality characterisation -/

section linear_ordered_add_comm_group
variables [linear_ordered_ring α] [linear_ordered_add_comm_group β] [module α β]
  [ordered_smul α β] {f : ι → α} {g : ι → β} {s : set ι} {a a₁ a₂ : α} {b b₁ b₂ : β}

lemma monovary_on_iff_forall_smul_nonneg :
  monovary_on f g s ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → 0 ≤ (f j - f i) • (g j - g i) :=
begin
  simp_rw [smul_nonneg_iff_pos_imp_nonneg, sub_pos, sub_nonneg, forall_and_distrib],
  exact (and_iff_right_of_imp monovary_on.symm).symm,
end

lemma antivary_on_iff_forall_smul_nonpos :
  antivary_on f g s ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → (f j - f i) • (g j - g i) ≤ 0 :=
monovary_on_to_dual_right.symm.trans $ by rw [monovary_on_iff_forall_smul_nonneg]; refl

lemma monovary_iff_forall_smul_nonneg : monovary f g ↔ ∀ i j, 0 ≤ (f j - f i) • (g j - g i) :=
monovary_on_univ.symm.trans $ monovary_on_iff_forall_smul_nonneg.trans $
  by simp only [set.mem_univ, forall_true_left]

lemma antivary_iff_forall_smul_nonpos : antivary f g ↔ ∀ i j, (f j - f i) • (g j - g i) ≤ 0 :=
monovary_to_dual_right.symm.trans $ by rw [monovary_iff_forall_smul_nonneg]; refl

/-- Two functions monovary iff the rearrangement inequality holds. -/
lemma monovary_on_iff_smul_rearrangement :
  monovary_on f g s ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → f i • g j + f j • g i ≤ f i • g i + f j • g j :=
monovary_on_iff_forall_smul_nonneg.trans $ forall₄_congr $ λ i hi j hj,
  by simp [smul_sub, sub_smul, ←add_sub_right_comm, le_sub_iff_add_le, add_comm (f i • g i)]

/-- Two functions antivary iff the rearrangement inequality holds. -/
lemma antivary_on_iff_smul_rearrangement :
  antivary_on f g s ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → f i • g i + f j • g j ≤ f i • g j + f j • g i :=
monovary_on_to_dual_right.symm.trans $ by rw [monovary_on_iff_smul_rearrangement]; refl

/-- Two functions monovary iff the rearrangement inequality holds. -/
lemma monovary_iff_smul_rearrangement :
  monovary f g ↔ ∀ i j, f i • g j + f j • g i ≤ f i • g i + f j • g j :=
monovary_on_univ.symm.trans $ monovary_on_iff_smul_rearrangement.trans $
  by simp only [set.mem_univ, forall_true_left]

/-- Two functions antivary iff the rearrangement inequality holds. -/
lemma antivary_iff_smul_rearrangement :
  antivary f g ↔ ∀ i j, f i • g i + f j • g j ≤ f i • g j + f j • g i :=
monovary_to_dual_right.symm.trans $ by rw [monovary_iff_smul_rearrangement]; refl

alias monovary_on_iff_forall_smul_nonneg ↔ monovary_on.sub_smul_sub_nonneg _
alias antivary_on_iff_forall_smul_nonpos ↔ antivary_on.sub_smul_sub_nonpos _
alias monovary_iff_forall_smul_nonneg ↔ monovary.sub_smul_sub_nonneg _
alias antivary_iff_forall_smul_nonpos ↔ antivary.sub_smul_sub_nonpos _
alias monovary_iff_smul_rearrangement ↔ monovary.smul_add_smul_le_smul_add_smul _
alias antivary_iff_smul_rearrangement ↔ antivary.smul_add_smul_le_smul_add_smul _
alias monovary_on_iff_smul_rearrangement ↔ monovary_on.smul_add_smul_le_smul_add_smul _
alias antivary_on_iff_smul_rearrangement ↔ antivary_on.smul_add_smul_le_smul_add_smul _

end linear_ordered_add_comm_group

section linear_ordered_ring
variables [linear_ordered_ring α] {f g : ι → α} {s : set ι} {a b c d : α}

lemma monovary_on_iff_forall_mul_nonneg :
  monovary_on f g s ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → 0 ≤ (f j - f i) * (g j - g i) :=
by simp only [smul_eq_mul, monovary_on_iff_forall_smul_nonneg]

lemma antivary_on_iff_forall_mul_nonpos :
  antivary_on f g s ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → (f j - f i) * (g j - g i) ≤ 0 :=
by simp only [smul_eq_mul, antivary_on_iff_forall_smul_nonpos]

lemma monovary_iff_forall_mul_nonneg : monovary f g ↔ ∀ i j, 0 ≤ (f j - f i) * (g j - g i) :=
by simp only [smul_eq_mul, monovary_iff_forall_smul_nonneg]

lemma antivary_iff_forall_mul_nonpos : antivary f g ↔ ∀ i j, (f j - f i) * (g j - g i) ≤ 0 :=
by simp only [smul_eq_mul, antivary_iff_forall_smul_nonpos]

/-- Two functions monovary iff the rearrangement inequality holds. -/
lemma monovary_on_iff_mul_rearrangement :
  monovary_on f g s ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → f i * g j + f j * g i ≤ f i * g i + f j * g j :=
by simp only [smul_eq_mul, monovary_on_iff_smul_rearrangement]

/-- Two functions antivary iff the rearrangement inequality holds. -/
lemma antivary_on_iff_mul_rearrangement :
  antivary_on f g s ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → f i • g i + f j • g j ≤ f i • g j + f j • g i :=
by simp only [smul_eq_mul, antivary_on_iff_smul_rearrangement]

/-- Two functions monovary iff the rearrangement inequality holds. -/
lemma monovary_iff_mul_rearrangement :
  monovary f g ↔ ∀ i j, f i * g j + f j * g i ≤ f i * g i + f j * g j :=
by simp only [smul_eq_mul, monovary_iff_smul_rearrangement]

/-- Two functions antivary iff the rearrangement inequality holds. -/
lemma antivary_iff_mul_rearrangement :
  antivary f g ↔ ∀ i j, f i • g i + f j • g j ≤ f i • g j + f j • g i :=
by simp only [smul_eq_mul, antivary_iff_smul_rearrangement]

alias monovary_on_iff_forall_mul_nonneg ↔ monovary_on.sub_mul_sub_nonneg _
alias antivary_on_iff_forall_mul_nonpos ↔ antivary_on.sub_mul_sub_nonpos _
alias monovary_iff_forall_mul_nonneg ↔ monovary.sub_mul_sub_nonneg _
alias antivary_iff_forall_mul_nonpos ↔ antivary.sub_mul_sub_nonpos _
alias monovary_iff_mul_rearrangement ↔ monovary.mul_add_mul_le_mul_add_mul _
alias antivary_iff_mul_rearrangement ↔ antivary.mul_add_mul_le_mul_add_mul _
alias monovary_on_iff_mul_rearrangement ↔ monovary_on.mul_add_mul_le_mul_add_mul _
alias antivary_on_iff_mul_rearrangement ↔ antivary_on.mul_add_mul_le_mul_add_mul _

end linear_ordered_ring
