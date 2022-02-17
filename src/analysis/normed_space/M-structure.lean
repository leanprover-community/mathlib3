import analysis.normed_space.basic

variables {X : Type*} [normed_group X]

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 X] -- [complete_space X]

def is_projection : (X →L[𝕜] X) → Prop := λ P, P^2 = P

lemma projection_def {P: X →L[𝕜] X} (h: is_projection P) : P^2 = P := by exact h

lemma projection_complement (P: X →L[𝕜] X) : is_projection P ↔ is_projection (1-P) :=
begin
  split,
  { unfold is_projection,
    intro h,
    rw sq at h,
    rw [sq, mul_sub, mul_one, sub_mul, one_mul, h, sub_self, sub_zero ], },
  { unfold is_projection,
    intro h,
    rw [sq, mul_sub, mul_one, sub_mul, one_mul, sub_eq_self, sub_eq_zero] at h,
    rw [sq, ← h], }
end

def is_Lprojection : (X →L[𝕜] X) → Prop := λ P, is_projection P ∧ ∀ (x : X), ∥x∥ = ∥P x∥ + ∥(1-P) x∥

def is_Mprojection : (X →L[𝕜] X) → Prop := λ P, is_projection P ∧ ∀ (x : X), ∥x∥ = (max ∥P x∥  ∥(1-P) x∥)

lemma Lcomplement (P: X →L[𝕜] X) : is_Lprojection P ↔ is_Lprojection (1-P) :=
begin
  split,
  {
    intro h,
    unfold is_Lprojection,
    rw ← projection_complement,
    rw sub_sub_cancel,
    split,
    { exact h.left, },
    { intros,
      rw add_comm,
      apply h.right,
    }
  },
  { intro h,
    unfold is_Lprojection,
    rw projection_complement,
    split,
    { exact h.left, },
    { intros,
      rw add_comm,
      nth_rewrite_rhs 1 ← sub_sub_cancel 1 P,
      apply h.right,
    }
   }
end

lemma Lproj_PQ_eq_QPQ (P: X →L[𝕜] X) (Q: X →L[𝕜] X) (h₁: is_Lprojection P) (h₂: is_Lprojection Q) :
  P * Q = Q * P * Q :=
begin
  ext,
  rw ← norm_sub_eq_zero_iff,
  have e1 : ∥Q x∥ ≥ ∥Q x∥ + 2 • ∥ (P * Q) x - (Q * P * Q) x∥ :=
  calc ∥Q x∥ = ∥P (Q x)∥ + ∥(1 - P) (Q x)∥ : by rw h₁.right
  ... = ∥Q (P (Q x))∥ + ∥(1-Q) (P (Q x))∥ + ∥(1 - P) (Q x)∥ : by rw h₂.right
  ... = ∥Q (P (Q x))∥ + ∥(1-Q) (P (Q x))∥ + (∥Q ((1 - P) (Q x))∥ + ∥(1-Q) ((1 - P) (Q x))∥) : by rw h₂.right ((1 - P) (Q x))
  ... = ∥Q (P (Q x))∥ + ∥(1-Q) (P (Q x))∥ + (∥Q (Q x - P (Q x))∥ + ∥(1-Q) ((1 - P) (Q x))∥) : rfl
  ... = ∥Q (P (Q x))∥ + ∥(1-Q) (P (Q x))∥ + (∥Q (Q x) - Q (P (Q x))∥ + ∥(1-Q) ((1 - P) (Q x))∥) : by rw map_sub
  ... = ∥Q (P (Q x))∥ + ∥(1-Q) (P (Q x))∥ + (∥(Q * Q) x - Q (P (Q x))∥ + ∥(1-Q) ((1 - P) (Q x))∥) : rfl
  ... = ∥Q (P (Q x))∥ + ∥(1-Q) (P (Q x))∥ + (∥Q x - Q (P (Q x))∥ + ∥(1-Q) ((1 - P) (Q x))∥) : by rw [← sq, projection_def h₂.left]
  ... = ∥Q (P (Q x))∥ + ∥(1-Q) (P (Q x))∥ + (∥Q x - Q (P (Q x))∥ + ∥(1-Q) (Q x - P (Q x))∥) : rfl
  ... = ∥Q (P (Q x))∥ + ∥(1-Q) (P (Q x))∥ + (∥Q x - Q (P (Q x))∥ + ∥(1-Q) (Q x) - (1-Q) (P (Q x))∥) : by rw map_sub
  ... = ∥Q (P (Q x))∥ + ∥(1-Q) (P (Q x))∥ + (∥Q x - Q (P (Q x))∥ + ∥((1-Q) * Q) x - (1-Q) (P (Q x))∥) : rfl
  ... = ∥Q (P (Q x))∥ + ∥(1-Q) (P (Q x))∥ + (∥Q x - Q (P (Q x))∥ + ∥0 - (1-Q) (P (Q x))∥) : by {rw [sub_mul, ← sq, projection_def h₂.left, one_mul, sub_self ], exact rfl }
  ... = ∥Q (P (Q x))∥ + ∥(1-Q) (P (Q x))∥ + (∥Q x - Q (P (Q x))∥ + ∥(1-Q) (P (Q x))∥) : by rw [zero_sub, norm_neg]
  ... = ∥Q (P (Q x))∥ + ∥Q x - Q (P (Q x))∥ + 2•∥(1-Q) (P (Q x))∥  : by abel
  ... ≥ ∥Q x∥ + 2 • ∥ (P * Q) x - (Q * P * Q) x∥ : by exact add_le_add_right (norm_le_insert' (Q x) (Q (P (Q x)))) (2•∥(1-Q) (P (Q x))∥),
  rw ge at e1,
  nth_rewrite_rhs 0 ← add_zero (∥Q x∥) at e1,
  rw [add_le_add_iff_left, two_smul,  ← two_mul]  at e1,
  rw le_antisymm_iff,
  split,
  { rw ← mul_zero (2:ℝ) at e1,
    rw mul_le_mul_left at e1, exact e1, norm_num, },
  { apply norm_nonneg, }
end

lemma Lproj_QP_eq_QPQ (P: X →L[𝕜] X) (Q: X →L[𝕜] X) (h₁: is_Lprojection P) (h₂: is_Lprojection Q) : Q * P = Q * P * Q :=
begin
  have e1: P * (1 - Q) = P * (1 - Q) - (Q * P - Q * P * Q) :=
  calc P * (1 - Q) = (1 - Q) * P * (1 - Q) : by rw Lproj_PQ_eq_QPQ P (1 - Q) h₁ ((Lcomplement Q).mp h₂)
  ... = 1 * (P * (1 - Q)) - Q * (P * (1 - Q)) : by {rw mul_assoc, rw sub_mul,}
  ... = P * (1 - Q) - Q * (P * (1 - Q)) : by rw one_mul
  ... = P * (1 - Q) - Q * (P - P * Q) : by rw [mul_sub, mul_one]
  ... = P * (1 - Q) - (Q * P - Q * P * Q) : by rw [mul_sub Q, mul_assoc],
  rw [eq_sub_iff_add_eq, add_right_eq_self, sub_eq_zero] at e1,
  exact e1,
end

lemma Lproj_commute (P: X →L[𝕜] X) (Q: X →L[𝕜] X) [h₁: is_Lprojection P] [h₂ : is_Lprojection Q] : commute P Q :=
begin
  unfold commute,
  unfold semiconj_by,
  rw Lproj_PQ_eq_QPQ P Q h₁ h₂,
  nth_rewrite_rhs 0 Lproj_QP_eq_QPQ P Q h₁ h₂,
end
