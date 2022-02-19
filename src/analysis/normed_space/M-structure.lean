import analysis.normed_space.basic

variables {X : Type*} [normed_group X]

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 X] -- [complete_space X]

def is_projection : (X →L[𝕜] X) → Prop := λ P, P^2 = P

lemma projection_def {P: X →L[𝕜] X} (h: is_projection P) : P^2 = P := by exact h

lemma is_projection.complement {P: X →L[𝕜] X} : is_projection P → is_projection (1-P) :=
begin
  unfold is_projection,
  intro h,
  rw sq at h,
  rw [sq, mul_sub, mul_one, sub_mul, one_mul, h, sub_self, sub_zero ],
end

lemma is_projection.complement_iff {P: X →L[𝕜] X} : is_projection P ↔ is_projection (1-P) :=
⟨ is_projection.complement ,
begin
  intros h,
  rw ← sub_sub_cancel 1 P,
  apply is_projection.complement h,
end ⟩

instance : has_compl (subtype (is_projection  : (X →L[𝕜] X) → Prop)) :=
⟨λ P, ⟨1-P, P.prop.complement⟩⟩

lemma commuting_projections (P: X →L[𝕜] X) (Q: X →L[𝕜] X) (h: commute P Q): is_projection P → is_projection Q →  is_projection (P*Q)  :=
begin
  intros h₁ h₂,
  unfold is_projection,
  unfold is_projection at h₁,
  unfold is_projection at h₂,
  unfold commute at h,
  unfold semiconj_by at h,
  rw [sq, mul_assoc, ← mul_assoc Q, ←h, mul_assoc P, ← sq, h₂, ← mul_assoc, ← sq, h₁],
end

def is_Lprojection : (X →L[𝕜] X) → Prop := λ P, is_projection P ∧ ∀ (x : X), ∥x∥ = ∥P x∥ + ∥(1-P) x∥

def is_Mprojection : (X →L[𝕜] X) → Prop := λ P, is_projection P ∧ ∀ (x : X), ∥x∥ = (max ∥P x∥  ∥(1-P) x∥)

lemma is_Lprojection.Lcomplement {P: X →L[𝕜] X} : is_Lprojection P → is_Lprojection (1-P) :=
begin
  intro h,
  unfold is_Lprojection,
  rw ← is_projection.complement_iff,
  rw sub_sub_cancel,
  split,
  { exact h.left, },
  { intros,
    rw add_comm,
    apply h.right,
  }
end

lemma is_Lprojection.Lcomplement_iff (P: X →L[𝕜] X) : is_Lprojection P ↔ is_Lprojection (1-P) := ⟨
  is_Lprojection.Lcomplement,
  begin
    intros h,
    rw ← sub_sub_cancel 1 P,
    apply is_Lprojection.Lcomplement h,
  end ⟩


lemma Lproj_PQ_eq_QPQ (P Q : X →L[𝕜] X) (h₁: is_Lprojection P) (h₂: is_Lprojection Q) :
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

lemma Lproj_QP_eq_QPQ (P Q : X →L[𝕜] X) (h₁: is_Lprojection P) (h₂: is_Lprojection Q) : Q * P = Q * P * Q :=
begin
  have e1: P * (1 - Q) = P * (1 - Q) - (Q * P - Q * P * Q) :=
  calc P * (1 - Q) = (1 - Q) * P * (1 - Q) : by rw Lproj_PQ_eq_QPQ P (1 - Q) h₁ h₂.Lcomplement
  ... = 1 * (P * (1 - Q)) - Q * (P * (1 - Q)) : by {rw mul_assoc, rw sub_mul,}
  ... = P * (1 - Q) - Q * (P * (1 - Q)) : by rw one_mul
  ... = P * (1 - Q) - Q * (P - P * Q) : by rw [mul_sub, mul_one]
  ... = P * (1 - Q) - (Q * P - Q * P * Q) : by rw [mul_sub Q, mul_assoc],
  rw [eq_sub_iff_add_eq, add_right_eq_self, sub_eq_zero] at e1,
  exact e1,
end

lemma Lproj_commute (P Q: X →L[𝕜] X) (h₁: is_Lprojection P) (h₂ : is_Lprojection Q) : commute P Q :=
begin
  unfold commute,
  unfold semiconj_by,
  rw Lproj_PQ_eq_QPQ P Q h₁ h₂,
  nth_rewrite_rhs 0 Lproj_QP_eq_QPQ P Q h₁ h₂,
end

@[simp] lemma is_Lprojection.product {P Q: X →L[𝕜] X} (h₁ : is_Lprojection P) (h₂ : is_Lprojection Q) : is_Lprojection (P*Q) :=
begin
  unfold is_Lprojection,
  split,
  { apply commuting_projections P Q (Lproj_commute P Q h₁ h₂) h₁.left h₂.left, },
  { intro x,
    rw le_antisymm_iff,
    split,
    -- rw map_sub, apply norm_add_le,
    { calc ∥ x ∥ = ∥(P * Q) x + (x - (P * Q) x)∥ : by abel
      ... ≤ ∥(P * Q) x∥ + ∥ x - (P * Q) x ∥ : by apply norm_add_le
      ... = ∥(P * Q) x∥ + ∥(1 - P * Q) x∥ : rfl },
    { calc ∥x∥ = ∥Q x∥ + ∥(1-Q) x∥ : by rw h₂.right x
      ... = ∥P(Q x)∥ + ∥(1-P)(Q x)∥ + ∥(1-Q) x∥ : by rw h₁.right (Q x)
      ... = ∥P(Q x)∥ + ∥Q x - P (Q x)∥ + ∥x - Q x∥ : rfl
      ... = ∥P(Q x)∥ + (∥Q x - P (Q x)∥ + ∥x - Q x∥) : by rw add_assoc
      ... ≥ ∥P(Q x)∥ + ∥(Q x - P (Q x)) + (x - Q x)∥ : by apply (add_le_add_iff_left (∥P(Q x)∥)).mpr (norm_add_le (Q x - P (Q x)) (x - Q x))
      ... = ∥P(Q x)∥ + ∥x - P (Q x)∥ : by rw sub_add_sub_cancel'
      ... = ∥(P * Q) x∥ + ∥(1 - P * Q) x∥ : rfl }, }
end

lemma test  (a b c d: X →L[𝕜] X) : a - b*(c-d) = a - b*c + b*d :=
begin
  rw mul_sub,

end

lemma test2 (a b c d: X →L[𝕜] X) : a + (b - c) = a + b - c :=
begin
  library_search
end

lemma is_Lprojection.join {P Q: X →L[𝕜] X} (h₁ : is_Lprojection P) (h₂ : is_Lprojection Q) : is_Lprojection (P + Q - P * Q) :=
begin
  have e1:  1 - (1 - P) * (1 - Q) = P + Q - P * Q :=
  calc 1 - (1 - P) * (1 - Q) = 1 -(1 - Q - P * (1 - Q)) : by rw [sub_mul, one_mul]
  ... = Q + P * (1 - Q) : by rw [sub_sub, sub_sub_self]
  ... = P + Q - P * Q : by rw [mul_sub, mul_one, add_sub, add_comm],
  rw ← e1,
  rw ← is_Lprojection.Lcomplement_iff,
  apply is_Lprojection.product,
  apply is_Lprojection.Lcomplement h₁,
  apply is_Lprojection.Lcomplement h₂,
end

instance Lprojections_compl: has_compl(subtype (is_Lprojection  : (X →L[𝕜] X) → Prop)) :=
⟨λ P, ⟨1-P, P.prop.Lcomplement⟩⟩

instance : has_inf (subtype (is_Lprojection  : (X →L[𝕜] X) → Prop)) :=
⟨λ P Q, ⟨P * Q, P.prop.product Q.prop⟩ ⟩

instance : has_sup (subtype (is_Lprojection  : (X →L[𝕜] X) → Prop)) :=
⟨λ P Q, ⟨P + Q - P * Q, P.prop.join Q.prop⟩ ⟩
