/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import analysis.normed_space.basic

/-!
# M-structure

A continuous projection P on a normed space X is said to be an L-projection if, for all `x` in `X`,
$$
∥x∥ = ∥P x∥ + ∥(1-P) x∥.
$$
The range of an L-projection is said to be an L-summand of X.

A continuous projection P on a normed space X is said to be an M-projection if, for all `x` in `X`,
$$
∥x∥ = max(∥P x∥,∥(1-P) x∥).
$$
The range of an M-projection is said to be an M-summand of X.

The L-projections and M-projections form Boolean algebras. When X is a Banach space, the Boolean
algebra of L-projections is complete.

Let `X` be a normed space with dual `X^*`. A closed subspace `M` of `X` is said to be an M-ideal if
the topological annihilator `M^∘` is an L-summand of `X^*`.

M-ideal, M-summands and L-summands were introduced by Alfsen and Effros in [alfseneffros1972] to
study the structure of general Banach spaces. When `A` is a JB*-triple, the M-ideals of `A` are
exactly the norm-closed ideals of `A`. When `A` is a JBW*-triple with predual `X`, the M-summands of
`A` are exactly the weak*-closed ideals, and their pre-duals can be identified with the L-summands
of `X`. In the special case when `A` is a C*-algebra, the M-ideals are exactly the norm-closed
two-sided ideals of `A`, when `A` is also a W*-algebra the M-summands are exactly the weak*-closed
two-sided ideals of `A`.

## Implementation notes

The approach to showing that the L-projections form a Boolean algebra is inspired by
`measure_theory.measurable_space`.

## References

* [Behrends, M-structure and the Banach-Stone Theorem][behrends1979]
* [Harmand, Werner, Werner, M-ideals in Banach spaces and Banach algebras][harmandwernerwerner1993]

## Tags

M-summand, M-projection, L-summand, L-projection, M-ideal, M-structure

-/

variables {M : Type*} [monoid M]

/--
A continuous linear map `P` on a normed space `X` is said to be a projection if it is idempotent.
-/
def is_projection (x : M) : Prop := x^2 = x

lemma projection_def {P : M} (h : is_projection P) : P^2 = P := by exact h

namespace is_projection

lemma mul_of_commute {P Q : M} (h : commute P Q) (h₁ : is_projection P) (h₂ : is_projection Q) :
  is_projection (P*Q)  :=
begin
  unfold is_projection,
  unfold is_projection at h₁,
  unfold is_projection at h₂,
  unfold commute at h,
  unfold semiconj_by at h,
  rw [sq, mul_assoc, ← mul_assoc Q, ←h, mul_assoc P, ← sq, h₂, ← mul_assoc, ← sq, h₁],
end

variables {R : Type*} [ring R]

lemma complement {P: R} (h: is_projection P) : is_projection (1-P) :=
begin
  unfold is_projection,
  unfold is_projection at h,
  rw sq at h,
  rw [sq, mul_sub_left_distrib, mul_one, sub_mul, one_mul, h, sub_self, sub_zero],
end


lemma complement_iff {P: R} : is_projection P ↔ is_projection (1-P) :=
⟨ is_projection.complement ,
begin
  intros h,
  rw ← sub_sub_cancel 1 P,
  apply is_projection.complement h,
end ⟩

instance : has_compl (subtype (is_projection  : R → Prop)) :=
⟨λ P, ⟨1-P, P.prop.complement⟩⟩

end is_projection

variables {X : Type*} [normed_group X]

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 X]

/--
A projection on a normed space `X` is said to be an L-projection if, for all `x` in `X`,
$$
∥x∥ = ∥P x∥ + ∥(1-P) x∥.
$$
-/
def is_Lprojection (P : X →L[𝕜] X) : Prop := is_projection P ∧ ∀ (x : X), ∥x∥ = ∥P x∥ + ∥(1-P) x∥

/--
A projection on a normed space `X` is said to be an M-projection if, for all `x` in `X`,
$$
∥x∥ = max(∥P x∥, ∥(1-P) x∥).
$$
-/
def is_Mprojection (P: X →L[𝕜] X) : Prop :=
  is_projection P ∧ ∀ (x : X), ∥x∥ = (max ∥P x∥  ∥(1-P) x∥)

namespace is_Lprojection

lemma Lcomplement {P: X →L[𝕜] X} (h: is_Lprojection P) :  is_Lprojection (1-P) :=
⟨is_projection.complement_iff.mp h.1, λ x, by { rw [add_comm, sub_sub_cancel], exact h.2 x }⟩

lemma Lcomplement_iff (P: X →L[𝕜] X) : is_Lprojection P ↔ is_Lprojection (1-P) := ⟨
  Lcomplement,
  begin
    intros h,
    rw ← sub_sub_cancel 1 P,
    apply Lcomplement h,
  end ⟩

lemma PQ_eq_QPQ (P Q : X →L[𝕜] X) (h₁: is_Lprojection P) (h₂: is_Lprojection Q) :
  P * Q = Q * P * Q :=
begin
  ext,
  rw ← norm_sub_eq_zero_iff,
  have e1 : ∥Q x∥ ≥ ∥Q x∥ + 2 • ∥ (P * Q) x - (Q * P * Q) x∥ :=
  calc ∥Q x∥ = ∥P (Q x)∥ + ∥(1 - P) (Q x)∥ : by rw h₁.right
  ... = ∥Q (P (Q x))∥ + ∥(1-Q) (P (Q x))∥ + ∥(1 - P) (Q x)∥ : by rw h₂.right
  ... = ∥Q (P (Q x))∥ + ∥(1-Q) (P (Q x))∥ + (∥Q ((1 - P) (Q x))∥ + ∥(1-Q) ((1 - P) (Q x))∥) :
    by rw h₂.right ((1 - P) (Q x))
  ... = ∥Q (P (Q x))∥ + ∥(1-Q) (P (Q x))∥ + (∥Q (Q x - P (Q x))∥ + ∥(1-Q) ((1 - P) (Q x))∥) : rfl
  ... = ∥Q (P (Q x))∥ + ∥(1-Q) (P (Q x))∥ + (∥Q (Q x) - Q (P (Q x))∥ + ∥(1-Q) ((1 - P) (Q x))∥) :
    by rw map_sub
  ... = ∥Q (P (Q x))∥ + ∥(1-Q) (P (Q x))∥ + (∥(Q * Q) x - Q (P (Q x))∥ + ∥(1-Q) ((1 - P) (Q x))∥) :
    rfl
  ... = ∥Q (P (Q x))∥ + ∥(1-Q) (P (Q x))∥ + (∥Q x - Q (P (Q x))∥ + ∥(1-Q) ((1 - P) (Q x))∥) :
    by rw [← sq, projection_def h₂.left]
  ... = ∥Q (P (Q x))∥ + ∥(1-Q) (P (Q x))∥ + (∥Q x - Q (P (Q x))∥ + ∥(1-Q) (Q x - P (Q x))∥) : rfl
  ... = ∥Q (P (Q x))∥ + ∥(1-Q) (P (Q x))∥ + (∥Q x - Q (P (Q x))∥ + ∥(1-Q) (Q x) - (1-Q) (P (Q x))∥)
    : by rw map_sub
  ... = ∥Q (P (Q x))∥ + ∥(1-Q) (P (Q x))∥ + (∥Q x - Q (P (Q x))∥
    + ∥((1-Q) * Q) x - (1-Q) (P (Q x))∥) : rfl
  ... = ∥Q (P (Q x))∥ + ∥(1-Q) (P (Q x))∥ + (∥Q x - Q (P (Q x))∥ + ∥0 - (1-Q) (P (Q x))∥) :
    by {rw [sub_mul, ← sq, projection_def h₂.left, one_mul, sub_self ], exact rfl }
  ... = ∥Q (P (Q x))∥ + ∥(1-Q) (P (Q x))∥ + (∥Q x - Q (P (Q x))∥ + ∥(1-Q) (P (Q x))∥) :
    by rw [zero_sub, norm_neg]
  ... = ∥Q (P (Q x))∥ + ∥Q x - Q (P (Q x))∥ + 2•∥(1-Q) (P (Q x))∥  : by abel
  ... ≥ ∥Q x∥ + 2 • ∥ (P * Q) x - (Q * P * Q) x∥ :
    by exact add_le_add_right (norm_le_insert' (Q x) (Q (P (Q x)))) (2•∥(1-Q) (P (Q x))∥),
  rw ge at e1,
  nth_rewrite_rhs 0 ← add_zero (∥Q x∥) at e1,
  rw [add_le_add_iff_left, two_smul,  ← two_mul]  at e1,
  rw le_antisymm_iff,
  split,
  { rw ← mul_zero (2:ℝ) at e1,
    rw mul_le_mul_left at e1, exact e1, norm_num, },
  { apply norm_nonneg, }
end

lemma QP_eq_QPQ (P Q : X →L[𝕜] X) (h₁: is_Lprojection P) (h₂: is_Lprojection Q) : Q * P = Q * P * Q
  :=
begin
  have e1: P * (1 - Q) = P * (1 - Q) - (Q * P - Q * P * Q) :=
  calc P * (1 - Q) = (1 - Q) * P * (1 - Q) : by rw PQ_eq_QPQ P (1 - Q) h₁ h₂.Lcomplement
  ... = 1 * (P * (1 - Q)) - Q * (P * (1 - Q)) : by {rw mul_assoc, rw sub_mul,}
  ... = P * (1 - Q) - Q * (P * (1 - Q)) : by rw one_mul
  ... = P * (1 - Q) - Q * (P - P * Q) : by rw [mul_sub, mul_one]
  ... = P * (1 - Q) - (Q * P - Q * P * Q) : by rw [mul_sub Q, mul_assoc],
  rw [eq_sub_iff_add_eq, add_right_eq_self, sub_eq_zero] at e1,
  exact e1,
end

lemma Lproj_commute {P Q: X →L[𝕜] X} (h₁: is_Lprojection P) (h₂ : is_Lprojection Q) : commute P Q :=
begin
  unfold commute,
  unfold semiconj_by,
  rw PQ_eq_QPQ P Q h₁ h₂,
  nth_rewrite_rhs 0 QP_eq_QPQ P Q h₁ h₂,
end

lemma mul {P Q : X →L[𝕜] X} (h₁ : is_Lprojection P) (h₂ : is_Lprojection Q) :
  is_Lprojection (P*Q) :=
begin
  unfold is_Lprojection,
  split,
  { apply is_projection.mul_of_commute (Lproj_commute h₁ h₂) h₁.left h₂.left, },
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
      ... ≥ ∥P(Q x)∥ + ∥(Q x - P (Q x)) + (x - Q x)∥ :
        by apply (add_le_add_iff_left (∥P(Q x)∥)).mpr (norm_add_le (Q x - P (Q x)) (x - Q x))
      ... = ∥P(Q x)∥ + ∥x - P (Q x)∥ : by rw sub_add_sub_cancel'
      ... = ∥(P * Q) x∥ + ∥(1 - P * Q) x∥ : rfl }, }
end

lemma join {P Q: X →L[𝕜] X} (h₁ : is_Lprojection P) (h₂ : is_Lprojection Q) :
  is_Lprojection (P + Q - P * Q) :=
begin
  have e1:  1 - (1 - P) * (1 - Q) = P + Q - P * Q :=
  calc 1 - (1 - P) * (1 - Q) = 1 -(1 - Q - P * (1 - Q)) : by rw [sub_mul, one_mul]
  ... = Q + P * (1 - Q) : by rw [sub_sub, sub_sub_self]
  ... = P + Q - P * Q : by rw [mul_sub, mul_one, add_sub, add_comm],
  rw ← e1,
  rw ← is_Lprojection.Lcomplement_iff,
  apply is_Lprojection.mul,
  apply is_Lprojection.Lcomplement h₁,
  apply is_Lprojection.Lcomplement h₂,
end

instance : has_compl { f : X →L[𝕜] X // is_Lprojection f } :=
⟨λ P, ⟨1-P, P.prop.Lcomplement⟩⟩

@[simp] lemma coe_compl (P : subtype (is_Lprojection  : (X →L[𝕜] X) → Prop)) :
  ↑(Pᶜ) = (1:X →L[𝕜] X) - ↑P := rfl

instance : has_inf (subtype (is_Lprojection  : (X →L[𝕜] X) → Prop)) :=
⟨λ P Q, ⟨P * Q, P.prop.mul Q.prop⟩ ⟩

@[simp] lemma coe_inf (P Q : subtype (is_Lprojection  : (X →L[𝕜] X) → Prop)) :
  ↑(P ⊓ Q) = ((↑P : (X →L[𝕜] X)) * ↑Q) := rfl

instance : has_sup (subtype (is_Lprojection  : (X →L[𝕜] X) → Prop)) :=
⟨λ P Q, ⟨P + Q - P * Q, P.prop.join Q.prop⟩ ⟩

@[simp] lemma coe_sup (P Q : subtype (is_Lprojection  : (X →L[𝕜] X) → Prop)) :
  ↑(P ⊔ Q) = ((↑P:X →L[𝕜] X) + ↑Q - ↑P * ↑Q) := rfl

instance : has_sdiff (subtype (is_Lprojection  : (X →L[𝕜] X) → Prop)) :=
⟨λ P Q, ⟨P * (1-Q), by exact is_Lprojection.mul P.prop (is_Lprojection.Lcomplement Q.prop) ⟩⟩

@[simp] lemma coe_sdiff (P Q : subtype (is_Lprojection  : (X →L[𝕜] X) → Prop)) :
  ↑(P \ Q) = (↑P:X →L[𝕜] X) * (1-↑Q) := rfl

instance : partial_order (subtype (is_Lprojection  : (X →L[𝕜] X) → Prop)) :=
{ le := λ P Q, (↑P:X →L[𝕜] X) = ↑(P ⊓ Q),
  le_refl := λ P, begin
    simp only [coe_inf],
    rw [← sq, projection_def],
    exact P.prop.left,
  end,
  le_trans := λ P Q R, begin
    intros h₁ h₂,
    simp only [coe_inf],
    have e₁: ↑P = ↑P * ↑Q := h₁,
    have e₂: ↑Q = ↑Q * ↑R := h₂,
    have e₃: (↑P:X →L[𝕜] X) = ↑P * ↑R := begin
      nth_rewrite_rhs 0 e₁,
      rw [mul_assoc, ← e₂, ← e₁],
    end,
    apply e₃,
  end,
  le_antisymm := λ P Q, begin
    intros h₁ h₂,
    have e₁: ↑P = ↑P * ↑Q := h₁,
    have e₂: ↑Q = ↑Q * ↑P := h₂,
    have e₃: (↑P:X →L[𝕜] X) = ↑Q := by rw [e₁, commute.eq (Lproj_commute P.prop Q.prop), ← e₂],
    apply subtype.eq e₃,
  end, }

instance : has_zero (subtype (is_Lprojection  : (X →L[𝕜] X) → Prop))  :=
⟨⟨0, begin
  unfold is_Lprojection,
  split,
  { unfold is_projection,
    rw [sq, zero_mul], },
  { intro, simp only [continuous_linear_map.zero_apply, norm_zero, sub_zero,
      continuous_linear_map.one_apply, zero_add], },
end⟩⟩

@[simp] lemma coe_zero : ↑(0 : subtype (is_Lprojection  : (X →L[𝕜] X) → Prop)) = (0 : X →L[𝕜] X) :=
rfl

instance : has_one (subtype (is_Lprojection  : (X →L[𝕜] X) → Prop))  :=
⟨⟨1, begin
  rw ← sub_zero (1:X →L[𝕜] X),
  apply is_Lprojection.Lcomplement,
  apply (0 : subtype (is_Lprojection  : (X →L[𝕜] X) → Prop)).prop,
end⟩⟩

@[simp] lemma coe_one : ↑(1 : subtype (is_Lprojection  : (X →L[𝕜] X) → Prop)) = (1 : X →L[𝕜] X) :=
rfl

instance : bounded_order (subtype (is_Lprojection  : (X →L[𝕜] X) → Prop)) :=
{ top := 1,
  le_top := λ P, begin
    have e: (↑P:X →L[𝕜] X) = ↑P *  1 := by rw mul_one,
    apply e,
  end,
  bot := 0,
  bot_le := λ P, show 0 ≤ P, from zero_mul P, }

@[simp] lemma coe_bot : ↑(bounded_order.bot : subtype (is_Lprojection  :
  (X →L[𝕜] X) → Prop)) = (0: X →L[𝕜] X) := rfl

@[simp] lemma coe_top : ↑(bounded_order.top : subtype (is_Lprojection  :
  (X →L[𝕜] X) → Prop)) = (1: X →L[𝕜] X) := rfl

lemma compl_mul_left {P : subtype (is_Lprojection  : (X →L[𝕜] X) → Prop)} {Q: X →L[𝕜] X} :
  Q - ↑P * Q = ↑Pᶜ * Q := by rw [coe_compl, sub_mul, one_mul]

lemma compl_orthog {P : subtype (is_Lprojection  : (X →L[𝕜] X) → Prop)} :
  (↑P: X →L[𝕜] X) * (↑ Pᶜ) = 0 :=
by rw [coe_compl, mul_sub, ← sq, mul_one, projection_def P.prop.left, sub_self]

lemma distrib_lattice_lemma {P Q R : subtype (is_Lprojection  : (X →L[𝕜] X) → Prop)} :
  ((↑P:X →L[𝕜] X) + ↑Pᶜ * R) * (↑P + ↑Q * ↑R * ↑Pᶜ) = (↑P + ↑Q * ↑R * ↑Pᶜ) :=
by rw [add_mul, mul_add, mul_add, mul_assoc ↑Pᶜ ↑R (↑Q * ↑R * ↑Pᶜ), ← mul_assoc ↑R (↑Q*↑R)  ↑Pᶜ,
    ← coe_inf Q, commute.eq (Lproj_commute Pᶜ.prop R.prop),
    commute.eq (Lproj_commute (Q⊓R).prop Pᶜ.prop), commute.eq (Lproj_commute R.prop (Q⊓R).prop),
    coe_inf Q, mul_assoc ↑Q, ← mul_assoc, mul_assoc ↑R, commute.eq (Lproj_commute Pᶜ.prop P.prop),
    compl_orthog, zero_mul, mul_zero, zero_add, add_zero, ← mul_assoc, ← sq, ← sq,
    projection_def P.prop.left, projection_def R.prop.left, ← coe_inf Q, mul_assoc,
    commute.eq (Lproj_commute (Q⊓R).prop Pᶜ.prop), ← mul_assoc, ← sq, projection_def Pᶜ.prop.left]

instance : distrib_lattice (subtype (is_Lprojection  : (X →L[𝕜] X) → Prop)) :=
{ le_sup_left := λ P Q, begin
    have e: ↑P = ↑P * ↑(P ⊔ Q) := by rw [coe_sup, ← add_sub, mul_add, mul_sub, ← mul_assoc, ← sq,
      projection_def P.prop.left, sub_self, add_zero],
    apply e,
  end,
  le_sup_right := λ P Q, begin
    have e: (↑Q: X →L[𝕜] X) = ↑Q * ↑(P ⊔ Q) :=
    begin
      rw [coe_sup, ← add_sub, mul_add, mul_sub, commute.eq (Lproj_commute P.prop Q.prop),
        ← mul_assoc, ← sq, projection_def Q.prop.left],
      abel,
    end,
    apply e,
  end,
  sup_le := λ P Q R, begin
    intros h₁ h₂,
    have e₁: ↑P = ↑P * ↑R := h₁,
    have e₂: ↑Q = ↑Q * ↑R := h₂,
    have e:  ↑(P ⊔ Q) = ↑(P ⊔ Q) * ↑R := by rw [coe_sup, ← add_sub, add_mul, sub_mul, mul_assoc,
       ← e₂, ← e₁],
    apply e,
  end,
  inf_le_left := λ P Q, begin
    have e: ↑(P ⊓ Q) = ↑(P ⊓ Q) * ↑P := by rw [coe_inf, mul_assoc,
      commute.eq (Lproj_commute Q.prop P.prop), ← mul_assoc, ← sq, (projection_def P.prop.left)],
    apply e,
  end,
  inf_le_right := λ P Q, begin
    have e: ↑(P ⊓ Q) = ↑(P ⊓ Q) * ↑Q := by
      rw [coe_inf, mul_assoc,  ← sq, (projection_def Q.prop.left)],
    apply e,
  end,
  le_inf := λ P Q R, begin
    intros h₁ h₂,
    have e₁: ↑P = ↑P * ↑Q := h₁,
    have e: ↑P =  ↑P * ↑(Q ⊓ R) := begin
      rw [coe_inf, ← mul_assoc, ← e₁],
      apply h₂,
    end,
    apply e,
  end,
  le_sup_inf := λ P Q R, begin
    have e₁: ↑((P ⊔ Q) ⊓ (P ⊔ R)) = ↑P + ↑Q * ↑R * ↑Pᶜ := by rw [coe_inf, coe_sup, coe_sup,
      ← add_sub, ← add_sub, compl_mul_left, compl_mul_left, add_mul,
      mul_add, commute.eq (Lproj_commute Pᶜ.prop Q.prop), mul_add, ← mul_assoc, mul_assoc ↑Q,
      commute.eq (Lproj_commute Pᶜ.prop P.prop), compl_orthog, zero_mul, mul_zero, zero_add,
      add_zero, ← mul_assoc, mul_assoc ↑Q, ←sq, ← sq, projection_def P.prop.left,
      projection_def Pᶜ.prop.left, mul_assoc, commute.eq (Lproj_commute Pᶜ.prop R.prop),
      ← mul_assoc],
    have e₂ : ↑((P ⊔ Q) ⊓ (P ⊔ R)) * ↑(P ⊔ Q ⊓ R) = ↑P + ↑Q * ↑R * ↑Pᶜ := by rw [coe_inf, coe_sup,
      coe_sup, coe_sup, ← add_sub, ← add_sub, ← add_sub, compl_mul_left, compl_mul_left,
      compl_mul_left, commute.eq (Lproj_commute Pᶜ.prop (Q⊓R).prop), coe_inf, mul_assoc,
      distrib_lattice_lemma, commute.eq (Lproj_commute Q.prop R.prop), distrib_lattice_lemma],
    have e: ↑((P ⊔ Q) ⊓ (P ⊔ R)) = ↑((P ⊔ Q) ⊓ (P ⊔ R)) * ↑(P ⊔ Q ⊓ R) := by rw [e₂, e₁],
    apply e,
  end,
  .. is_Lprojection.subtype.has_inf,
  .. is_Lprojection.subtype.has_sup,
  .. is_Lprojection.subtype.partial_order }

instance : boolean_algebra (subtype (is_Lprojection  : (X →L[𝕜] X) → Prop)) :=
{ sup_inf_sdiff := λ P Q, begin
    apply subtype.eq,
    simp only [subtype.val_eq_coe, coe_sup, coe_inf, coe_sdiff],
    rw [mul_assoc, ← mul_assoc ↑Q, commute.eq (Lproj_commute Q.prop P.prop), mul_assoc ↑P ↑Q,
      ← coe_compl, compl_orthog, mul_zero, mul_zero, sub_zero, ← mul_add, coe_compl,
      add_sub_cancel'_right, mul_one],
  end,
  inf_inf_sdiff := λ P Q, begin
    apply subtype.eq,
    simp only [subtype.val_eq_coe, coe_inf, coe_sdiff, coe_bot],
    rw [mul_assoc, ← mul_assoc ↑Q, commute.eq (Lproj_commute Q.prop P.prop), ← coe_compl, mul_assoc,
      compl_orthog, mul_zero, mul_zero],
  end,
  inf_compl_le_bot := λ P, begin
    apply eq.le,
    apply subtype.eq,
    simp only [subtype.val_eq_coe, coe_inf, coe_compl, coe_bot],
    rw [← coe_compl, compl_orthog],
  end,
  top_le_sup_compl := λ P, begin
    apply eq.le,
    apply subtype.eq,
    simp only [subtype.val_eq_coe, coe_top, coe_sup, coe_compl, add_sub_cancel'_right],
    rw [← coe_compl, compl_orthog, sub_zero],
  end,
  sdiff_eq := λ P Q, begin
    apply subtype.eq,
    simp only [subtype.val_eq_coe, coe_inf, coe_sdiff, coe_compl],
  end,
  .. is_Lprojection.subtype.has_compl,
  .. is_Lprojection.subtype.has_sdiff,
  .. is_Lprojection.subtype.bounded_order,
  .. is_Lprojection.subtype.distrib_lattice }

end is_Lprojection
