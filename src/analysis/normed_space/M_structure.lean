/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import analysis.normed_space.basic
import algebra.ring.idempotents
import tactic.noncomm_ring

/-!
# M-structure

A continuous projection `P` on a normed space `X` is said to be an L-projection if, for all `x` in
`X`,
$$
∥x∥ = ∥P x∥ + ∥(1 - P) x∥.
$$

A continuous projection `P` on a normed space `X` is said to be an M-projection if, for all `x` in
`X`,
$$
∥x∥ = max(∥P x∥,∥(1 - P) x∥).
$$

The L-projections on `X` form a Boolean algebra.

## TODO (Motivational background)

The M-projections on a normed space form a Boolean algebra.

The range of an L-projection on a normed space `X` is said to be an L-summand of `X`. The range of
an M-projection is said to be an M-summand of `X`.

When `X` is a Banach space, the Boolean algebra of L-projections is complete. Let `X` be a normed
space with dual `X^*`. A closed subspace `M` of `X` is said to be an M-ideal if the topological
annihilator `M^∘` is an L-summand of `X^*`.

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

variables {X : Type*} [normed_group X]

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 X]

/--
A projection on a normed space `X` is said to be an L-projection if, for all `x` in `X`,
$$
∥x∥ = ∥P x∥ + ∥(1 - P) x∥.
$$
-/
structure is_Lprojection (P : X →L[𝕜] X) : Prop :=
(proj : is_idempotent_elem P)
(Lnorm : ∀ (x : X), ∥x∥ = ∥P x∥ + ∥(1 - P) x∥)

/--
A projection on a normed space `X` is said to be an M-projection if, for all `x` in `X`,
$$
∥x∥ = max(∥P x∥, ∥(1 - P) x∥).
$$
-/
structure is_Mprojection (P : X →L[𝕜] X) : Prop :=
(proj : is_idempotent_elem P)
(Mnorm : ∀ (x : X), ∥x∥ = (max ∥P x∥  ∥(1 - P) x∥))

namespace is_Lprojection

lemma Lcomplement {P : X →L[𝕜] X} (h: is_Lprojection P) :  is_Lprojection (1 - P) :=
⟨h.proj.one_sub, λ x, by { rw [add_comm, sub_sub_cancel], exact h.Lnorm x }⟩

lemma Lcomplement_iff (P : X →L[𝕜] X) : is_Lprojection P ↔ is_Lprojection (1 - P) :=
⟨Lcomplement, λ h, sub_sub_cancel 1 P ▸ h.Lcomplement⟩

lemma commute {P Q : X →L[𝕜] X} (h₁ : is_Lprojection P) (h₂ : is_Lprojection Q) : commute P Q :=
begin
  have PR_eq_RPR : ∀ R : (X →L[𝕜] X), is_Lprojection R →  (P * R = R * P * R) :=λ R h₃,
  begin
    ext,
    rw ← norm_sub_eq_zero_iff,
    have e1 : ∥R x∥ ≥ ∥R x∥ + 2 • ∥ (P * R) x - (R * P * R) x∥ :=
    calc ∥R x∥ = ∥R (P (R x))∥ + ∥(1 - R) (P (R x))∥ + (∥(R * R) x - R (P (R x))∥
      + ∥(1 - R) ((1 - P) (R x))∥) :
      by rw [h₁.Lnorm, h₃.Lnorm, h₃.Lnorm ((1 - P) (R x)), continuous_linear_map.sub_apply 1 P,
        continuous_linear_map.one_apply, map_sub, continuous_linear_map.coe_mul]
    ... = ∥R (P (R x))∥ + ∥(1 - R) (P (R x))∥ + (∥R x - R (P (R x))∥
      + ∥((1 - R) * R) x - (1 - R) (P (R x))∥) : by rw [h₃.proj.eq,
        continuous_linear_map.sub_apply 1 P, continuous_linear_map.one_apply,
        map_sub,continuous_linear_map.coe_mul]
    ... = ∥R (P (R x))∥ + ∥(1 - R) (P (R x))∥ + (∥R x - R (P (R x))∥ + ∥(1 - R) (P (R x))∥) :
      by rw [sub_mul, h₃.proj.eq, one_mul, sub_self, continuous_linear_map.zero_apply, zero_sub,
        norm_neg]
    ... = ∥R (P (R x))∥ + ∥R x - R (P (R x))∥ + 2•∥(1 - R) (P (R x))∥  : by abel
    ... ≥ ∥R x∥ + 2 • ∥ (P * R) x - (R * P * R) x∥ :
      by exact add_le_add_right (norm_le_insert' (R x) (R (P (R x)))) (2•∥(1 - R) (P (R x))∥),
    rw ge at e1,
    nth_rewrite_rhs 0 ← add_zero (∥R x∥) at e1,
    rw [add_le_add_iff_left, two_smul,  ← two_mul]  at e1,
    rw le_antisymm_iff,
    refine ⟨_, norm_nonneg _⟩,
    rwa [←mul_zero (2 : ℝ), mul_le_mul_left (show (0 : ℝ) < 2, by norm_num)] at e1
  end,
  have QP_eq_QPQ : Q * P = Q * P * Q,
  { have e1 : P * (1 - Q) = P * (1 - Q) - (Q * P - Q * P * Q) :=
    calc P * (1 - Q) = (1 - Q) * P * (1 - Q) : by rw PR_eq_RPR (1 - Q) h₂.Lcomplement
    ... = P * (1 - Q) - (Q * P - Q * P * Q) : by noncomm_ring,
    rwa [eq_sub_iff_add_eq, add_right_eq_self, sub_eq_zero] at e1 },
  show P * Q = Q * P, by rw [QP_eq_QPQ, PR_eq_RPR Q h₂]
end

lemma mul {P Q : X →L[𝕜] X} (h₁ : is_Lprojection P) (h₂ : is_Lprojection Q) :
  is_Lprojection (P * Q) :=
begin
  refine ⟨is_idempotent_elem.mul_of_commute (h₁.commute h₂) h₁.proj h₂.proj, _⟩,
  intro x,
  refine le_antisymm _ _,
  { calc ∥ x ∥ = ∥(P * Q) x + (x - (P * Q) x)∥ : by rw add_sub_cancel'_right ((P * Q) x) x
    ... ≤ ∥(P * Q) x∥ + ∥ x - (P * Q) x ∥ : by apply norm_add_le
    ... = ∥(P * Q) x∥ + ∥(1 - P * Q) x∥ : by rw [continuous_linear_map.sub_apply,
      continuous_linear_map.one_apply] },
  { calc ∥x∥ = ∥P (Q x)∥ + (∥Q x - P (Q x)∥ + ∥x - Q x∥) : by rw [h₂.Lnorm x, h₁.Lnorm (Q x),
      continuous_linear_map.sub_apply, continuous_linear_map.one_apply,
      continuous_linear_map.sub_apply, continuous_linear_map.one_apply, add_assoc]
    ... ≥ ∥P (Q x)∥ + ∥(Q x - P (Q x)) + (x - Q x)∥ :
      (add_le_add_iff_left (∥P(Q x)∥)).mpr (norm_add_le (Q x - P (Q x)) (x - Q x))
    ... = ∥(P * Q) x∥ + ∥(1 - P * Q) x∥ : by rw [sub_add_sub_cancel',
      continuous_linear_map.sub_apply, continuous_linear_map.one_apply,
      continuous_linear_map.coe_mul] }
end

lemma join {P Q : X →L[𝕜] X} (h₁ : is_Lprojection P) (h₂ : is_Lprojection Q) :
  is_Lprojection (P + Q - P * Q) :=
begin
  convert (Lcomplement_iff _).mp (h₁.Lcomplement.mul h₂.Lcomplement) using 1,
  noncomm_ring,
end

instance : has_compl { f : X →L[𝕜] X // is_Lprojection f } :=
⟨λ P, ⟨1 - P, P.prop.Lcomplement⟩⟩

@[simp] lemma coe_compl (P : {P : X →L[𝕜] X // is_Lprojection P}) :
  ↑(Pᶜ) = (1 : X →L[𝕜] X) - ↑P := rfl

instance : has_inf {P : X →L[𝕜] X // is_Lprojection P} :=
⟨λ P Q, ⟨P * Q, P.prop.mul Q.prop⟩ ⟩

@[simp] lemma coe_inf (P Q : {P : X →L[𝕜] X // is_Lprojection P}) :
  ↑(P ⊓ Q) = ((↑P : (X →L[𝕜] X)) * ↑Q) := rfl

instance : has_sup {P : X →L[𝕜] X // is_Lprojection P} :=
⟨λ P Q, ⟨P + Q - P * Q, P.prop.join Q.prop⟩ ⟩

@[simp] lemma coe_sup (P Q : {P : X →L[𝕜] X // is_Lprojection P}) :
  ↑(P ⊔ Q) = ((↑P : X →L[𝕜] X) + ↑Q - ↑P * ↑Q) := rfl

instance : has_sdiff {P : X →L[𝕜] X // is_Lprojection P} :=
⟨λ P Q, ⟨P * (1 - Q), by exact P.prop.mul Q.prop.Lcomplement ⟩⟩

@[simp] lemma coe_sdiff (P Q : {P : X →L[𝕜] X // is_Lprojection P}) :
  ↑(P \ Q) = (↑P : X →L[𝕜] X) * (1 - ↑Q) := rfl

instance : partial_order {P : X →L[𝕜] X // is_Lprojection P} :=
{ le := λ P Q, (↑P : X →L[𝕜] X) = ↑(P ⊓ Q),
  le_refl := λ P, by simpa only [coe_inf, ←sq] using (P.prop.proj.eq).symm,
  le_trans := λ P Q R h₁ h₂, by { simp only [coe_inf] at ⊢ h₁ h₂, rw [h₁, mul_assoc, ←h₂] },
  le_antisymm := λ P Q h₁ h₂, subtype.eq (by convert (P.prop.commute Q.prop).eq) }

lemma le_def (P Q : {P : X →L[𝕜] X // is_Lprojection P}) : P ≤ Q ↔ (P : X →L[𝕜] X) = ↑(P ⊓ Q) :=
iff.rfl

instance : has_zero {P : X →L[𝕜] X // is_Lprojection P}  :=
⟨⟨0, ⟨by rw [is_idempotent_elem, zero_mul],
     λ x, by simp only [continuous_linear_map.zero_apply, norm_zero, sub_zero,
                        continuous_linear_map.one_apply, zero_add]⟩⟩⟩

@[simp] lemma coe_zero : ↑(0 : {P : X →L[𝕜] X // is_Lprojection P}) = (0 : X →L[𝕜] X) :=
rfl

instance : has_one {P : X →L[𝕜] X // is_Lprojection P}  :=
⟨⟨1, sub_zero (1 : X →L[𝕜] X) ▸ (0 : {P : X →L[𝕜] X // is_Lprojection P}).prop.Lcomplement⟩⟩

@[simp] lemma coe_one : ↑(1 : {P : X →L[𝕜] X // is_Lprojection P}) = (1 : X →L[𝕜] X) :=
rfl

instance : bounded_order {P : X →L[𝕜] X // is_Lprojection P} :=
{ top := 1,
  le_top := λ P, (by rw mul_one : (↑P : X  →L[𝕜] X) = ↑P * 1),
  bot := 0,
  bot_le := λ P, show 0 ≤ P, from zero_mul P, }

@[simp] lemma coe_bot : ↑(bounded_order.bot : {P : X →L[𝕜] X // is_Lprojection P}) = (0 : X →L[𝕜] X)
  := rfl

@[simp] lemma coe_top : ↑(bounded_order.top : {P : X →L[𝕜] X // is_Lprojection P}) = (1 : X →L[𝕜] X)
  := rfl

lemma compl_mul_left {P : {P : X →L[𝕜] X // is_Lprojection P}} {Q : X →L[𝕜] X} :
  Q - ↑P * Q = ↑Pᶜ * Q := by rw [coe_compl, sub_mul, one_mul]

lemma compl_orthog {P : {P : X →L[𝕜] X // is_Lprojection P}} :
  (↑P : X →L[𝕜] X) * (↑Pᶜ) = 0 :=
by rw [coe_compl, mul_sub, mul_one, P.prop.proj.eq, sub_self]

lemma distrib_lattice_lemma {P Q R : {P : X →L[𝕜] X // is_Lprojection P}} :
  ((↑P : X →L[𝕜] X) + ↑Pᶜ * R) * (↑P + ↑Q * ↑R * ↑Pᶜ) = (↑P + ↑Q * ↑R * ↑Pᶜ) :=
by rw [add_mul, mul_add, mul_add, mul_assoc ↑Pᶜ ↑R (↑Q * ↑R * ↑Pᶜ), ← mul_assoc ↑R (↑Q * ↑R)  ↑Pᶜ,
    ← coe_inf Q, (Pᶜ.prop.commute R.prop).eq, ((Q ⊓ R).prop.commute Pᶜ.prop).eq,
    (R.prop.commute (Q ⊓ R).prop).eq, coe_inf Q, mul_assoc ↑Q, ← mul_assoc, mul_assoc ↑R,
    (Pᶜ.prop.commute P.prop).eq, compl_orthog, zero_mul, mul_zero, zero_add, add_zero, ← mul_assoc,
    P.prop.proj.eq, R.prop.proj.eq, ← coe_inf Q, mul_assoc, ((Q ⊓ R).prop.commute Pᶜ.prop).eq,
    ← mul_assoc, Pᶜ.prop.proj.eq]

instance : distrib_lattice {P : X →L[𝕜] X // is_Lprojection P} :=
{ le_sup_left := λ P Q, by rw [le_def, coe_inf, coe_sup, ← add_sub, mul_add, mul_sub, ← mul_assoc,
    P.prop.proj.eq, sub_self, add_zero],
  le_sup_right := λ P Q,
  begin
    rw [le_def, coe_inf, coe_sup, ← add_sub, mul_add, mul_sub, commute.eq (commute P.prop Q.prop),
      ← mul_assoc, Q.prop.proj.eq, add_sub_cancel'_right],
  end,
  sup_le := λ P Q R,
  begin
    rw [le_def, le_def, le_def, coe_inf, coe_inf, coe_sup, coe_inf, coe_sup, ← add_sub, add_mul,
      sub_mul, mul_assoc],
    intros h₁ h₂,
    rw [← h₂, ← h₁],
  end,
  inf_le_left := λ P Q, by rw [le_def, coe_inf, coe_inf, coe_inf, mul_assoc,
    (Q.prop.commute P.prop).eq, ← mul_assoc, P.prop.proj.eq],
  inf_le_right := λ P Q, by rw [le_def, coe_inf, coe_inf, coe_inf, mul_assoc, Q.prop.proj.eq],
  le_inf := λ P Q R,
  begin
    rw [le_def, le_def, le_def, coe_inf, coe_inf, coe_inf, coe_inf, ← mul_assoc],
    intros h₁ h₂,
    rw [← h₁, ← h₂],
  end,
  le_sup_inf := λ P Q R,
  begin
    have e₁: ↑((P ⊔ Q) ⊓ (P ⊔ R)) = ↑P + ↑Q * ↑R * ↑Pᶜ :=
    by rw [coe_inf, coe_sup, coe_sup,
      ← add_sub, ← add_sub, compl_mul_left, compl_mul_left, add_mul, mul_add,
      (Pᶜ.prop.commute Q.prop).eq, mul_add, ← mul_assoc, mul_assoc ↑Q, (Pᶜ.prop.commute P.prop).eq,
      compl_orthog, zero_mul, mul_zero, zero_add, add_zero, ← mul_assoc, mul_assoc ↑Q,
      P.prop.proj.eq, Pᶜ.prop.proj.eq, mul_assoc, (Pᶜ.prop.commute R.prop).eq, ← mul_assoc],
    have e₂ : ↑((P ⊔ Q) ⊓ (P ⊔ R)) * ↑(P ⊔ Q ⊓ R) = ↑P + ↑Q * ↑R * ↑Pᶜ := by rw [coe_inf, coe_sup,
      coe_sup, coe_sup, ← add_sub, ← add_sub, ← add_sub, compl_mul_left, compl_mul_left,
      compl_mul_left, (Pᶜ.prop.commute (Q⊓R).prop).eq, coe_inf, mul_assoc, distrib_lattice_lemma,
      (Q.prop.commute R.prop).eq, distrib_lattice_lemma],
    rw [le_def, e₁, coe_inf, e₂],
  end,
  .. is_Lprojection.subtype.has_inf,
  .. is_Lprojection.subtype.has_sup,
  .. is_Lprojection.subtype.partial_order }

instance : boolean_algebra {P : X →L[𝕜] X // is_Lprojection P} :=
{ sup_inf_sdiff := λ P Q,
  subtype.ext (by rw [coe_sup, coe_inf, coe_sdiff, mul_assoc, ← mul_assoc ↑Q,
    (Q.prop.commute P.prop).eq, mul_assoc ↑P ↑Q, ← coe_compl, compl_orthog, mul_zero, mul_zero,
    sub_zero, ← mul_add, coe_compl, add_sub_cancel'_right, mul_one]),
  inf_inf_sdiff := λ P Q,
    subtype.ext (by rw [coe_inf, coe_inf, coe_sdiff, coe_bot, mul_assoc, ← mul_assoc ↑Q,
    (Q.prop.commute P.prop).eq, ← coe_compl, mul_assoc, compl_orthog, mul_zero, mul_zero]),
  inf_compl_le_bot := λ P,
    (subtype.ext (by rw [coe_inf, coe_compl, coe_bot, ← coe_compl, compl_orthog])).le,
  top_le_sup_compl := λ P, (subtype.ext(by rw [coe_top, coe_sup, coe_compl,
    add_sub_cancel'_right, ← coe_compl, compl_orthog, sub_zero])).le,
  sdiff_eq := λ P Q,
  subtype.ext
  (by rw [coe_sdiff, ← coe_compl, coe_inf]),
  .. is_Lprojection.subtype.has_compl,
  .. is_Lprojection.subtype.has_sdiff,
  .. is_Lprojection.subtype.bounded_order,
  .. is_Lprojection.subtype.distrib_lattice }

end is_Lprojection
