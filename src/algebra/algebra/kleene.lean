
/-
Copyright (c) 2022 Siddhartha Prasad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Prasad.
-/


import data.real.basic
import data.vector
import tactic.explode
import tactic.find
import tactic.induction
import tactic.rcases
import tactic.rewrite

/-!
# Kleene Algebras

This file defines Kleene algebras, which are used extensively in theory of computation.

A Kleene algebra is an idempotent semiring with an additional unary operator
called a Kleene star (⋆).

## References

* (Kozen, D. . A completeness theorem for Kleene algebras and the algebra of regular events.)
  [https://www.cs.cornell.edu/~kozen/Papers/ka.pdf].
* https://planetmath.org/idempotentsemiring
* https://encyclopediaofmath.org/wiki/Idempotent_semi-ring
* https://planetmath.org/kleenealgebra


## Tags

kleene algebra

-/



namespace isemiring

universe u
variables {α : Type u}

/--
An isemiring is a semiring with the additional property that the addition (+)
operation is idempotent.

For some idempotent semiring S,  ∀ x ∈ S, `x + x = x`.

Additionally, the binary relation ≤ defines a partial order on isemirings.
where, a ≤ b ↔ a + b = b

-/

class isemiring  (α : Type u) extends semiring α, partial_order α :=
(idem_add : ∀ a : α, a + a = a)
(le_def : ∀ a b : α, a ≤ b ↔ a + b = b)

variables [isemiring α] {a b c: α}


/--  a = b iff a ≤ b and b ≤ a --/
lemma ineq_of_eq : ∀ a b : α, a = b ↔ a ≤ b ∧ b ≤ a :=
  begin
    intros a b,
    apply iff.intro,
    { intro h,
      exact antisymm_iff.mpr h, },
    { intro h,
      exact le_antisymm_iff.mpr h,}
  end


/-- The addition operator on isemirings is monotonic. --/
lemma le_of_add : ∀ x y : α, x ≤ x + y :=
begin
  intros x y,
  apply iff.elim_right (isemiring.le_def x (x + y)),
  have : x + (x + y) = (x + x) + y := by exact (add_assoc x x y).symm,
  rw [this],
  rw (isemiring.idem_add x),
end


/-- The addition operator on isemirings is monotonic across the partial order --/
lemma add_monotone : ∀ a b c: α, a ≤ b → a + c ≤ b + c :=
begin
  intros x y c h,
  rw [isemiring.le_def] at *,
  have h₁ : x + y + c + c = y + c + c :=
        by exact congr_arg2 has_add.add (congr_fun (congr_arg has_add.add h) c) rfl,
  have h₂ : x + y + c + c = (x + c) + (y + c) :=
    begin
      calc x + y + c + c = x + y + (c + c) : by exact add_assoc (x + y) c c
      ...  = x + (y + (c + c)) : by exact add_assoc x y (c + c)
      ...  = x + ((y + c) + c) : by rw [add_assoc]
      ... = (x + (y + c)) + c : by exact (add_assoc x (y + c) c).symm
      ... = (x + c) + (y + c) : by  exact add_right_comm x (y + c) c,
    end,
  have h₃ : y + c + c = y + c :=
    begin
      calc y + c + c  = y + (c + c) : _
      ... = y + c : _,
      { exact add_assoc y c c, },
      { rw (isemiring.idem_add c), }
    end,
  have h₃ : (x + c) + (y + c) = (y + c) := by exact (eq.congr h₂ h₃).mp h₁,
  exact h₃,
end


/-- If c is the supremum of a and b with respect to ≤, then c
is also the supremum of a + b. -/
lemma supremum_of_add : ∀ a b c : α, a ≤ c → b ≤ c → (a + b) ≤ c
:=
begin
  intros a b c h₁ h₂,
  have ha : a ≤ a + b := by exact le_of_add a b,
  have hb : b ≤ a + b :=
  begin
    rw [add_comm a b],
    exact le_of_add b a,
  end,

  have ha₁ : a + c = c := by exact (isemiring.le_def a c).mp h₁,
  have hb₁ : b +c = c := by exact (isemiring.le_def b c).mp h₂,

  have h_inter : (a + c) + (b + c) = c :=
  begin
    simp [ha₁, hb₁],
    exact (isemiring.idem_add c),
  end,

  have h₃: (a + b) + c = c :=
  begin
    have hassoc : (a + c) + (b + c) = (a + b) + (c + c) := by finish,
    simp [isemiring.idem_add c] at hassoc,
    simp [hassoc] at h_inter,
    exact h_inter,
    end,
    exact (isemiring.le_def (a + b) c).mpr h₃
end

/-- 0 is the bottom element of an isemiring. --/
lemma partial_order_of_zero  : ∀ a : α,  (0 : α) ≤  a :=
begin
  intro a,
  have : 0 + a = a := by exact zero_add a,
  simp [isemiring.le_def],
end

/--
 c is the supremum of a and b with respect to ≤ iff
 c is the supremum of a + b.
--/
lemma ineq_of_add : ∀ a b c : α, a + b ≤ c ↔ a ≤ c ∧ b ≤ c  :=
begin
  intros a b c,
  apply iff.intro,
  { intro h,
    apply and.intro,
    { have h_ineq₁ : a ≤ a + b := le_of_add a b,
      exact le_trans h_ineq₁ h, },
    { have h_ineq₂ : b ≤ b + a :=  le_of_add b a,
      rw ←(add_comm a b) at h_ineq₂,
      exact le_trans h_ineq₂ h, }},
  { have h₁ := supremum_of_add a b c,
    intros h,
    cases' h,
    exact h₁ left right, }
end


/--
  Multiplication preserves the partial order defined by ≤.
--/
lemma mul_monotone : ∀ a b c: α, a ≤ b → (c*a) ≤ (c*b)
:=
begin
  intros a b c h,
  have h_le : b = (a + b) := by exact eq.symm ((isemiring.le_def a b).mp h),
  have h_distr : c * (a + b) = (c* a) + (c * b) := by exact mul_add c a b,

  rw [h_le, h_distr, isemiring.le_def],
  rw (add_assoc (c * a) (c * a) (c * b)).symm,
  rw isemiring.idem_add (c * a),
end

/--
  Multiplication preserves the partial order defined by ≤ (commutative variation).
--/
lemma mul_monotone_comm : ∀ a b c: α, a ≤ b → (a*c) ≤ (b*c)
:=
begin
  intros a b c h,
  have h_le : b = (a + b) := by exact eq.symm ((isemiring.le_def a b).mp h),
  have h_distr :(a + b)*c = ( a * c) + ( b * c) := by exact add_mul a b c,
  rw [h_le, h_distr, isemiring.le_def],
  rw (add_assoc (a * c) (a * c) (b * c)).symm,
  rw isemiring.idem_add (a * c),
end

end isemiring

namespace kleene_algebra

universe u
variables {α : Type u}

/--
A Kleene Algebra is an isemiring with an additional unary operator (star), that
satisfies the following properties:

1 + a* (a∗) ≤ (a∗)
1 + (a∗) * a ≤ (a∗)

a*c + b ≤ c ⇒ (a∗) * b ≤ c
c*a + b ≤ c ⇒ b * (a∗) ≤ c ,

-/
class kleene_algebra (α : Type u) extends isemiring.isemiring α :=
  (star :  α → α)
  (star_unfold_right : ∀ a : α, (1 : α) + a * (star a) ≤  star a)
  (star_unfold_left :  ∀ a : α, (1 : α) + (star a) * a ≤ star a)
  (star_inf_right : ∀ a b c: α,  a*c + b ≤ c → (star a) * b ≤ c)
  (star_inf_left : ∀ a b c: α,  c*a + b ≤ c → b*(star a) ≤ c)

notation  a`∗` := kleene_algebra.star a

variables [kleene_algebra α] {a b c: α}

open isemiring


/--
 (a ∗)*b is the least prefixpoint of the monotone map x ↦ b + a*x
--/
lemma lfp_monotone : ∀ a b : α, b + (a∗)* a * b ≤ (a∗) * b :=
begin
  intros a b,
  have h₀ : (1 + (a∗)*a) * b = b +  (a∗) * a * b :=
  begin
    exact one_add_mul ((a∗)*a) b
  end,

  have h₁: (1 + (a∗)*a) * b ≤ (a∗) * b  :=
  begin
    have ha := (kleene_algebra.star_unfold_left a),
    exact mul_monotone_comm (1 + (a∗)*a) (a∗) b ha,
  end,
  exact (eq.symm h₀).trans_le h₁
end

/--
  Kleene star (∗) preserves monotonicity on the partial order ≤.
--/
lemma star_monotone : ∀a b : α, a ≤ b → (a∗) ≤ (b ∗) :=
begin
  intros x y h,
  have h₀ := kleene_algebra.star_inf_left x 1 (y ∗ ),
  simp [mul_one] at h₀,
  apply h₀,
  have h₁ : (y ∗)*x + 1 ≤ (y ∗)*y + 1 := -- by monotonicity,
  begin
    exact add_monotone ((y ∗)*x) ((y∗)*y) 1 (mul_monotone x y (y ∗) h),
  end,
  have h₂ : (y ∗)* y + 1 ≤ (y∗) :=
  begin
    have hh := lfp_monotone y 1,
    simp [mul_one] at hh,
    rw [add_comm] at hh,
    exact hh,
  end,
  exact le_trans h₁ h₂,
end

/--
1 is the bottom element of the kleene star.
--/
lemma partial_order_of_one : ∀ a : α, 1 ≤ (a∗) :=
begin
  intro a,
  have h₀ := kleene_algebra.star_unfold_left a,
  have h₁ := (ineq_of_add 1 ((a∗)* a) (a∗)).mp h₀,
  cases' h₁,
  exact left,
end

/-
  This section shows that for some element x in a Kleene Algebra, x∗ is the
  reflexive and transitive element dominating x.
-/


/--
  All members 'a', of a kleene algebra are ordered lower than (a∗)
--/
lemma ineq_of_star : ∀ a : α, a ≤ (a∗) :=
begin
  intro a,
  have h₀ := kleene_algebra.star_unfold_right a,
  have h₁ : a ≤ a * (a∗) :=
  begin
     have h_int := mul_monotone 1 (a∗) a (partial_order_of_one a),
     simp [mul_one] at h_int,
     exact h_int,
  end,
  have h₂ : a * (a∗) ≤ 1 + a * (a∗) :=
  begin
    rw [add_comm],
    exact le_of_add (a * (a∗)) 1,
  end,
  exact le_implies_le_of_le_of_le h₁ h₀ h₂,
end

/--
  For all members 'a' of a Kleene Algebra,
  the product of (a∗) with itself is ordered lower that a∗.
--/
lemma mul_of_star_le : ∀ a : α, (a∗) * (a∗) ≤ (a∗) :=
begin
  intro a,
  have h := kleene_algebra.star_unfold_right a,
  have h₀ : a*(a∗) ≤ 1 + a*(a∗) :=
  begin
    rw [add_comm],
    exact le_of_add (a * (a∗)) 1,
  end,
  have h₁ : a*(a∗) ≤ (a∗) := by exact le_trans h₀ h,
  have h₂ :  a*(a∗) + (a∗) ≤ (a∗) :=
  begin
    have h' : a*(a∗) + (a∗) ≤ (a∗) + (a∗) := by
        exact add_monotone (a*(a∗)) (a∗) (a∗) h₁,
    rw [isemiring.idem_add (a∗)] at h',
    exact h',
  end,
  apply kleene_algebra.star_inf_right a (a∗) (a∗) h₂,
end

/--
  For all members 'a' of a Kleene Algebra,
  the product of (a∗) with itself is  equal to a∗.
--/
lemma mul_of_star : ∀ a : α, (a∗) * (a∗) = (a∗) :=
begin
  intro a,
  have h₁ := mul_monotone 1 (a∗) (a∗) (partial_order_of_one a),
  simp [mul_one] at h₁,
  have h₂ := mul_of_star_le a,
  have h₃ := (isemiring.ineq_of_eq ((a∗)*(a∗)) (a∗)).mpr,
  apply h₃,
  apply and.intro h₂ h₁,
end

/--
  Kleene star is idempotent.
--/
lemma star_of_star : ∀ a : α, (a∗) = ((a∗) ∗) :=
begin
  intro a,

  have h₁ : (a∗) ≤ ((a∗) ∗) := by exact star_monotone a (a∗) (ineq_of_star a),
  have h₂ : ((a∗)∗) ≤ (a∗) :=
  begin
    have h := kleene_algebra.star_inf_right (a ∗ ) 1 (a ∗ ),
    simp [mul_one] at h,
    apply h,
    rw mul_of_star,

    have h' := add_monotone 1 (a ∗) (a ∗) (partial_order_of_one a),
    rw [isemiring.idem_add (a ∗ )] at h',
    rw [add_comm],
    exact h',
  end,
  have h₃ := (isemiring.ineq_of_eq (a∗) ((a∗)∗)).mpr,
  apply h₃,
  apply and.intro h₁ h₂,
end

end kleene_algebra
