/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import algebra.ternary
import algebra.lie.of_associative

/-!
# Jordan triples

Let `A` be a module over a ring `R`. A triple product on `A` is a trilinear map
$\{.\,.\,\}:A\times A\times A\mapsto A$ which is symmetric in the first and third variables. The
module `A` is said to be a Jordan triple if, for any `a`, `b`, `c`, `d` and `e` in `A` the following
Leibniz rule is satisfied:
$$
\{a\,b\,\{c\,d\,e\}\} = \{\{a\,b\,c\}\,d\,e\} - \{c\,\{b\,a\,d\}\,e\} + \{c\,d\,\{a\,b\,e\}\}
$$
A module `A` over a *-ring `R` is said to be a *-triple if it has a triple product linear and
symmetric in the first and thrid variable and conjugate linear in the second variable. A *-triple
satisfying the Leibniz rule is said to be a Jordan *-triple.

As well as being of algebraic interest, Jordan *-triples arise naturally in mathematical physics,
functional analysis and differential geometry. For more information about these connections the
interested reader is referred to [alfsenshultz2003], [chu2012], [friedmanscarr2005],
[iordanescu2003] and [upmeier1987].

## Main results

(None yet, we're just getting started.)

## References

* [Chu, Jordan Structures in Geometry and Analysis][chu2012]
-/

notation ⦃a, b, c⦄ := has_tp.tp a b c

/-- A Jordan triple product satisfies a Leibniz law -/
class is_jordan_tp (A : Type*) [has_add A] [has_sub A] extends has_trilinear_tp A:=
(comm : ∀ (a b c : A), ⦃a, b, c⦄ = ⦃c, b, a⦄)
(leibniz : ∀ (a b c d e: A), ⦃a, b, ⦃c, d, e⦄⦄  =
  ⦃⦃a, b, c⦄, d, e⦄ - ⦃c, ⦃b, a, d⦄, e⦄ + ⦃c, d, ⦃a, b, e⦄⦄)

/--
We say that a pair of operators $(T,T^′)$ are Leibniz if they satisfy a law reminiscent of
differentiation.
-/
def leibniz {A : Type*} [has_tp A] [has_add A] (T : A → A) (T'  : A → A) :=
  ∀ (a b c : A),  T ⦃ a, b, c ⦄  = ⦃ T a, b, c⦄ + ⦃a, T' b, c⦄ + ⦃a, b, T c⦄

namespace is_jordan_tp

variables {A : Type*} [add_comm_group A] [is_jordan_tp A]

lemma polar (a b c : A) : ⦃a + c, b, a + c⦄ = ⦃a, b, a⦄ + 2•⦃a, b, c⦄ + ⦃c, b, c⦄ :=
calc ⦃a + c, b, a + c⦄ = ⦃a, b, a⦄ + ⦃a, b, c⦄ + ⦃c, b, a⦄ + ⦃c, b, c⦄ :
  by rw has_trilinear_tp.lr_bilinear a c b a c
... = ⦃a, b, a⦄ + ⦃a, b, c⦄ + ⦃a, b, c⦄ + ⦃c, b, c⦄ : by rw comm c b a
... = ⦃a, b, a⦄ + (⦃a, b, c⦄ + ⦃a, b, c⦄)  + ⦃c, b, c⦄ : by rw ← add_assoc
... = ⦃a, b, a⦄ + 2•⦃a, b, c⦄ + ⦃c, b, c⦄ : by rw two_nsmul

/-- Define the multiplication operator `D` -/
@[simps] def D : A →+ A →+ add_monoid.End A := add_monoid_hom.tp

/-- Define the quadratic operator `Q` -/
@[simps] def Q : A →+ A →+  add_monoid.End A :=
{ to_fun := λ a, (D a : A →+  add_monoid.End A).flip,
  map_zero' := by { ext, simp, },
  map_add' := λ _ _, by { ext, simp, }, }

lemma Q_def (a b c : A) : Q a c b = ⦃a, b, c⦄ := by simp

end is_jordan_tp

variables {A : Type*} [add_comm_group A] [is_jordan_tp A]

open is_jordan_tp (D)

lemma lie_D_D [is_jordan_tp A] (a b c d: A) : ⁅D a b, D c d⁆ = D ⦃a, b, c⦄ d - D c ⦃b, a, d⦄ :=
begin
  ext e,
  rw ring.lie_def,
  simp only [add_monoid_hom.sub_apply, function.comp_app, is_jordan_tp.D_apply_apply_apply,
    add_monoid.coe_mul],
  rw [sub_eq_iff_eq_add, is_jordan_tp.leibniz],
end

/--
For a and b in A, the pair D(a,b) and -D(b,a) are Leibniz
-/
lemma D_D_leibniz [is_jordan_tp A] (a b : A) : leibniz (D a b) (-D b a) := begin
  unfold leibniz,
  intros c d e,
  rw [is_jordan_tp.D_apply_apply_apply, is_jordan_tp.D_apply_apply_apply,
  is_jordan_tp.D_apply_apply_apply, pi.neg_apply, is_jordan_tp.D_apply_apply_apply,
  has_trilinear_tp.mneg, tactic.ring.add_neg_eq_sub, is_jordan_tp.leibniz],
end
