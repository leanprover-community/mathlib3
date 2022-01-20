/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

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

/-- Notation class for the triple product -/
class has_tp (A : Type*) := (tp : A → A → A → A )

notation ⦃a, b, c⦄ := has_tp.tp a b c

/-- A triple product is a trilinear map, symmetric in the first and third variable -/
class is_tp (A : Type*) [has_tp A] [has_add A] :=
(comm : ∀ (a b c : A), ⦃a, b, c⦄ = ⦃c, b, a⦄)
(ladd : ∀ (a₁ a₂ b c : A), ⦃(a₁+a₂), b, c⦄ = ⦃a₁, b, c⦄ + ⦃a₂, b, c⦄)
(madd : ∀ (a b₁ b₂ c : A), ⦃a, (b₁+b₂), c⦄ = ⦃a, b₁, c⦄ + ⦃a, b₂, c⦄)

/-- A Jordan triple product satisfies a Leibniz law -/
class is_jordan_tp (A : Type*) [has_tp A] [has_add A] [has_sub A] :=
(leibniz : ∀ (a b c d e: A), ⦃a, b, ⦃c, d, e⦄⦄  =
  ⦃⦃a, b, c⦄, d, e⦄ - ⦃c, ⦃b, a, d⦄, e⦄ + ⦃c, d, ⦃a, b, e⦄⦄)

/--
We say that a pair of operators $(T,T^′)$ are Leibniz if they satisfy a law reminiscent of
differentiation.
-/
def leibniz {A : Type*} [has_tp A] [has_add A] (T : A → A) (T'  : A → A) :=
  ∀ (a b c : A),  T ⦃ a, b, c ⦄  = ⦃ T a, b, c⦄ + ⦃a, T' b, c⦄ + ⦃a, b, T c⦄

namespace is_tp

lemma radd {A : Type*} [has_tp A] [has_add A] [is_tp A] (a b c₁ c₂ : A) :
  ⦃a, b, c₁ + c₂⦄ = ⦃a, b, c₁⦄ + ⦃a, b, c₂⦄ := by rw [comm, ladd, comm, comm c₂]

variables {A : Type*} [has_tp A] [add_comm_group A] [is_tp A]

lemma lzero (b c : A) : ⦃0, b, c⦄ = 0 :=
(add_monoid_hom.mk' (λ (a : A), ⦃a, b, c⦄) (λ a₁ a₂, ladd a₁ a₂ b c )).map_zero

lemma mzero (a c : A) : ⦃a, 0, c⦄ = 0 :=
(add_monoid_hom.mk' (λ (b : A), ⦃a, b, c⦄) (λ b₁ b₂ , madd a b₁ b₂ c)).map_zero

lemma rzero (a b : A) : ⦃a, b, 0⦄ = 0 :=
by rw [comm, lzero]

lemma lzsmul (a b c : A) (z : ℤ) : ⦃z•a, b, c⦄ = z•⦃a, b, c⦄ :=
add_monoid_hom.map_zsmul ⟨λ (a : A), ⦃a, b, c⦄, lzero b c, λ _ _, ladd _ _ _ _⟩ _ _

lemma mzsmul (a b c : A) (z : ℤ) : ⦃a, z•b, c⦄ = z•⦃a, b, c⦄ :=
add_monoid_hom.map_zsmul ⟨λ (b : A), ⦃a, b, c⦄, mzero a c, λ _ _, madd _ _ _ _⟩ _ _

lemma rzsmul (a b : A) (z : ℤ) (c : A) : ⦃a, b, z•c⦄ = z•⦃a, b, c⦄ :=
  by rw [comm, lzsmul, comm]

lemma lneg (a b c : A) : ⦃-a, b, c⦄ = -⦃a, b, c⦄ :=
by rw [←sub_eq_zero, sub_neg_eq_add, ←ladd, neg_add_self, lzero]

lemma mneg (a b c : A): ⦃a, -b, c⦄ = -⦃a, b, c⦄ :=
by rw [←sub_eq_zero, sub_neg_eq_add, ←madd, neg_add_self, mzero]

lemma rneg (a b c : A): ⦃a, b, -c⦄ = -⦃a, b, c⦄ := by rw [comm, lneg, comm]

lemma lsub (a b c d : A) : ⦃a - d, b, c⦄ = ⦃a, b, c⦄ - ⦃d, b, c⦄ :=
by rw [eq_sub_iff_add_eq, ← ladd, sub_add_cancel]

lemma msub (a b c d : A) : ⦃a, b - c, d⦄ = ⦃a, b, d⦄ - ⦃a, c, d⦄ :=
by rw [eq_sub_iff_add_eq, ← madd, sub_add_cancel]


lemma rsub (a b c d : A) : ⦃a, b, c - d⦄ = ⦃a, b, c⦄ - ⦃a, b, d⦄ :=
by rw [comm, lsub, comm, comm d]

lemma lr_bilinear (a₁ a₂ b c₁ c₂ : A) : ⦃a₁ + a₂, b, c₁ + c₂⦄ =
  ⦃a₁, b, c₁⦄ + ⦃a₁, b, c₂⦄ + ⦃a₂, b, c₁⦄ + ⦃a₂, b, c₂⦄ :=
calc ⦃a₁ + a₂, b, c₁ + c₂⦄ = ⦃a₁, b, c₁ + c₂⦄ + ⦃a₂, b, c₁ + c₂⦄ : by rw ladd
... = ⦃a₁, b, c₁⦄ + ⦃a₁, b, c₂⦄ + ⦃a₂, b, c₁ + c₂⦄ : by rw radd
... = ⦃a₁, b, c₁⦄ + ⦃a₁, b, c₂⦄ + (⦃a₂, b, c₁⦄ + ⦃a₂, b, c₂⦄) : by rw radd
... = ⦃a₁, b, c₁⦄ + ⦃a₁, b, c₂⦄ + ⦃a₂, b, c₁⦄ + ⦃a₂, b, c₂⦄ : by rw ← add_assoc

lemma polar (a b c : A) : ⦃a + c, b, a + c⦄ = ⦃a, b, a⦄ + 2•⦃a, b, c⦄ + ⦃c, b, c⦄ :=
calc ⦃a + c, b, a + c⦄ = ⦃a, b, a⦄ + ⦃a, b, c⦄ + ⦃c, b, a⦄ + ⦃c, b, c⦄ :
  by rw lr_bilinear a c b a c
... = ⦃a, b, a⦄ + ⦃a, b, c⦄ + ⦃a, b, c⦄ + ⦃c, b, c⦄ : by rw comm c b a
... = ⦃a, b, a⦄ + (⦃a, b, c⦄ + ⦃a, b, c⦄)  + ⦃c, b, c⦄ : by rw ← add_assoc
... = ⦃a, b, a⦄ + 2•⦃a, b, c⦄ + ⦃c, b, c⦄ : by rw two_nsmul

/-- The triple product as an additive monoid homomorphism in each variable -/
@[simps] def add_monoid_hom.tp : A →+ A →+ A →+ A :=
{ to_fun := λ a,
  { to_fun := λ b,
    { to_fun := λ c, ⦃a, b, c⦄,
      map_zero' := by rw rzero,
      map_add' := λ _ _, by rw radd, },
    map_zero' := add_monoid_hom.ext $ λ _, by exact mzero _ _,
    map_add' := λ a₁ a₂, add_monoid_hom.ext $ λ _, by exact madd _ _ _ _, },
  map_zero' := add_monoid_hom.ext $ λ _, add_monoid_hom.ext $ λ _, by exact lzero _ _,
  map_add' := λ a₁ a₂, add_monoid_hom.ext $ λ b, add_monoid_hom.ext $ λ _, by exact ladd _ _ _ _, }

/-- Define the multiplication operator `D` -/
@[simps] def D : A →+ A →+ add_monoid.End A := add_monoid_hom.tp

/-- Define the quadratic operator `Q` -/
@[simps] def Q : A →+ A →+  add_monoid.End A :=
{ to_fun := λ a, (D a : A →+  add_monoid.End A).flip,
  map_zero' := by { ext, simp, },
  map_add' := λ _ _, by { ext, simp, }, }

lemma Q_def (a b c : A) : Q a c b = ⦃a, b, c⦄ := by simp

def Q' : A →+ A →+  add_monoid.End A := D.comp add_monoid_hom.flip

end is_tp

variables {A : Type*} [has_tp A] [add_comm_group A] [is_tp A]

open is_tp (D)

lemma lie_D_D [is_jordan_tp A] (a b c d: A) : ⁅D a b, D c d⁆ = D ⦃a, b, c⦄ d - D c ⦃b, a, d⦄ :=
begin
  ext e,
  rw ring.lie_def,
  simp only [add_monoid_hom.sub_apply, function.comp_app, is_tp.D_apply_apply_apply,
    add_monoid.coe_mul],
  rw [sub_eq_iff_eq_add, is_jordan_tp.leibniz],
end

/--
For a and b in A, the pair D(a,b) and -D(b,a) are Leibniz
-/
lemma D_D_leibniz [is_jordan_tp A] (a b : A) : leibniz (D a b) (-D b a) := begin
  unfold leibniz,
  intros c d e,
  rw [is_tp.D_apply_apply_apply, is_tp.D_apply_apply_apply, is_tp.D_apply_apply_apply, pi.neg_apply,
  is_tp.D_apply_apply_apply, is_tp.mneg, tactic.ring.add_neg_eq_sub, is_jordan_tp.leibniz],
end
