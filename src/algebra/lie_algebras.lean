/-
Copyright (c) 2019 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import ring_theory.algebra data.matrix.basic

/-!
# Lie algebras

This file defines Lie rings, and Lie algebras over a commutative ring. It shows how these arise from
associative rings and algebras via the ring commutator. In particular it defines the Lie algebra
of endomorphisms of a module as well as of the algebra of square matrices over a commutative ring.

## Notations

We introduce the notation ⁅x, y⁆ for the Lie bracket. Note that these are the Unicode "square with
quill" square brackets rather than the usual square brackets.

## Implementation notes

Lie algebras are defined as modules with a compatible Lie ring structure, and thus are partially
unbundled. Since they extend Lie rings, these are also partially unbundled.

## References
* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*][bourbaki1975]

## Tags

lie bracket, ring commutator, jacobi identity, lie ring, lie algebra
-/

universes u v

class has_bracket (L : Type v) := (bracket : L → L → L)

notation `⁅`x`,` y`⁆` := has_bracket.bracket x y

namespace ring_commutator

variables (A : Type v) [ring A]

instance bracket : has_bracket A :=
{ bracket := λ x y, x*y - y*x }

@[simp] lemma add_left (x y z : A) :
  ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ :=
by { unfold has_bracket.bracket, simp [right_distrib, left_distrib] }

@[simp] lemma add_right (x y z : A) :
  ⁅z, x + y⁆ = ⁅z, x⁆ + ⁅z, y⁆ :=
by { unfold has_bracket.bracket, simp [right_distrib, left_distrib] }

@[simp] lemma alternate (x : A) :
  ⁅x, x⁆ = 0 :=
by { unfold has_bracket.bracket, simp }

lemma jacobi (x y z : A) :
  ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 :=
begin
  unfold has_bracket.bracket,
  repeat { rw mul_sub_left_distrib },
  repeat { rw mul_sub_right_distrib },
  repeat { rw add_sub },
  repeat { rw ←sub_add },
  repeat { rw ←mul_assoc },
  have h : ∀ (x y z : A), x - y + z + y = x+z := by simp,
  repeat { rw h },
  simp,
end

end ring_commutator

/--
A Lie ring is an additive group with compatible product, known as the bracket, satisfying the
Jacobi identity. The bracket is not associative unless it is identically zero.
-/
class lie_ring (L : Type v) [add_comm_group L] extends has_bracket L :=
(add_left : ∀ (x y z : L), ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆)
(add_right : ∀ (x y z : L), ⁅z, x + y⁆ = ⁅z, x⁆ + ⁅z, y⁆)
(alternate : ∀ (x : L), ⁅x, x⁆ = 0)
(jacobi : ∀ (x y z : L), ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0)

namespace lie_ring

variables (L : Type v) [add_comm_group L] [lie_ring L]

attribute [simp] add_left
attribute [simp] add_right
attribute [simp] alternate
attribute [simp] jacobi

@[simp] protected lemma skew (x y : L) :
  -⁅y, x⁆ = ⁅x, y⁆ :=
begin
  symmetry,
  rw [←sub_eq_zero_iff_eq, sub_neg_eq_add],
  have H : ⁅x + y, x + y⁆ = 0 := by apply lie_ring.alternate,
  rw [lie_ring.add_left,
      lie_ring.add_right, lie_ring.add_right,
      lie_ring.alternate, lie_ring.alternate] at H,
  simp at H,
  exact H,
end

@[simp] protected lemma zero_left (x : L) :
  ⁅x, 0⁆ = 0 :=
begin
  have H : ⁅x, 0⁆ + ⁅x, 0⁆ = ⁅x, 0⁆ + 0 := by { rw ←lie_ring.add_right, simp, },
  exact add_left_cancel H,
end

@[simp] protected lemma zero_right (x : L) :
  ⁅0, x⁆ = 0 := by { rw [←lie_ring.skew, lie_ring.zero_left], simp, }

@[simp] protected lemma neg_left (x y : L) :
  ⁅-x, y⁆ = -⁅x, y⁆ := by { rw [←sub_eq_zero_iff_eq, sub_neg_eq_add, ←lie_ring.add_left], simp, }

@[simp] protected lemma neg_right (x y : L) :
  ⁅x, -y⁆ = -⁅x, y⁆ := by { rw [←lie_ring.skew, ←lie_ring.skew], simp, }

instance of_associative_ring (A : Type v) [ring A] : lie_ring A :=
{ add_left  := ring_commutator.add_left A,
  add_right := ring_commutator.add_right A,
  alternate := ring_commutator.alternate A,
  jacobi    := ring_commutator.jacobi A }

end lie_ring

/--
A Lie algebra is a module with compatible product, known as the bracket, satisfying the Jacobi
identity. Forgetting the scalar multiplication, every Lie algebra is a Lie ring.
-/
class lie_algebra (R : Type u) (L : Type v)
  [comm_ring R] [add_comm_group L] extends module R L, lie_ring L :=
(smul_right : ∀ (t : R) (x y : L), ⁅x, t • y⁆ = t • ⁅x, y⁆)

namespace lie_algebra

variables (R : Type u) (L : Type v) [comm_ring R] [add_comm_group L] [lie_algebra R L]

attribute [simp] smul_right

@[simp] protected lemma smul_left (t : R) (x y : L) :
  ⁅t • x, y⁆ = t • ⁅x, y⁆ :=
by { rw [←lie_ring.skew, ←lie_ring.skew _ x y], simp [-lie_ring.skew] }

def adjoint_action (x : L) : L →ₗ[R] L :=
{ to_fun := has_bracket.bracket x,
  add    := by { intros, apply lie_ring.add_right },
  smul   := by { intros, apply lie_algebra.smul_right } }

def bracket_bilinear : L →ₗ[R] L →ₗ[R] L :=
{ to_fun := lie_algebra.adjoint_action R L,
  add    := by { unfold lie_algebra.adjoint_action, intros, ext, simp [lie_ring.add_left], },
  smul   := by { unfold lie_algebra.adjoint_action, intros, ext, simp, } }

instance of_associative_algebra (A : Type v) [ring A] [algebra R A] : lie_algebra R A :=
begin
  apply @lie_algebra.mk R A _ _ _ (lie_ring.of_associative_ring A),
  intros t x y,
  unfold has_bracket.bracket,
  rw [algebra.mul_smul_comm, algebra.smul_mul_assoc, smul_sub],
end

instance of_endomorphism_algebra (M : Type v)
  [add_comm_group M] [module R M] : lie_algebra R (module.End R M) := infer_instance

end lie_algebra

instance matrix.lie_algebra (n : Type u) (R : Type v)
  [fintype n] [decidable_eq n] [comm_ring R] : lie_algebra R (matrix n n R) := infer_instance
