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
quill" brackets rather than the usual square brackets.

## Implementation notes

Lie algebras are defined as modules with a compatible Lie ring structure, and thus are partially
unbundled. Since they extend Lie rings, these are also partially unbundled.

## References
* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*][bourbaki1975]

## Tags

lie bracket, ring commutator, jacobi identity, lie ring, lie algebra
-/

universes u v
set_option default_priority 100 -- see Note [default priority]

/--
A binary operation, intended use in Lie algebras and similar structures.
-/
class has_bracket (L : Type v) := (bracket : L → L → L)

notation `⁅`x`,` y`⁆` := has_bracket.bracket x y

namespace ring_commutator

variables {A : Type v} [ring A]

/--
The ring commutator captures the extent to which a ring is commutative. It is identically zero
exactly when the ring is commutative.
-/
def commutator (x y : A) := x*y - y*x

local notation `⁅`x`,` y`⁆` := commutator x y

@[simp] lemma add_left (x y z : A) :
  ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ :=
by simp [commutator, right_distrib, left_distrib]

@[simp] lemma add_right (x y z : A) :
  ⁅z, x + y⁆ = ⁅z, x⁆ + ⁅z, y⁆ :=
by simp [commutator, right_distrib, left_distrib]

@[simp] lemma alternate (x : A) :
  ⁅x, x⁆ = 0 :=
by simp [commutator]

lemma jacobi (x y z : A) :
  ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 :=
begin
  unfold commutator,
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
(add_lie : ∀ (x y z : L), ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆)
(lie_add : ∀ (x y z : L), ⁅z, x + y⁆ = ⁅z, x⁆ + ⁅z, y⁆)
(lie_self : ∀ (x : L), ⁅x, x⁆ = 0)
(jacobi : ∀ (x y z : L), ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0)

section lie_ring

variables {L : Type v} [add_comm_group L] [lie_ring L]

@[simp] lemma add_lie (x y z : L) : ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ := lie_ring.add_lie x y z
@[simp] lemma lie_add (x y z : L) : ⁅z, x + y⁆ = ⁅z, x⁆ + ⁅z, y⁆ := lie_ring.lie_add x y z
@[simp] lemma lie_self (x : L) : ⁅x, x⁆ = 0 := lie_ring.lie_self x

@[simp] lemma lie_skew (x y : L) :
  -⁅y, x⁆ = ⁅x, y⁆ :=
begin
  symmetry,
  rw [←sub_eq_zero_iff_eq, sub_neg_eq_add],
  have H : ⁅x + y, x + y⁆ = 0, from lie_self _,
  rw add_lie at H,
  simpa using H,
end

@[simp] lemma lie_zero (x : L) :
  ⁅x, 0⁆ = 0 :=
begin
  have H : ⁅x, 0⁆ + ⁅x, 0⁆ = ⁅x, 0⁆ + 0 := by { rw ←lie_add, simp, },
  exact add_left_cancel H,
end

@[simp] lemma zero_lie (x : L) :
  ⁅0, x⁆ = 0 := by { rw [←lie_skew, lie_zero], simp, }

@[simp] lemma neg_lie (x y : L) :
  ⁅-x, y⁆ = -⁅x, y⁆ := by { rw [←sub_eq_zero_iff_eq, sub_neg_eq_add, ←add_lie], simp, }

@[simp] lemma lie_neg (x y : L) :
  ⁅x, -y⁆ = -⁅x, y⁆ := by { rw [←lie_skew, ←lie_skew], simp, }

@[simp] lemma gsmul_lie (x y : L) (n : ℤ) :
  ⁅n • x, y⁆ = n • ⁅x, y⁆ :=
begin
  let Ad := λ z, ⁅z, y⁆,
  haveI : is_add_group_hom Ad := { map_add := by simp [Ad], },
  apply is_add_group_hom.map_gsmul Ad,
end

@[simp] lemma lie_gsmul (x y : L) (n : ℤ) :
  ⁅x, n • y⁆ = n • ⁅x, y⁆ :=
begin
  rw [←lie_skew, ←lie_skew x, gsmul_lie],
  unfold has_scalar.smul, rw gsmul_neg,
end

/--
An associative ring gives rise to a Lie ring by taking the bracket to be the ring commutator.
-/
def lie_ring.of_associative_ring (A : Type v) [ring A] : lie_ring A :=
{ bracket  := ring_commutator.commutator,
  add_lie  := ring_commutator.add_left,
  lie_add  := ring_commutator.add_right,
  lie_self := ring_commutator.alternate,
  jacobi   := ring_commutator.jacobi }

end lie_ring

/--
A Lie algebra is a module with compatible product, known as the bracket, satisfying the Jacobi
identity. Forgetting the scalar multiplication, every Lie algebra is a Lie ring.
-/
class lie_algebra (R : Type u) (L : Type v)
  [comm_ring R] [add_comm_group L] extends module R L, lie_ring L :=
(lie_smul : ∀ (t : R) (x y : L), ⁅x, t • y⁆ = t • ⁅x, y⁆)

@[simp] lemma lie_smul  (R : Type u) (L : Type v) [comm_ring R] [add_comm_group L] [lie_algebra R L]
  (t : R) (x y : L) : ⁅x, t • y⁆ = t • ⁅x, y⁆ :=
  lie_algebra.lie_smul t x y

@[simp] lemma smul_lie (R : Type u) (L : Type v) [comm_ring R] [add_comm_group L] [lie_algebra R L]
  (t : R) (x y : L) : ⁅t • x, y⁆ = t • ⁅x, y⁆ :=
  by { rw [←lie_skew, ←lie_skew x y], simp [-lie_skew], }

namespace lie_algebra

variables (R : Type u) (L : Type v) [comm_ring R] [add_comm_group L] [lie_algebra R L]

/--
The adjoint action of a Lie algebra on itself.
-/
def Ad (x : L) : L →ₗ[R] L :=
{ to_fun := has_bracket.bracket x,
  add    := by { intros, apply lie_add },
  smul   := by { intros, apply lie_smul } }

/--
The bracket of a Lie algebra as a bilinear map.
-/
def bil_lie : L →ₗ[R] L →ₗ[R] L :=
{ to_fun := lie_algebra.Ad R L,
  add    := by { unfold lie_algebra.Ad, intros, ext, simp [add_lie], },
  smul   := by { unfold lie_algebra.Ad, intros, ext, simp, } }

/--
An associative algebra gives rise to a Lie algebra by taking the bracket to be the ring commutator.
-/
def of_associative_algebra (A : Type v) [ring A] [algebra R A] : lie_algebra R A :=
{ bracket  := ring_commutator.commutator,
  lie_smul := by { intros, unfold has_bracket.bracket, unfold ring_commutator.commutator,
                   rw [algebra.mul_smul_comm, algebra.smul_mul_assoc, smul_sub], },
  ..lie_ring.of_associative_ring A }

/--
An important class of Lie algebras are those arising from the associative algebra structure on
module endomorphisms.
-/
def of_endomorphism_algebra (M : Type v)
  [add_comm_group M] [module R M] : lie_algebra R (module.End R M) :=
of_associative_algebra R (module.End R M)

end lie_algebra

/--
An important class of Lie algebras are those arising from the associative algebra structure on
square matrices over a commutative ring.
-/
def matrix.lie_algebra (n : Type u) (R : Type v)
  [fintype n] [decidable_eq n] [comm_ring R] : lie_algebra R (matrix n n R) :=
lie_algebra.of_associative_algebra R (matrix n n R)
