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

It also includes definitions of morphisms of Lie algebras, Lie subalgebras, Lie modules, Lie
submodules, and the quotient of a Lie algebra by an ideal.

## Notations

We introduce the notation ⁅x, y⁆ for the Lie bracket. Note that these are the Unicode "square with
quill" brackets rather than the usual square brackets.

We also introduce the notations L →ₗ⁅R⁆ L' for a morphism of Lie algebras over a commutative ring R,
and L →ₗ⁅⁆ L' for the same, when the ring is implicit.

## Implementation notes

Lie algebras are defined as modules with a compatible Lie ring structure, and thus are partially
unbundled. Since they extend Lie rings, these are also partially unbundled.

## References
* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*][bourbaki1975]

## Tags

lie bracket, ring commutator, jacobi identity, lie ring, lie algebra
-/

universes u v

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

section prio
set_option default_priority 100 -- see Note [default priority]
/--
A Lie ring is an additive group with compatible product, known as the bracket, satisfying the
Jacobi identity. The bracket is not associative unless it is identically zero.
-/
class lie_ring (L : Type v) [add_comm_group L] extends has_bracket L :=
(add_lie : ∀ (x y z : L), ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆)
(lie_add : ∀ (x y z : L), ⁅z, x + y⁆ = ⁅z, x⁆ + ⁅z, y⁆)
(lie_self : ∀ (x : L), ⁅x, x⁆ = 0)
(jacobi : ∀ (x y z : L), ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0)
end prio

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

section prio
set_option default_priority 100 -- see Note [default priority]
/--
A Lie algebra is a module with compatible product, known as the bracket, satisfying the Jacobi
identity. Forgetting the scalar multiplication, every Lie algebra is a Lie ring.
-/
class lie_algebra (R : Type u) (L : Type v)
  [comm_ring R] [add_comm_group L] extends module R L, lie_ring L :=
(lie_smul : ∀ (t : R) (x y : L), ⁅x, t • y⁆ = t • ⁅x, y⁆)
end prio

@[simp] lemma lie_smul  (R : Type u) (L : Type v) [comm_ring R] [add_comm_group L] [lie_algebra R L]
  (t : R) (x y : L) : ⁅x, t • y⁆ = t • ⁅x, y⁆ :=
  lie_algebra.lie_smul t x y

@[simp] lemma smul_lie (R : Type u) (L : Type v) [comm_ring R] [add_comm_group L] [lie_algebra R L]
  (t : R) (x y : L) : ⁅t • x, y⁆ = t • ⁅x, y⁆ :=
  by { rw [←lie_skew, ←lie_skew x y], simp [-lie_skew], }

namespace lie_algebra

/--
A morphism of Lie algebras is a linear map respecting the bracket operations.
-/
structure morphism (R : Type u) (L : Type v) (L' : Type v)
  [comm_ring R] [add_comm_group L] [lie_algebra R L] [add_comm_group L'] [lie_algebra R L']
  extends linear_map R L L' :=
(bracket : ∀ {x y : L}, to_fun ⁅x, y⁆ = ⁅to_fun x, to_fun y⁆)

infixr ` →ₗ⁅⁆ `:25 := morphism _
notation L ` →ₗ⁅`:25 R:25 `⁆ `:0 L':0 := morphism R L L'

instance (R : Type u) (L : Type v) (L' : Type v)
  [comm_ring R] [add_comm_group L] [lie_algebra R L] [add_comm_group L'] [lie_algebra R L'] :
  has_coe_to_fun (L →ₗ⁅R⁆ L') := ⟨_, linear_map.to_fun ∘ morphism.to_linear_map⟩

variables {R : Type u} {L : Type v} [comm_ring R] [add_comm_group L] [lie_algebra R L]

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
instance of_endomorphism_algebra (M : Type v)
  [add_comm_group M] [module R M] : lie_algebra R (module.End R M) :=
of_associative_algebra (module.End R M)

/--
The adjoint action of a Lie algebra on itself.
-/
def Ad (x : L) : L →ₗ[R] L :=
{ to_fun := has_bracket.bracket x,
  add    := by { intros, apply lie_add },
  smul   := by { intros, apply lie_smul } }

set_option class.instance_max_depth 35
lemma is_morphism_Ad (x y : L) : (Ad ⁅x, y⁆ : L →ₗ[R] L) = ⁅Ad x, Ad y⁆ :=
begin
  ext z,
  suffices : ⁅⁅x, y⁆, z⁆ = ⁅x, ⁅y, z⁆⁆ + ⁅⁅x, z⁆, y⁆, by {
    dunfold of_endomorphism_algebra of_associative_algebra Ad
            has_bracket.bracket ring_commutator.commutator,
    simpa using this,
  },
  rw [eq_comm, ←lie_skew ⁅x, y⁆ z, ←lie_skew ⁅x, z⁆ y, ←lie_skew x z, lie_neg, neg_neg,
      ←sub_eq_zero_iff_eq, sub_neg_eq_add, lie_ring.jacobi],
end

/--
The bracket of a Lie algebra as a bilinear map.
-/
def bil_lie : L →ₗ[R] L →ₗ[R] L :=
{ to_fun := Ad,
  add    := by { unfold Ad, intros, ext, simp [add_lie], },
  smul   := by { unfold Ad, intros, ext, simp, } }

/--
The bracket of a Lie algebra as a morphism of Lie algebras.
-/
def bil_lie_morphism : L →ₗ⁅R⁆ module.End R L := { bracket := is_morphism_Ad, ..bil_lie }

end lie_algebra

section lie_subalgebra

variables (R : Type u) (L : Type v) [comm_ring R] [add_comm_group L] [lie_algebra R L]

/--
A Lie subalgebra of a Lie algebra is submodule that is closed under the Lie bracket.
This is a sufficient condition for the subset itself to form a Lie algebra.
-/
structure lie_subalgebra extends submodule R L :=
(bracket : ∀ {x y}, x ∈ carrier → y ∈ carrier → ⁅x, y⁆ ∈ carrier)

instance lie_subalgebra_coe_submodule : has_coe (lie_subalgebra R L) (submodule R L) :=
⟨lie_subalgebra.to_submodule⟩

instance lie_subalgebra_lie_algebra [L' : lie_subalgebra R L] : lie_algebra R L' := {
  bracket  := λ x y, ⟨⁅x.val, y.val⁆, L'.bracket x.property y.property⟩,
  lie_add  := by { intros, apply set_coe.ext, apply lie_add, },
  add_lie  := by { intros, apply set_coe.ext, apply add_lie, },
  lie_self := by { intros, apply set_coe.ext, apply lie_self, },
  jacobi   := by { intros, apply set_coe.ext, apply lie_ring.jacobi, },
  lie_smul := by { intros, apply set_coe.ext, apply lie_smul, } }

end lie_subalgebra

section lie_module

variables (R : Type u) (L : Type v) [comm_ring R] [add_comm_group L] [lie_algebra R L]
variables (M  : Type v) [add_comm_group M] [module R M]

section prio
set_option default_priority 100 -- see Note [default priority]
/--
A Lie module is a module over a commutative ring, together with a linear action of a Lie algebra
on this module, such that the Lie bracket acts as the commutator of endomorphisms.
-/
class lie_module := (action : L →ₗ⁅R⁆ module.End R M)
end prio

/--
Every Lie algebra is a module over itself.
-/
instance lie_algebra_self_module : lie_module R L L := ⟨lie_algebra.bil_lie_morphism⟩

/--
A Lie submodule of a Lie module is a submodule that is closed under the Lie bracket.
This is a sufficient condition for the subset itself to form a Lie module.
-/
structure lie_submodule [lie_module R L M] extends submodule R M :=
(bracket : ∀ {x m}, m ∈ carrier → lie_module.action R L M x m ∈ carrier)

instance lie_submodule_coe_submodule [lie_module R L M] :
  has_coe (lie_submodule R L M) (submodule R M) := ⟨lie_submodule.to_submodule⟩

instance lie_submodule_has_mem [lie_module R L M] :
  has_mem M (lie_submodule R L M) := ⟨λ x M', x ∈ (M' : set M)⟩

instance lie_submodule_lie_module [α : lie_module R L M] [M' : lie_submodule R L M] :
  lie_module R L M' := ⟨{
  add     := by { intros, ext, apply set_coe.ext,
                  rw [linear_map.coe_mk, subtype.coe_mk, linear_map.add], refl, },
  smul    := by { intros, ext, apply set_coe.ext,
                  rw [linear_map.coe_mk, subtype.coe_mk, linear_map.smul], refl, },
  bracket := by { intros, ext, apply set_coe.ext,
                  rw [linear_map.coe_mk, subtype.coe_mk, lie_algebra.morphism.bracket], refl, },
  to_fun  := λ x, {
    to_fun := λ m, ⟨α.action.to_fun x m, M'.bracket m.property⟩,
    add    := by { intros, apply set_coe.ext, simp, },
    smul   := by { intros, apply set_coe.ext, simp, }}}⟩

/--
An ideal of a Lie algebra is a Lie submodule of the Lie algebra as a Lie module over itself.
-/
abbreviation lie_ideal := lie_submodule R L L

lemma lie_mem_right (I : lie_ideal R L) (x y : L) (h : y ∈ I) : ⁅x, y⁆ ∈ I := I.bracket h

lemma lie_bracket_mem_left (I : lie_ideal R L) (x y : L) (h : x ∈ I) : ⁅x, y⁆ ∈ I := by {
  rw [←lie_skew, ←neg_lie], apply lie_mem_right, assumption, }

end lie_module

namespace lie_quotient

variables {R : Type u} {L : Type v} [comm_ring R] [add_comm_group L] [lie_algebra R L]

/--
The quotient of a Lie algebra by a Lie ideal. It is a Lie algebra.
-/
abbreviation quotient (I : lie_ideal R L) := submodule.quotient I.to_submodule

/--
Map sending an element of `L` to the corresponding element of `L/I`, when `I` is a lie_ideal of `L`.
-/
abbreviation mk {I : lie_ideal R L} : L → I.to_submodule.quotient := submodule.quotient.mk

lemma is_quotient_mk {I : lie_ideal R L} (x : L) :
  quotient.mk' x = (mk x : quotient I) := by { intros, refl, }

instance lie_quotient_has_bracket (I : lie_ideal R L) : has_bracket (quotient I) := ⟨by {
  intros x y,
  apply quotient.lift_on₂' x y (λ x' y', mk ⁅x', y'⁆),
  intros x₁ x₂ y₁ y₂ h₁ h₂,
  apply (submodule.quotient.eq I.to_submodule).2,
  have h : ⁅x₁, x₂⁆ - ⁅y₁, y₂⁆ = ⁅x₁, x₂ - y₂⁆ + ⁅x₁ - y₁, y₂⁆ := by { simp [-lie_skew], },
  rw h,
  apply submodule.add_mem,
  { apply lie_bracket_mem_right R L I x₁ (x₂ - y₂) h₂, },
  { apply lie_bracket_mem_left R L I (x₁ - y₁) y₂ h₁, }, }⟩

@[simp] theorem mk_bracket (I : lie_ideal R L) (x y : L) :
  (mk ⁅x, y⁆ : quotient I) = ⁅mk x, mk y⁆ := rfl

instance lie_quotient_lie_algebra (I : lie_ideal R L) : lie_algebra R (quotient I) := {
  add_lie  := by { intros x' y' z', apply quotient.induction_on₃' x' y' z', intros x y z,
                   repeat { rw is_quotient_mk <|>
                            rw ←mk_bracket <|>
                            rw ←submodule.quotient.mk_add, },
                   apply congr_arg, apply add_lie, },
  lie_add  := by { intros x' y' z', apply quotient.induction_on₃' x' y' z', intros x y z,
                   repeat { rw is_quotient_mk <|>
                            rw ←mk_bracket <|>
                            rw ←submodule.quotient.mk_add, },
                   apply congr_arg, apply lie_add, },
  lie_self := by { intros x', apply quotient.induction_on' x', intros x,
                   rw [is_quotient_mk, ←mk_bracket],
                   apply congr_arg, apply lie_self, },
  jacobi   := by { intros x' y' z', apply quotient.induction_on₃' x' y' z', intros x y z,
                   repeat { rw is_quotient_mk <|>
                            rw ←mk_bracket <|>
                            rw ←submodule.quotient.mk_add, },
                   apply congr_arg, apply lie_ring.jacobi, },
  lie_smul := by { intros t x' y', apply quotient.induction_on₂' x' y', intros x y,
                   repeat { rw is_quotient_mk <|>
                            rw ←mk_bracket <|>
                            rw ←submodule.quotient.mk_smul, },
                   apply congr_arg, apply lie_smul, } }

end lie_quotient

/--
An important class of Lie algebras are those arising from the associative algebra structure on
square matrices over a commutative ring.
-/
def matrix.lie_algebra (n : Type u) (R : Type v)
  [fintype n] [decidable_eq n] [comm_ring R] : lie_algebra R (matrix n n R) :=
lie_algebra.of_associative_algebra (matrix n n R)

#lint
