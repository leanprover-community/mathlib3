/-
Copyright (c) 2019 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import ring_theory.algebra
import linear_algebra.linear_action
import linear_algebra.bilinear_form
import tactic.noncomm_ring

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

universes u v w w₁

/--
A binary operation, intended use in Lie algebras and similar structures.
-/
class has_bracket (L : Type v) := (bracket : L → L → L)

notation `⁅`x`,` y`⁆` := has_bracket.bracket x y

/-- An Abelian Lie algebra is one in which all brackets vanish. Arguably this class belongs in the
`has_bracket` namespace but it seems much more user-friendly to compromise slightly and put it in
the `lie_algebra` namespace. -/
class lie_algebra.is_abelian (L : Type v) [has_bracket L] [has_zero L] : Prop :=
(abelian : ∀ (x y : L), ⁅x, y⁆ = 0)

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
by simp [commutator, right_distrib, left_distrib, sub_eq_add_neg, add_comm, add_left_comm]

@[simp] lemma add_right (x y z : A) :
  ⁅z, x + y⁆ = ⁅z, x⁆ + ⁅z, y⁆ :=
by simp [commutator, right_distrib, left_distrib, sub_eq_add_neg, add_comm, add_left_comm]

@[simp] lemma alternate (x : A) :
  ⁅x, x⁆ = 0 :=
by simp [commutator]

lemma jacobi (x y z : A) :
  ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 :=
by { unfold commutator, noncomm_ring, }

end ring_commutator

section prio
set_option default_priority 100 -- see Note [default priority]
/--
A Lie ring is an additive group with compatible product, known as the bracket, satisfying the
Jacobi identity. The bracket is not associative unless it is identically zero.
-/
@[protect_proj] class lie_ring (L : Type v) extends add_comm_group L, has_bracket L :=
(add_lie : ∀ (x y z : L), ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆)
(lie_add : ∀ (x y z : L), ⁅z, x + y⁆ = ⁅z, x⁆ + ⁅z, y⁆)
(lie_self : ∀ (x : L), ⁅x, x⁆ = 0)
(jacobi : ∀ (x y z : L), ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0)
end prio

section lie_ring

variables {L : Type v} [lie_ring L]

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
add_monoid_hom.map_gsmul ⟨λ x, ⁅x, y⁆, zero_lie y, λ _ _, add_lie _ _ _⟩ _ _

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

local attribute [instance] lie_ring.of_associative_ring

lemma lie_ring.of_associative_ring_bracket (A : Type v) [ring A] (x y : A) :
  ⁅x, y⁆ = x*y - y*x := rfl

lemma commutative_ring_iff_abelian_lie_ring (A : Type v) [ring A] :
  is_commutative A (*) ↔ lie_algebra.is_abelian A :=
begin
  have h₁ : is_commutative A (*) ↔ ∀ (a b : A), a * b = b * a := ⟨λ h, h.1, λ h, ⟨h⟩⟩,
  have h₂ : lie_algebra.is_abelian A ↔ ∀ (a b : A), ⁅a, b⁆ = 0 := ⟨λ h, h.1, λ h, ⟨h⟩⟩,
  simp only [h₁, h₂, lie_ring.of_associative_ring_bracket, sub_eq_zero],
end

end lie_ring

section prio
set_option default_priority 100 -- see Note [default priority]
/--
A Lie algebra is a module with compatible product, known as the bracket, satisfying the Jacobi
identity. Forgetting the scalar multiplication, every Lie algebra is a Lie ring.
-/
class lie_algebra (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] extends semimodule R L :=
(lie_smul : ∀ (t : R) (x y : L), ⁅x, t • y⁆ = t • ⁅x, y⁆)
end prio

@[simp] lemma lie_smul  (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L]
  (t : R) (x y : L) : ⁅x, t • y⁆ = t • ⁅x, y⁆ :=
  lie_algebra.lie_smul t x y

@[simp] lemma smul_lie (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L]
  (t : R) (x y : L) : ⁅t • x, y⁆ = t • ⁅x, y⁆ :=
  by { rw [←lie_skew, ←lie_skew x y], simp [-lie_skew], }

namespace lie_algebra

set_option old_structure_cmd true
/-- A morphism of Lie algebras is a linear map respecting the bracket operations. -/
structure morphism (R : Type u) (L : Type v) (L' : Type w)
  [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L']
  extends linear_map R L L' :=
(map_lie : ∀ {x y : L}, to_fun ⁅x, y⁆ = ⁅to_fun x, to_fun y⁆)

attribute [nolint doc_blame] lie_algebra.morphism.to_linear_map

infixr ` →ₗ⁅⁆ `:25 := morphism _
notation L ` →ₗ⁅`:25 R:25 `⁆ `:0 L':0 := morphism R L L'

section morphism_properties

variables {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}
variables [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_ring L₃]
variables [lie_algebra R L₁] [lie_algebra R L₂] [lie_algebra R L₃]

instance : has_coe (L₁ →ₗ⁅R⁆ L₂) (L₁ →ₗ[R] L₂) := ⟨morphism.to_linear_map⟩

/-- see Note [function coercion] -/
instance : has_coe_to_fun (L₁ →ₗ⁅R⁆ L₂) := ⟨_, morphism.to_fun⟩

@[simp] lemma map_lie (f : L₁ →ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x, f y⁆ := morphism.map_lie f

/-- The constant 0 map is a Lie algebra morphism. -/
instance : has_zero (L₁ →ₗ⁅R⁆ L₂) := ⟨{ map_lie := by simp, ..(0 : L₁ →ₗ[R] L₂)}⟩

/-- The identity map is a Lie algebra morphism. -/
instance : has_one (L₁ →ₗ⁅R⁆ L₁) := ⟨{ map_lie := by simp, ..(1 : L₁ →ₗ[R] L₁)}⟩

instance : inhabited (L₁ →ₗ⁅R⁆ L₂) := ⟨0⟩

/-- The composition of morphisms is a morphism. -/
def morphism.comp (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) : L₁ →ₗ⁅R⁆ L₃ :=
{ map_lie := λ x y, by { change f (g ⁅x, y⁆) = ⁅f (g x), f (g y)⁆, rw [map_lie, map_lie], },
  ..linear_map.comp f.to_linear_map g.to_linear_map }

lemma morphism.comp_apply (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) (x : L₁) :
  f.comp g x = f (g x) := rfl

/-- The inverse of a bijective morphism is a morphism. -/
def morphism.inverse (f : L₁ →ₗ⁅R⁆ L₂) (g : L₂ → L₁)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) : L₂ →ₗ⁅R⁆ L₁ :=
{ map_lie := λ x y, by {
  calc g ⁅x, y⁆ = g ⁅f (g x), f (g y)⁆ : by { conv_lhs { rw [←h₂ x, ←h₂ y], }, }
            ... = g (f ⁅g x, g y⁆) : by rw map_lie
            ... = ⁅g x, g y⁆ : (h₁ _), },
  ..linear_map.inverse f.to_linear_map g h₁ h₂ }

end morphism_properties

/-- An equivalence of Lie algebras is a morphism which is also a linear equivalence. We could
instead define an equivalence to be a morphism which is also a (plain) equivalence. However it is
more convenient to define via linear equivalence to get `.to_linear_equiv` for free. -/
structure equiv (R : Type u) (L : Type v) (L' : Type w)
  [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L']
  extends L →ₗ⁅R⁆ L', L ≃ₗ[R] L'

attribute [nolint doc_blame] lie_algebra.equiv.to_morphism
attribute [nolint doc_blame] lie_algebra.equiv.to_linear_equiv

notation L ` ≃ₗ⁅`:50 R `⁆ ` L' := equiv R L L'

namespace equiv

variables {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}
variables [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_ring L₃]
variables [lie_algebra R L₁] [lie_algebra R L₂] [lie_algebra R L₃]

instance has_coe_to_lie_hom : has_coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ →ₗ⁅R⁆ L₂) := ⟨to_morphism⟩
instance has_coe_to_linear_equiv : has_coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ ≃ₗ[R] L₂) := ⟨to_linear_equiv⟩

/-- see Note [function coercion] -/
instance : has_coe_to_fun (L₁ ≃ₗ⁅R⁆ L₂) := ⟨_, to_fun⟩

@[simp, norm_cast] lemma coe_to_lie_equiv (e : L₁ ≃ₗ⁅R⁆ L₂) : ((e : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) = e :=
  rfl

@[simp, norm_cast] lemma coe_to_linear_equiv (e : L₁ ≃ₗ⁅R⁆ L₂) : ((e : L₁ ≃ₗ[R] L₂) : L₁ → L₂) = e :=
  rfl

instance : has_one (L₁ ≃ₗ⁅R⁆ L₁) :=
⟨{ map_lie := λ x y, by { change ((1 : L₁→ₗ[R] L₁) ⁅x, y⁆) = ⁅(1 : L₁→ₗ[R] L₁) x, (1 : L₁→ₗ[R] L₁) y⁆, simp, },
  ..(1 : L₁ ≃ₗ[R] L₁)}⟩

@[simp] lemma one_apply (x : L₁) : (1 : (L₁ ≃ₗ⁅R⁆ L₁)) x = x := rfl

instance : inhabited (L₁ ≃ₗ⁅R⁆ L₁) := ⟨1⟩

/-- Lie algebra equivalences are reflexive. -/
@[refl]
def refl : L₁ ≃ₗ⁅R⁆ L₁ := 1

@[simp] lemma refl_apply (x : L₁) : (refl : L₁ ≃ₗ⁅R⁆ L₁) x = x := rfl

/-- Lie algebra equivalences are symmetric. -/
@[symm]
def symm (e : L₁ ≃ₗ⁅R⁆ L₂) : L₂ ≃ₗ⁅R⁆ L₁ :=
{ ..morphism.inverse e.to_morphism e.inv_fun e.left_inv e.right_inv,
  ..e.to_linear_equiv.symm }

@[simp] lemma symm_symm (e : L₁ ≃ₗ⁅R⁆ L₂) : e.symm.symm = e :=
by { cases e, refl, }

@[simp] lemma apply_symm_apply (e : L₁ ≃ₗ⁅R⁆ L₂) : ∀ x, e (e.symm x) = x :=
  e.to_linear_equiv.apply_symm_apply

@[simp] lemma symm_apply_apply (e : L₁ ≃ₗ⁅R⁆ L₂) : ∀ x, e.symm (e x) = x :=
  e.to_linear_equiv.symm_apply_apply

/-- Lie algebra equivalences are transitive. -/
@[trans]
def trans (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) : L₁ ≃ₗ⁅R⁆ L₃ :=
{ ..morphism.comp e₂.to_morphism e₁.to_morphism,
  ..linear_equiv.trans e₁.to_linear_equiv e₂.to_linear_equiv }

@[simp] lemma trans_apply (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) (x : L₁) :
  (e₁.trans e₂) x = e₂ (e₁ x) := rfl

@[simp] lemma symm_trans_apply (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) (x : L₃) :
  (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) := rfl

end equiv

namespace direct_sum
open dfinsupp

variables {R : Type u} [comm_ring R]
variables {ι : Type v} [decidable_eq ι] {L : ι → Type w}
variables [Π i, lie_ring (L i)] [Π i, lie_algebra R (L i)]

/-- The direct sum of Lie rings carries a natural Lie ring structure. -/
instance : lie_ring (direct_sum ι L) := {
  bracket  := zip_with (λ i, λ x y, ⁅x, y⁆) (λ i, lie_zero 0),
  add_lie  := λ x y z, by { ext, simp only [zip_with_apply, add_apply, add_lie], },
  lie_add  := λ x y z, by { ext, simp only [zip_with_apply, add_apply, lie_add], },
  lie_self := λ x, by { ext, simp only [zip_with_apply, add_apply, lie_self, zero_apply], },
  jacobi   := λ x y z, by { ext, simp only [zip_with_apply, add_apply, lie_ring.jacobi, zero_apply], },
  ..(infer_instance : add_comm_group _) }

@[simp] lemma bracket_apply {x y : direct_sum ι L} {i : ι} :
  ⁅x, y⁆ i = ⁅x i, y i⁆ := zip_with_apply

/-- The direct sum of Lie algebras carries a natural Lie algebra structure. -/
instance : lie_algebra R (direct_sum ι L) :=
{ lie_smul := λ c x y, by { ext, simp only [zip_with_apply, smul_apply, bracket_apply, lie_smul], },
  ..(infer_instance : module R _) }

end direct_sum

variables {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L]

/--
An associative algebra gives rise to a Lie algebra by taking the bracket to be the ring commutator.
-/
def of_associative_algebra (A : Type v) [ring A] [algebra R A] :
  @lie_algebra R A _ (lie_ring.of_associative_ring _) :=
{ lie_smul := λ t x y,
    by rw [lie_ring.of_associative_ring_bracket, lie_ring.of_associative_ring_bracket,
           algebra.mul_smul_comm, algebra.smul_mul_assoc, smul_sub], }

instance (M : Type v) [add_comm_group M] [module R M] : lie_ring (module.End R M) :=
lie_ring.of_associative_ring _

local attribute [instance] lie_ring.of_associative_ring
local attribute [instance] lie_algebra.of_associative_algebra

/-- The map `of_associative_algebra` associating a Lie algebra to an associative algebra is
functorial. -/
def of_associative_algebra_hom {R : Type u} {A : Type v} {B : Type w}
  [comm_ring R] [ring A] [ring B] [algebra R A] [algebra R B] (f : A →ₐ[R] B) : A →ₗ⁅R⁆ B :=
 { map_lie := λ x y, show f ⁅x,y⁆ = ⁅f x,f y⁆,
     by simp only [lie_ring.of_associative_ring_bracket, alg_hom.map_sub, alg_hom.map_mul],
  ..f.to_linear_map, }

@[simp] lemma of_associative_algebra_hom_id {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A] :
  of_associative_algebra_hom (alg_hom.id R A) = 1 := rfl

@[simp] lemma of_associative_algebra_hom_comp {R : Type u} {A : Type v} {B : Type w} {C : Type w₁}
  [comm_ring R] [ring A] [ring B] [ring C] [algebra R A] [algebra R B] [algebra R C]
  (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
  of_associative_algebra_hom (g.comp f) = (of_associative_algebra_hom g).comp (of_associative_algebra_hom f) := rfl

/--
An important class of Lie algebras are those arising from the associative algebra structure on
module endomorphisms.
-/
instance of_endomorphism_algebra (M : Type v) [add_comm_group M] [module R M] :
  lie_algebra R (module.End R M) :=
of_associative_algebra (module.End R M)

lemma endo_algebra_bracket (M : Type v) [add_comm_group M] [module R M] (f g : module.End R M) :
  ⁅f, g⁆ = f.comp g - g.comp f := rfl

/--
The adjoint action of a Lie algebra on itself.
-/
def Ad : L →ₗ⁅R⁆ module.End R L :=
{ to_fun    := λ x,
  { to_fun    := has_bracket.bracket x,
    map_add'  := by { intros, apply lie_add, },
    map_smul' := by { intros, apply lie_smul, } },
  map_add'  := by { intros, ext, simp, },
  map_smul' := by { intros, ext, simp, },
  map_lie   := by {
    intros x y, ext z,
    rw endo_algebra_bracket,
    suffices : ⁅⁅x, y⁆, z⁆ = ⁅x, ⁅y, z⁆⁆ + ⁅⁅x, z⁆, y⁆, by simpa [sub_eq_add_neg],
    rw [eq_comm, ←lie_skew ⁅x, y⁆ z, ←lie_skew ⁅x, z⁆ y, ←lie_skew x z, lie_neg, neg_neg,
        ←sub_eq_zero_iff_eq, sub_neg_eq_add, lie_ring.jacobi], } }

end lie_algebra

section lie_subalgebra

variables (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L]

set_option old_structure_cmd true
/--
A Lie subalgebra of a Lie algebra is submodule that is closed under the Lie bracket.
This is a sufficient condition for the subset itself to form a Lie algebra.
-/
structure lie_subalgebra extends submodule R L :=
(lie_mem : ∀ {x y}, x ∈ carrier → y ∈ carrier → ⁅x, y⁆ ∈ carrier)

attribute [nolint doc_blame] lie_subalgebra.to_submodule

/-- The zero algebra is a subalgebra of any Lie algebra. -/
instance : has_zero (lie_subalgebra R L) :=
⟨{ lie_mem := λ x y hx hy, by { rw [((submodule.mem_bot R).1 hx), zero_lie],
                                exact submodule.zero_mem (0 : submodule R L), },
   ..(0 : submodule R L) }⟩

instance : inhabited (lie_subalgebra R L) := ⟨0⟩
instance : has_coe (lie_subalgebra R L) (set L) := ⟨lie_subalgebra.carrier⟩
instance : has_mem L (lie_subalgebra R L) := ⟨λ x L', x ∈ (L' : set L)⟩

instance lie_subalgebra_coe_submodule : has_coe (lie_subalgebra R L) (submodule R L) :=
⟨lie_subalgebra.to_submodule⟩

/-- A Lie subalgebra forms a new Lie ring. -/
instance lie_subalgebra_lie_ring (L' : lie_subalgebra R L) : lie_ring L' := {
  bracket  := λ x y, ⟨⁅x.val, y.val⁆, L'.lie_mem x.property y.property⟩,
  lie_add  := by { intros, apply set_coe.ext, apply lie_add, },
  add_lie  := by { intros, apply set_coe.ext, apply add_lie, },
  lie_self := by { intros, apply set_coe.ext, apply lie_self, },
  jacobi   := by { intros, apply set_coe.ext, apply lie_ring.jacobi, } }

/-- A Lie subalgebra forms a new Lie algebra. -/
instance lie_subalgebra_lie_algebra (L' : lie_subalgebra R L) :
    @lie_algebra R L' _ (lie_subalgebra_lie_ring _ _ _) :=
{ lie_smul := by { intros, apply set_coe.ext, apply lie_smul } }

@[simp] lemma lie_subalgebra.mem_coe {L' : lie_subalgebra R L} {x : L} :
  x ∈ (L' : set L) ↔ x ∈ L' := iff.rfl

@[simp] lemma lie_subalgebra.mem_coe' {L' : lie_subalgebra R L} {x : L} :
  x ∈ (L' : submodule R L) ↔ x ∈ L' := iff.rfl

@[simp, norm_cast] lemma lie_subalgebra.coe_bracket (L' : lie_subalgebra R L) (x y : L') :
  (↑⁅x, y⁆ : L) = ⁅↑x, ↑y⁆ := rfl

@[ext] lemma lie_subalgebra.ext (L₁' L₂' : lie_subalgebra R L) (h : ∀ x, x ∈ L₁' ↔ x ∈ L₂') :
  L₁' = L₂' :=
by { cases L₁', cases L₂', simp only [], ext x, exact h x, }

lemma lie_subalgebra.ext_iff (L₁' L₂' : lie_subalgebra R L) : L₁' = L₂' ↔ ∀ x, x ∈ L₁' ↔ x ∈ L₂' :=
⟨λ h x, by rw h, lie_subalgebra.ext R L L₁' L₂'⟩

local attribute [instance] lie_ring.of_associative_ring
local attribute [instance] lie_algebra.of_associative_algebra

/-- A subalgebra of an associative algebra is a Lie subalgebra of the associated Lie algebra. -/
def lie_subalgebra_of_subalgebra (A : Type v) [ring A] [algebra R A]
  (A' : subalgebra R A) : lie_subalgebra R A :=
{ lie_mem := λ x y hx hy, by {
    change ⁅x, y⁆ ∈ A', change x ∈ A' at hx, change y ∈ A' at hy,
    rw lie_ring.of_associative_ring_bracket,
    have hxy := subalgebra.mul_mem A' x y hx hy,
    have hyx := subalgebra.mul_mem A' y x hy hx,
    exact submodule.sub_mem A'.to_submodule hxy hyx, },
  ..A'.to_submodule }

variables {R L} {L₂ : Type w} [lie_ring L₂] [lie_algebra R L₂]

/-- The embedding of a Lie subalgebra into the ambient space as a Lie morphism. -/
def lie_subalgebra.incl (L' : lie_subalgebra R L) : L' →ₗ⁅R⁆ L :=
{ map_lie := λ x y, by { rw [linear_map.to_fun_eq_coe, submodule.subtype_apply], refl, },
  ..L'.to_submodule.subtype }

/-- The range of a morphism of Lie algebras is a Lie subalgebra. -/
def lie_algebra.morphism.range (f : L →ₗ⁅R⁆ L₂) : lie_subalgebra R L₂ :=
{ lie_mem := λ x y,
    show x ∈ f.to_linear_map.range → y ∈ f.to_linear_map.range → ⁅x, y⁆ ∈ f.to_linear_map.range,
    by { repeat { rw linear_map.mem_range }, rintros ⟨x', hx⟩ ⟨y', hy⟩, refine ⟨⁅x', y'⁆, _⟩,
         rw [←hx, ←hy], change f ⁅x', y'⁆ = ⁅f x', f y'⁆, rw lie_algebra.map_lie, },
  ..f.to_linear_map.range }

@[simp] lemma lie_algebra.morphism.range_bracket (f : L →ₗ⁅R⁆ L₂) (x y : f.range) :
  (↑⁅x, y⁆ : L₂) = ⁅↑x, ↑y⁆ := rfl

/-- The image of a Lie subalgebra under a Lie algebra morphism is a Lie subalgebra of the
codomain. -/
def lie_subalgebra.map (f : L →ₗ⁅R⁆ L₂) (L' : lie_subalgebra R L) : lie_subalgebra R L₂ :=
{ lie_mem := λ x y hx hy, by {
    erw submodule.mem_map at hx, rcases hx with ⟨x', hx', hx⟩, rw ←hx,
    erw submodule.mem_map at hy, rcases hy with ⟨y', hy', hy⟩, rw ←hy,
    erw submodule.mem_map,
    exact ⟨⁅x', y'⁆, L'.lie_mem hx' hy', lie_algebra.map_lie f x' y'⟩, },
..((L' : submodule R L).map (f : L →ₗ[R] L₂))}

@[simp] lemma lie_subalgebra.mem_map_submodule (e : L ≃ₗ⁅R⁆ L₂) (L' : lie_subalgebra R L) (x : L₂) :
  x ∈ L'.map (e : L →ₗ⁅R⁆ L₂) ↔ x ∈ (L' : submodule R L).map (e : L →ₗ[R] L₂) :=
by refl

end lie_subalgebra

namespace lie_algebra

variables {R : Type u} {L₁ : Type v} {L₂ : Type w}
variables [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂]

namespace equiv

/-- An injective Lie algebra morphism is an equivalence onto its range. -/
noncomputable def of_injective (f : L₁ →ₗ⁅R⁆ L₂) (h : function.injective f) :
  L₁ ≃ₗ⁅R⁆ f.range :=
have h' : (f : L₁ →ₗ[R] L₂).ker = ⊥ := linear_map.ker_eq_bot_of_injective h,
{ map_lie := λ x y, by { apply set_coe.ext,
    simp only [linear_equiv.of_injective_apply, lie_algebra.morphism.range_bracket],
    apply f.map_lie, },
..(linear_equiv.of_injective ↑f h')}

@[simp] lemma of_injective_apply (f : L₁ →ₗ⁅R⁆ L₂) (h : function.injective f) (x : L₁) :
  ↑(of_injective f h x) = f x := rfl

variables (L₁' L₁'' : lie_subalgebra R L₁) (L₂' : lie_subalgebra R L₂)

/-- Lie subalgebras that are equal as sets are equivalent as Lie algebras. -/
def of_eq (h : (L₁' : set L₁) = L₁'') : L₁' ≃ₗ⁅R⁆ L₁'' :=
{ map_lie := λ x y, by { apply set_coe.ext, simp, },
  ..(linear_equiv.of_eq ↑L₁' ↑L₁''
      (by {ext x, change x ∈ (L₁' : set L₁) ↔ x ∈ (L₁'' : set L₁), rw h, } )) }

@[simp] lemma of_eq_apply (L L' : lie_subalgebra R L₁) (h : (L : set L₁) = L') (x : L) :
  (↑(of_eq L L' h x) : L₁) = x := rfl

variables (e : L₁ ≃ₗ⁅R⁆ L₂)

/-- An equivalence of Lie algebras restricts to an equivalence from any Lie subalgebra onto its
image. -/
def of_subalgebra : L₁'' ≃ₗ⁅R⁆ (L₁''.map e : lie_subalgebra R L₂) :=
{ map_lie := λ x y, by { apply set_coe.ext, exact lie_algebra.map_lie (↑e : L₁ →ₗ⁅R⁆ L₂) ↑x ↑y, }
  ..(linear_equiv.of_submodule (e : L₁ ≃ₗ[R] L₂) ↑L₁'') }

@[simp] lemma of_subalgebra_apply (x : L₁'') : ↑(e.of_subalgebra _  x) = e x := rfl

/-- An equivalence of Lie algebras restricts to an equivalence from any Lie subalgebra onto its
image. -/
def of_subalgebras (h : L₁'.map ↑e = L₂') : L₁' ≃ₗ⁅R⁆ L₂' :=
{ map_lie := λ x y, by { apply set_coe.ext, exact lie_algebra.map_lie (↑e : L₁ →ₗ⁅R⁆ L₂) ↑x ↑y, },
  ..(linear_equiv.of_submodules (e : L₁ ≃ₗ[R] L₂) ↑L₁' ↑L₂' (by { rw ←h, refl, })) }

@[simp] lemma of_subalgebras_apply (h : L₁'.map ↑e = L₂') (x : L₁') :
  ↑(e.of_subalgebras _ _ h x) = e x := rfl

@[simp] lemma of_subalgebras_symm_apply (h : L₁'.map ↑e = L₂') (x : L₂') :
  ↑((e.of_subalgebras _ _ h).symm x) = e.symm x := rfl

end equiv

end lie_algebra

section lie_module

variables (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L]
variables (M  : Type v) [add_comm_group M] [module R M]

section prio
set_option default_priority 100 -- see Note [default priority]
/--
A Lie module is a module over a commutative ring, together with a linear action of a Lie algebra
on this module, such that the Lie bracket acts as the commutator of endomorphisms.
-/
class lie_module extends linear_action R L M :=
(lie_act : ∀ (l l' : L) (m : M), act ⁅l, l'⁆ m = act l (act l' m) - act l' (act l m))
end prio

@[simp] lemma lie_act [lie_module R L M]
  (l l' : L) (m : M) : linear_action.act R ⁅l, l'⁆ m =
                       linear_action.act R l (linear_action.act R l' m) -
                       linear_action.act R l' (linear_action.act R l m) :=
  lie_module.lie_act l l' m

protected lemma of_endo_map_action (α : L →ₗ⁅R⁆ module.End R M) (x : L) (m : M) :
  @linear_action.act R _ _ _ _ _ _ _ (linear_action.of_endo_map R L M α) x m = α x m := rfl

/--
A Lie morphism from a Lie algebra to the endomorphism algebra of a module yields
a Lie module structure.
-/
def lie_module.of_endo_morphism (α : L →ₗ⁅R⁆ module.End R M) : lie_module R L M := {
  lie_act := by { intros x y m, rw [of_endo_map_action, lie_algebra.map_lie,
                                    lie_algebra.endo_algebra_bracket], refl, },
  ..(linear_action.of_endo_map R L M α) }

/--
Every Lie algebra is a module over itself.
-/
instance lie_algebra_self_module : lie_module R L L :=
  lie_module.of_endo_morphism R L L lie_algebra.Ad

/--
A Lie submodule of a Lie module is a submodule that is closed under the Lie bracket.
This is a sufficient condition for the subset itself to form a Lie module.
-/
structure lie_submodule [lie_module R L M] extends submodule R M :=
(lie_mem : ∀ {x : L} {m : M}, m ∈ carrier → linear_action.act R x m ∈ carrier)

/-- The zero module is a Lie submodule of any Lie module. -/
instance [lie_module R L M] : has_zero (lie_submodule R L M) :=
⟨{ lie_mem := λ x m h, by { rw [((submodule.mem_bot R).1 h), linear_action_zero],
                            exact submodule.zero_mem (0 : submodule R M), },
   ..(0 : submodule R M)}⟩

instance [lie_module R L M] : inhabited (lie_submodule R L M) := ⟨0⟩

instance lie_submodule_coe_submodule [lie_module R L M] :
  has_coe (lie_submodule R L M) (submodule R M) := ⟨lie_submodule.to_submodule⟩

instance lie_submodule_has_mem [lie_module R L M] :
  has_mem M (lie_submodule R L M) := ⟨λ x N, x ∈ (N : set M)⟩

instance lie_submodule_lie_module [lie_module R L M] (N : lie_submodule R L M) :
  lie_module R L N := {
  act      := λ x m, ⟨linear_action.act R x m.val, N.lie_mem m.property⟩,
  add_act  := by { intros x y m, apply set_coe.ext, apply linear_action.add_act, },
  act_add  := by { intros x m n, apply set_coe.ext, apply linear_action.act_add, },
  act_smul := by { intros r x y, apply set_coe.ext, apply linear_action.act_smul, },
  smul_act := by { intros r x y, apply set_coe.ext, apply linear_action.smul_act, },
  lie_act  := by { intros x y m, apply set_coe.ext, apply lie_module.lie_act, } }

/--
An ideal of a Lie algebra is a Lie submodule of the Lie algebra as a Lie module over itself.
-/
abbreviation lie_ideal := lie_submodule R L L

lemma lie_mem_right (I : lie_ideal R L) (x y : L) (h : y ∈ I) : ⁅x, y⁆ ∈ I := I.lie_mem h

lemma lie_mem_left (I : lie_ideal R L) (x y : L) (h : x ∈ I) : ⁅x, y⁆ ∈ I := by {
  rw [←lie_skew, ←neg_lie], apply lie_mem_right, assumption, }

/--
An ideal of a Lie algebra is a Lie subalgebra.
-/
def lie_ideal_subalgebra (I : lie_ideal R L) : lie_subalgebra R L := {
  lie_mem := by { intros x y hx hy, apply lie_mem_right, exact hy, },
  ..I.to_submodule, }

/-- A Lie module is irreducible if its only non-trivial Lie submodule is itself. -/
class lie_module.is_irreducible [lie_module R L M] : Prop :=
(irreducible : ∀ (M' : lie_submodule R L M), (∃ (m : M'), m ≠ 0) → (∀ (m : M), m ∈ M'))

/-- A Lie algebra is simple if it is irreducible as a Lie module over itself via the adjoint
action, and it is non-Abelian. -/
class lie_algebra.is_simple : Prop :=
(simple : lie_module.is_irreducible R L L ∧ ¬lie_algebra.is_abelian L)

end lie_module

namespace lie_submodule

variables {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L]
variables {M : Type v} [add_comm_group M] [module R M] [α : lie_module R L M]
variables (N : lie_submodule R L M) (I : lie_ideal R L)

/--
The quotient of a Lie module by a Lie submodule. It is a Lie module.
-/
abbreviation quotient := N.to_submodule.quotient

namespace quotient

variables {N I}

/--
Map sending an element of `M` to the corresponding element of `M/N`, when `N` is a lie_submodule of
the lie_module `N`.
-/
abbreviation mk : M → N.quotient := submodule.quotient.mk

lemma is_quotient_mk (m : M) :
  quotient.mk' m = (mk m : N.quotient) := rfl

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there
is a natural linear map from `L` to the endomorphisms of `M` leaving `N` invariant. -/
def lie_submodule_invariant : L →ₗ[R] submodule.compatible_maps N.to_submodule N.to_submodule :=
  linear_map.cod_restrict _ (α.to_linear_action.to_endo_map _ _ _) N.lie_mem

instance lie_quotient_action : linear_action R L N.quotient :=
  linear_action.of_endo_map _ _ _ (linear_map.comp (submodule.mapq_linear N N) lie_submodule_invariant)

lemma lie_quotient_action_apply (z : L) (m : M) :
  linear_action.act R z (mk m : N.quotient) = mk (linear_action.act R z m) := rfl

/-- The quotient of a Lie module by a Lie submodule, is a Lie module. -/
instance lie_quotient_lie_module : lie_module R L N.quotient :=
{ lie_act := λ x y m', by { apply quotient.induction_on' m', intros m, rw is_quotient_mk,
                            repeat { rw lie_quotient_action_apply, }, rw lie_act, refl, },
  ..quotient.lie_quotient_action, }

instance lie_quotient_has_bracket : has_bracket (quotient I) := ⟨by {
  intros x y,
  apply quotient.lift_on₂' x y (λ x' y', mk ⁅x', y'⁆),
  intros x₁ x₂ y₁ y₂ h₁ h₂,
  apply (submodule.quotient.eq I.to_submodule).2,
  have h : ⁅x₁, x₂⁆ - ⁅y₁, y₂⁆ = ⁅x₁, x₂ - y₂⁆ + ⁅x₁ - y₁, y₂⁆ := by simp [-lie_skew, sub_eq_add_neg, add_assoc],
  rw h,
  apply submodule.add_mem,
  { apply lie_mem_right R L I x₁ (x₂ - y₂) h₂, },
  { apply lie_mem_left R L I (x₁ - y₁) y₂ h₁, }, }⟩

@[simp] lemma mk_bracket (x y : L) :
  (mk ⁅x, y⁆ : quotient I) = ⁅mk x, mk y⁆ := rfl

instance lie_quotient_lie_ring : lie_ring (quotient I) := {
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
                   apply congr_arg, apply lie_ring.jacobi, } }

instance lie_quotient_lie_algebra : lie_algebra R (quotient I) := {
  lie_smul := by { intros t x' y', apply quotient.induction_on₂' x' y', intros x y,
                   repeat { rw is_quotient_mk <|>
                            rw ←mk_bracket <|>
                            rw ←submodule.quotient.mk_smul, },
                   apply congr_arg, apply lie_smul, } }

end quotient

end lie_submodule

namespace linear_equiv

variables {R : Type u} {M₁ : Type v} {M₂ : Type w}
variables [comm_ring R] [add_comm_group M₁] [module R M₁] [add_comm_group M₂] [module R M₂]
variables (e : M₁ ≃ₗ[R] M₂)

/-- A linear equivalence of two modules induces a Lie algebra equivalence of their endomorphisms. -/
def lie_conj : module.End R M₁ ≃ₗ⁅R⁆ module.End R M₂ :=
{ map_lie := λ f g, show e.conj ⁅f, g⁆ =  ⁅e.conj f, e.conj g⁆,
             by simp only [lie_algebra.endo_algebra_bracket, e.conj_comp, linear_equiv.map_sub],
  ..e.conj }

@[simp] lemma lie_conj_apply (f : module.End R M₁) : e.lie_conj f = e.conj f := rfl

@[simp] lemma lie_conj_symm : e.lie_conj.symm = e.symm.lie_conj := rfl

end linear_equiv

section matrices
open_locale matrix

variables {R : Type u} [comm_ring R]
variables {n : Type w} [fintype n] [decidable_eq n]

/-- An important class of Lie rings are those arising from the associative algebra structure on
square matrices over a commutative ring. -/
def matrix.lie_ring : lie_ring (matrix n n R) :=
lie_ring.of_associative_ring (matrix n n R)

local attribute [instance] matrix.lie_ring

/-- An important class of Lie algebras are those arising from the associative algebra structure on
square matrices over a commutative ring. -/
def matrix.lie_algebra : lie_algebra R (matrix n n R) :=
lie_algebra.of_associative_algebra (matrix n n R)

local attribute [instance] matrix.lie_algebra

/-- The natural equivalence between linear endomorphisms of finite free modules and square matrices
is compatible with the Lie algebra structures. -/
def lie_equiv_matrix' : module.End R (n → R) ≃ₗ⁅R⁆ matrix n n R :=
{ map_lie := λ T S,
  begin
    let f := @linear_map.to_matrixₗ n n _ _ R _ _,
    change f (T.comp S - S.comp T) = (f T) * (f S) - (f S) * (f T),
    have h : ∀ (T S : module.End R _), f (T.comp S) = (f T) ⬝ (f S) := matrix.comp_to_matrix_mul,
    rw [linear_map.map_sub, h, h, matrix.mul_eq_mul, matrix.mul_eq_mul],
  end,
  ..linear_equiv_matrix' }

@[simp] lemma lie_equiv_matrix'_apply (f : module.End R (n → R)) :
  lie_equiv_matrix' f = f.to_matrix := rfl

@[simp] lemma lie_equiv_matrix'_symm_apply (A : matrix n n R) :
  (@lie_equiv_matrix' R _ n _ _).symm A = A.to_lin := rfl

/-- An invertible matrix induces a Lie algebra equivalence from the space of matrices to itself. -/
noncomputable def matrix.lie_conj (P : matrix n n R) (h : is_unit P) :
  matrix n n R ≃ₗ⁅R⁆ matrix n n R :=
((@lie_equiv_matrix' R _ n _ _).symm.trans (P.to_linear_equiv h).lie_conj).trans lie_equiv_matrix'

@[simp] lemma matrix.lie_conj_apply (P A : matrix n n R) (h : is_unit P) :
  P.lie_conj h A = P ⬝ A ⬝ P⁻¹ :=
by simp [linear_equiv.conj_apply, matrix.lie_conj, matrix.comp_to_matrix_mul, to_lin_to_matrix]

@[simp] lemma matrix.lie_conj_symm_apply (P A : matrix n n R) (h : is_unit P) :
  (P.lie_conj h).symm A = P⁻¹ ⬝ A ⬝ P :=
by simp [linear_equiv.symm_conj_apply, matrix.lie_conj, matrix.comp_to_matrix_mul, to_lin_to_matrix]

end matrices

section skew_adjoint_endomorphisms
open bilin_form

variables {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
variables (B : bilin_form R M)

lemma bilin_form.is_skew_adjoint_bracket (f g : module.End R M)
  (hf : f ∈ B.skew_adjoint_submodule) (hg : g ∈ B.skew_adjoint_submodule) :
  ⁅f, g⁆ ∈ B.skew_adjoint_submodule :=
begin
  rw mem_skew_adjoint_submodule at *,
  have hfg : is_adjoint_pair B B (f * g) (g * f), { rw ←neg_mul_neg g f, exact hf.mul hg, },
  have hgf : is_adjoint_pair B B (g * f) (f * g), { rw ←neg_mul_neg f g, exact hg.mul hf, },
  change bilin_form.is_adjoint_pair B B (f * g - g * f) (-(f * g - g * f)), rw neg_sub,
  exact hfg.sub hgf,
end

/-- Given an `R`-module `M`, equipped with a bilinear form, the skew-adjoint endomorphisms form a
Lie subalgebra of the Lie algebra of endomorphisms. -/
def skew_adjoint_lie_subalgebra : lie_subalgebra R (module.End R M) :=
{ lie_mem := B.is_skew_adjoint_bracket, ..B.skew_adjoint_submodule }

variables {N : Type w} [add_comm_group N] [module R N] (e : N ≃ₗ[R] M)

/-- An equivalence of modules with bilinear forms gives equivalence of Lie algebras of skew-adjoint
endomorphisms. -/
def skew_adjoint_lie_subalgebra_equiv :
  skew_adjoint_lie_subalgebra (B.comp (↑e : N →ₗ[R] M) ↑e) ≃ₗ⁅R⁆ skew_adjoint_lie_subalgebra B :=
begin
  apply lie_algebra.equiv.of_subalgebras _ _ e.lie_conj,
  ext f,
  simp only [lie_subalgebra.mem_coe, submodule.mem_map_equiv, lie_subalgebra.mem_map_submodule,
    coe_coe],
  exact (bilin_form.is_pair_self_adjoint_equiv (-B) B e f).symm,
end

@[simp] lemma skew_adjoint_lie_subalgebra_equiv_apply
  (f : skew_adjoint_lie_subalgebra (B.comp ↑e ↑e)) :
  ↑(skew_adjoint_lie_subalgebra_equiv B e f) = e.lie_conj f :=
by simp [skew_adjoint_lie_subalgebra_equiv]

@[simp] lemma skew_adjoint_lie_subalgebra_equiv_symm_apply (f : skew_adjoint_lie_subalgebra B) :
  ↑((skew_adjoint_lie_subalgebra_equiv B e).symm f) = e.symm.lie_conj f :=
by simp [skew_adjoint_lie_subalgebra_equiv]

end skew_adjoint_endomorphisms

section skew_adjoint_matrices
open_locale matrix

variables {R : Type u} {n : Type w} [comm_ring R] [fintype n] [decidable_eq n]
variables (J : matrix n n R)

local attribute [instance] matrix.lie_ring
local attribute [instance] matrix.lie_algebra

lemma matrix.lie_transpose (A B : matrix n n R) : ⁅A, B⁆ᵀ = ⁅Bᵀ, Aᵀ⁆ :=
show (A * B - B * A)ᵀ = (Bᵀ * Aᵀ - Aᵀ * Bᵀ), by simp

lemma matrix.is_skew_adjoint_bracket (A B : matrix n n R)
  (hA : A ∈ skew_adjoint_matrices_submodule J) (hB : B ∈ skew_adjoint_matrices_submodule J) :
  ⁅A, B⁆ ∈ skew_adjoint_matrices_submodule J :=
begin
  simp only [mem_skew_adjoint_matrices_submodule] at *,
  change ⁅A, B⁆ᵀ ⬝ J = J ⬝ -⁅A, B⁆, change Aᵀ ⬝ J = J ⬝ -A at hA, change Bᵀ ⬝ J = J ⬝ -B at hB,
  simp only [←matrix.mul_eq_mul] at *,
  rw [matrix.lie_transpose, lie_ring.of_associative_ring_bracket, lie_ring.of_associative_ring_bracket,
    sub_mul, mul_assoc, mul_assoc, hA, hB, ←mul_assoc, ←mul_assoc, hA, hB],
  noncomm_ring,
end

/-- The Lie subalgebra of skew-adjoint square matrices corresponding to a square matrix `J`. -/
def skew_adjoint_matrices_lie_subalgebra : lie_subalgebra R (matrix n n R) :=
{ lie_mem := J.is_skew_adjoint_bracket, ..(skew_adjoint_matrices_submodule J) }

/-- An invertible matrix `P` gives a Lie algebra equivalence between those endomorphisms that are
skew-adjoint with respect to a square matrix `J` and those with respect to `PᵀJP`. -/
noncomputable def skew_adjoint_matrices_lie_subalgebra_equiv (P : matrix n n R) (h : is_unit P) :
  skew_adjoint_matrices_lie_subalgebra J ≃ₗ⁅R⁆ skew_adjoint_matrices_lie_subalgebra (Pᵀ ⬝ J ⬝ P) :=
lie_algebra.equiv.of_subalgebras _ _ (P.lie_conj h).symm
begin
  ext A,
  suffices : P.lie_conj h A ∈ skew_adjoint_matrices_submodule J ↔
    A ∈ skew_adjoint_matrices_submodule (Pᵀ ⬝ J ⬝ P),
  { simp only [lie_subalgebra.mem_coe, submodule.mem_map_equiv, lie_subalgebra.mem_map_submodule,
      coe_coe], exact this, },
  simp [matrix.is_skew_adjoint, J.is_adjoint_pair_equiv _ _ P h],
end

lemma skew_adjoint_matrices_lie_subalgebra_equiv_apply
  (P : matrix n n R) (h : is_unit P) (A : skew_adjoint_matrices_lie_subalgebra J) :
  ↑(skew_adjoint_matrices_lie_subalgebra_equiv J P h A) = P⁻¹ ⬝ ↑A ⬝ P :=
by simp [skew_adjoint_matrices_lie_subalgebra_equiv]

end skew_adjoint_matrices
