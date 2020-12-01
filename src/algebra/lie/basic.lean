/-
Copyright (c) 2019 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.algebra.basic
import linear_algebra.bilinear_form
import linear_algebra.matrix
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

Working over a fixed commutative ring `R`, we introduce the notations:
 * `L →ₗ⁅R⁆ L'` for a morphism of Lie algebras,
 * `L ≃ₗ⁅R⁆ L'` for an equivalence of Lie algebras,
 * `M →ₗ⁅R,L⁆ N` for a morphism of Lie algebra modules `M`, `N` over a Lie algebra `L`,
 * `M ≃ₗ⁅R,L⁆ N` for an equivalence of Lie algebra modules `M`, `N` over a Lie algebra `L`.

## Implementation notes

Lie algebras are defined as modules with a compatible Lie ring structure and thus, like modules,
are partially unbundled.

## References
* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*][bourbaki1975]

## Tags

lie bracket, ring commutator, jacobi identity, lie ring, lie algebra
-/

universes u v w w₁ w₂

/-- The has_bracket class has two intended uses:

  1. for the product `⁅x, y⁆` of two elements `x`, `y` in a Lie algebra
     (analogous to `has_mul` in the associative setting),

  2. for the action `⁅x, m⁆` of an element `x` of a Lie algebra on an element `m` in one of its
     modules (analogous to `has_scalar` in the associative setting). -/
class has_bracket (L : Type v) (M : Type w) := (bracket : L → M → M)

notation `⁅`x`,` y`⁆` := has_bracket.bracket x y

/-- A Lie ring is an additive group with compatible product, known as the bracket, satisfying the
Jacobi identity. The bracket is not associative unless it is identically zero. -/
@[protect_proj] class lie_ring (L : Type v) extends add_comm_group L, has_bracket L L :=
(add_lie : ∀ (x y z : L), ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆)
(lie_add : ∀ (x y z : L), ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆)
(lie_self : ∀ (x : L), ⁅x, x⁆ = 0)
(leibniz_lie : ∀ (x y z : L), ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆)

/-- A Lie algebra is a module with compatible product, known as the bracket, satisfying the Jacobi
identity. Forgetting the scalar multiplication, every Lie algebra is a Lie ring. -/
@[protect_proj] class lie_algebra (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] extends semimodule R L :=
(lie_smul : ∀ (t : R) (x y : L), ⁅x, t • y⁆ = t • ⁅x, y⁆)

/-- A Lie ring module is an additive group, together with an additive action of a
Lie ring on this group, such that the Lie bracket acts as the commutator of endomorphisms.
(For representations of Lie *algebras* see `lie_module`.) -/
@[protect_proj] class lie_ring_module (L : Type v) (M : Type w)
  [lie_ring L] [add_comm_group M] extends has_bracket L M :=
(add_lie : ∀ (x y : L) (m : M), ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆)
(lie_add : ∀ (x : L) (m n : M), ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆)
(leibniz_lie : ∀ (x y : L) (m : M), ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆)

/-- A Lie module is a module over a commutative ring, together with a linear action of a Lie
algebra on this module, such that the Lie bracket acts as the commutator of endomorphisms. -/
@[protect_proj] class lie_module (R : Type u) (L : Type v) (M : Type w)
  [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M] [lie_ring_module L M] :=
(smul_lie : ∀ (t : R) (x : L) (m : M), ⁅t • x, m⁆ = t • ⁅x, m⁆)
(lie_smul : ∀ (t : R) (x : L) (m : M), ⁅x, t • m⁆ = t • ⁅x, m⁆)

section basic_properties

variables {R : Type u} {L : Type v} {M : Type w}
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]
variables [lie_ring_module L M] [lie_module R L M]
variables (t : R) (x y z : L) (m n : M)

@[simp] lemma add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆ := lie_ring_module.add_lie x y m

@[simp] lemma lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆ := lie_ring_module.lie_add x m n

@[simp] lemma smul_lie : ⁅t • x, m⁆ = t • ⁅x, m⁆ := lie_module.smul_lie t x m

@[simp] lemma lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆ := lie_module.lie_smul t x m

lemma leibniz_lie : ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆ := lie_ring_module.leibniz_lie x y m

@[simp] lemma lie_zero : ⁅x, 0⁆ = (0 : M) := (add_monoid_hom.mk' _ (lie_add x)).map_zero

@[simp] lemma zero_lie : ⁅(0 : L), m⁆ = 0 :=
(add_monoid_hom.mk' (λ (x : L), ⁅x, m⁆) (λ x y, add_lie x y m)).map_zero

@[simp] lemma lie_self : ⁅x, x⁆ = 0 := lie_ring.lie_self x

instance lie_ring_self_module : lie_ring_module L L := { ..(infer_instance : lie_ring L) }

@[simp] lemma lie_skew : -⁅y, x⁆ = ⁅x, y⁆ :=
have h : ⁅x + y, x⁆ + ⁅x + y, y⁆ = 0, { rw ← lie_add, apply lie_self, },
by simpa [neg_eq_iff_add_eq_zero] using h

/-- Every Lie algebra is a module over itself. -/
instance lie_algebra_self_module : lie_module R L L :=
{ smul_lie := λ t x m, by rw [←lie_skew, ←lie_skew x m, lie_algebra.lie_smul, smul_neg],
  lie_smul := by apply lie_algebra.lie_smul, }

@[simp] lemma neg_lie : ⁅-x, m⁆ = -⁅x, m⁆ :=
by { rw [←sub_eq_zero_iff_eq, sub_neg_eq_add, ←add_lie], simp, }

@[simp] lemma lie_neg : ⁅x, -m⁆ = -⁅x, m⁆ :=
by { rw [←sub_eq_zero_iff_eq, sub_neg_eq_add, ←lie_add], simp, }

@[simp] lemma gsmul_lie (a : ℤ) : ⁅a • x, m⁆ = a • ⁅x, m⁆ :=
add_monoid_hom.map_gsmul ⟨λ (x : L), ⁅x, m⁆, zero_lie m, λ _ _, add_lie _ _ _⟩ _ _

@[simp] lemma lie_gsmul (a : ℤ) : ⁅x, a • m⁆ = a • ⁅x, m⁆ :=
add_monoid_hom.map_gsmul ⟨λ (m : M), ⁅x, m⁆, lie_zero x, λ _ _, lie_add _ _ _⟩ _ _

@[simp] lemma lie_lie : ⁅⁅x, y⁆, m⁆ = ⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆ :=
by rw [leibniz_lie, add_sub_cancel]

lemma lie_jacobi : ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 :=
by { rw [← neg_neg ⁅x, y⁆, lie_neg z, lie_skew y x, ← lie_skew, lie_lie], abel, }

end basic_properties

namespace lie_algebra

set_option old_structure_cmd true
/-- A morphism of Lie algebras is a linear map respecting the bracket operations. -/
structure morphism (R : Type u) (L : Type v) (L' : Type w)
  [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L']
  extends linear_map R L L' :=
(map_lie : ∀ {x y : L}, to_fun ⁅x, y⁆ = ⁅to_fun x, to_fun y⁆)

attribute [nolint doc_blame] lie_algebra.morphism.to_linear_map

notation L ` →ₗ⁅`:25 R:25 `⁆ `:0 L':0 := morphism R L L'

section morphism_properties

variables {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}
variables [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_ring L₃]
variables [lie_algebra R L₁] [lie_algebra R L₂] [lie_algebra R L₃]

instance : has_coe (L₁ →ₗ⁅R⁆ L₂) (L₁ →ₗ[R] L₂) := ⟨morphism.to_linear_map⟩

/-- see Note [function coercion] -/
instance : has_coe_to_fun (L₁ →ₗ⁅R⁆ L₂) := ⟨_, morphism.to_fun⟩

@[simp] lemma coe_mk (f : L₁ → L₂) (h₁ h₂ h₃) :
  ((⟨f, h₁, h₂, h₃⟩ : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) = f := rfl

@[simp, norm_cast] lemma coe_to_linear_map (f : L₁ →ₗ⁅R⁆ L₂) : ((f : L₁ →ₗ[R] L₂) : L₁ → L₂) = f :=
rfl

@[simp] lemma map_lie (f : L₁ →ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x, f y⁆ := morphism.map_lie f

/-- The constant 0 map is a Lie algebra morphism. -/
instance : has_zero (L₁ →ₗ⁅R⁆ L₂) := ⟨{ map_lie := by simp, ..(0 : L₁ →ₗ[R] L₂)}⟩

/-- The identity map is a Lie algebra morphism. -/
instance : has_one (L₁ →ₗ⁅R⁆ L₁) := ⟨{ map_lie := by simp, ..(1 : L₁ →ₗ[R] L₁)}⟩

instance : inhabited (L₁ →ₗ⁅R⁆ L₂) := ⟨0⟩

lemma morphism.coe_injective : function.injective (λ f : L₁ →ₗ⁅R⁆ L₂, show L₁ → L₂, from f) :=
by rintro ⟨f, _⟩ ⟨g, _⟩ ⟨h⟩; congr

@[ext] lemma morphism.ext {f g : L₁ →ₗ⁅R⁆ L₂} (h : ∀ x, f x = g x) : f = g :=
morphism.coe_injective $ funext h

lemma morphism.ext_iff {f g : L₁ →ₗ⁅R⁆ L₂} : f = g ↔ ∀ x, f x = g x :=
⟨by { rintro rfl x, refl }, morphism.ext⟩

/-- The composition of morphisms is a morphism. -/
def morphism.comp (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) : L₁ →ₗ⁅R⁆ L₃ :=
{ map_lie := λ x y, by { change f (g ⁅x, y⁆) = ⁅f (g x), f (g y)⁆, rw [map_lie, map_lie], },
  ..linear_map.comp f.to_linear_map g.to_linear_map }

@[simp] lemma morphism.comp_apply (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) (x : L₁) :
  f.comp g x = f (g x) := rfl

@[norm_cast]
lemma morphism.comp_coe (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) :
  (f : L₂ → L₃) ∘ (g : L₁ → L₂) = f.comp g := rfl

/-- The inverse of a bijective morphism is a morphism. -/
def morphism.inverse (f : L₁ →ₗ⁅R⁆ L₂) (g : L₂ → L₁)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) : L₂ →ₗ⁅R⁆ L₁ :=
{ map_lie := λ x y,
  calc g ⁅x, y⁆ = g ⁅f (g x), f (g y)⁆ : by { conv_lhs { rw [←h₂ x, ←h₂ y], }, }
            ... = g (f ⁅g x, g y⁆) : by rw map_lie
            ... = ⁅g x, g y⁆ : (h₁ _),
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

end lie_algebra

section lie_module_morphisms

variables (R : Type u) (L : Type v) (M : Type w) (N : Type w₁) (P : Type w₂)
variables [comm_ring R] [lie_ring L] [lie_algebra R L]
variables [add_comm_group M] [add_comm_group N] [add_comm_group P]
variables [module R M] [module R N] [module R P]
variables [lie_ring_module L M] [lie_ring_module L N] [lie_ring_module L P]
variables [lie_module R L M] [lie_module R L N] [lie_module R L P]

set_option old_structure_cmd true

/-- A morphism of Lie algebra modules is a linear map which commutes with the action of the Lie
algebra. -/
structure lie_module_hom extends M →ₗ[R] N :=
(map_lie : ∀ {x : L} {m : M}, to_fun ⁅x, m⁆ = ⁅x, to_fun m⁆)

attribute [nolint doc_blame] lie_module_hom.to_linear_map

notation M ` →ₗ⁅`:25 R,L:25 `⁆ `:0 N:0 := lie_module_hom R L M N

namespace lie_module_hom

variables {R L M N P}

instance : has_coe (M →ₗ⁅R,L⁆ N) (M →ₗ[R] N) := ⟨lie_module_hom.to_linear_map⟩

/-- see Note [function coercion] -/
instance : has_coe_to_fun (M →ₗ⁅R,L⁆ N) := ⟨_, lie_module_hom.to_fun⟩

@[simp] lemma coe_mk (f : M → N) (h₁ h₂ h₃) :
  ((⟨f, h₁, h₂, h₃⟩ : M →ₗ⁅R,L⁆ N) : M → N) = f := rfl

@[simp, norm_cast] lemma coe_to_linear_map (f : M →ₗ⁅R,L⁆ N) : ((f : M →ₗ[R] N) : M → N) = f :=
rfl

@[simp] lemma map_lie' (f : M →ₗ⁅R,L⁆ N) (x : L) (m : M) : f ⁅x, m⁆ = ⁅x, f m⁆ :=
lie_module_hom.map_lie f

/-- The constant 0 map is a Lie module morphism. -/
instance : has_zero (M →ₗ⁅R,L⁆ N) := ⟨{ map_lie := by simp, ..(0 : M →ₗ[R] N) }⟩

/-- The identity map is a Lie module morphism. -/
instance : has_one (M →ₗ⁅R,L⁆ M) := ⟨{ map_lie := by simp, ..(1 : M →ₗ[R] M) }⟩

instance : inhabited (M →ₗ⁅R,L⁆ N) := ⟨0⟩

lemma coe_injective : function.injective (λ f : M →ₗ⁅R,L⁆ N, show M → N, from f) :=
by { rintros ⟨f, _⟩ ⟨g, _⟩ ⟨h⟩, congr, }

@[ext] lemma ext {f g : M →ₗ⁅R,L⁆ N} (h : ∀ m, f m = g m) : f = g :=
coe_injective $ funext h

lemma ext_iff {f g : M →ₗ⁅R,L⁆ N} : f = g ↔ ∀ m, f m = g m :=
⟨by { rintro rfl m, refl, }, ext⟩

/-- The composition of Lie module morphisms is a morphism. -/
def comp (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) : M →ₗ⁅R,L⁆ P :=
{ map_lie := λ x m, by { change f (g ⁅x, m⁆) = ⁅x, f (g m)⁆, rw [map_lie', map_lie'], },
  ..linear_map.comp f.to_linear_map g.to_linear_map }

@[simp] lemma comp_apply (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) (m : M) :
  f.comp g m = f (g m) := rfl

@[norm_cast] lemma comp_coe (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) :
  (f : N → P) ∘ (g : M → N) = f.comp g := rfl

/-- The inverse of a bijective morphism of Lie modules is a morphism of Lie modules. -/
def inverse (f : M →ₗ⁅R,L⁆ N) (g : N → M)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) : N →ₗ⁅R,L⁆ M :=
{ map_lie := λ x n,
    calc g ⁅x, n⁆ = g ⁅x, f (g n)⁆ : by rw h₂
              ... = g (f ⁅x, g n⁆) : by rw map_lie'
              ... = ⁅x, g n⁆ : (h₁ _),
  ..linear_map.inverse f.to_linear_map g h₁ h₂ }

end lie_module_hom

/-- An equivalence of Lie algebra modules is a linear equivalence which is also a morphism of
Lie algebra modules. -/
structure lie_module_equiv extends M ≃ₗ[R] N, M →ₗ⁅R,L⁆ N

attribute [nolint doc_blame] lie_module_equiv.to_lie_module_hom
attribute [nolint doc_blame] lie_module_equiv.to_linear_equiv

notation M ` ≃ₗ⁅`:25 R,L:25 `⁆ `:0 N:0 := lie_module_equiv R L M N

namespace lie_module_equiv

variables {R L M N P}

instance has_coe_to_lie_module_hom : has_coe (M ≃ₗ⁅R,L⁆ N) (M →ₗ⁅R,L⁆ N) := ⟨to_lie_module_hom⟩
instance has_coe_to_linear_equiv : has_coe (M ≃ₗ⁅R,L⁆ N) (M ≃ₗ[R] N) := ⟨to_linear_equiv⟩

/-- see Note [function coercion] -/
instance : has_coe_to_fun (M ≃ₗ⁅R,L⁆ N) := ⟨_, to_fun⟩

@[simp, norm_cast] lemma coe_to_lie_module_hom (e : M ≃ₗ⁅R,L⁆ N) : ((e : M →ₗ⁅R,L⁆ N) : M → N) = e :=
  rfl

@[simp, norm_cast] lemma coe_to_linear_equiv (e : M ≃ₗ⁅R,L⁆ N) : ((e : M ≃ₗ[R] N) : M → N) = e :=
  rfl

instance : has_one (M ≃ₗ⁅R,L⁆ M) := ⟨{ map_lie := λ x m, rfl, ..(1 : M ≃ₗ[R] M) }⟩

@[simp] lemma one_apply (m : M) : (1 : (M ≃ₗ⁅R,L⁆ M)) m = m := rfl

instance : inhabited (M ≃ₗ⁅R,L⁆ M) := ⟨1⟩

/-- Lie module equivalences are reflexive. -/
@[refl] def refl : M ≃ₗ⁅R,L⁆ M := 1

@[simp] lemma refl_apply (m : M) : (refl : M ≃ₗ⁅R,L⁆ M) m = m := rfl

/-- Lie module equivalences are syemmtric. -/
@[symm] def symm (e : M ≃ₗ⁅R,L⁆ N) : N ≃ₗ⁅R,L⁆ M :=
{ ..lie_module_hom.inverse e.to_lie_module_hom e.inv_fun e.left_inv e.right_inv,
  ..(e : M ≃ₗ[R] N).symm }

@[simp] lemma symm_symm (e : M ≃ₗ⁅R,L⁆ N) : e.symm.symm = e :=
by { cases e, refl, }

@[simp] lemma apply_symm_apply (e : M ≃ₗ⁅R,L⁆ N) : ∀ x, e (e.symm x) = x :=
  e.to_linear_equiv.apply_symm_apply

@[simp] lemma symm_apply_apply (e : M ≃ₗ⁅R,L⁆ N) : ∀ x, e.symm (e x) = x :=
  e.to_linear_equiv.symm_apply_apply

/-- Lie module equivalences are transitive. -/
@[trans] def trans (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) : M ≃ₗ⁅R,L⁆ P :=
{ ..lie_module_hom.comp e₂.to_lie_module_hom e₁.to_lie_module_hom,
  ..linear_equiv.trans e₁.to_linear_equiv e₂.to_linear_equiv }

@[simp] lemma trans_apply (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) (m : M) :
  (e₁.trans e₂) m = e₂ (e₁ m) := rfl

@[simp] lemma symm_trans_apply (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) (p : P) :
  (e₁.trans e₂).symm p = e₁.symm (e₂.symm p) := rfl

end lie_module_equiv

end lie_module_morphisms

section of_associative

variables {A : Type v} [ring A]

namespace ring_commutator

/-- The bracket operation for rings is the ring commutator, which captures the extent to which a
ring is commutative. It is identically zero exactly when the ring is commutative. -/
@[priority 100]
instance : has_bracket A A := ⟨λ x y, x*y - y*x⟩

lemma commutator (x y : A) : ⁅x, y⁆ = x*y - y*x := rfl

end ring_commutator

namespace lie_ring

/-- An associative ring gives rise to a Lie ring by taking the bracket to be the ring commutator. -/
@[priority 100]
instance of_associative_ring : lie_ring A :=
{ add_lie      := by simp only [ring_commutator.commutator, right_distrib, left_distrib,
    sub_eq_add_neg, add_comm, add_left_comm, forall_const, eq_self_iff_true, neg_add_rev],
  lie_add      := by simp only [ring_commutator.commutator, right_distrib, left_distrib,
    sub_eq_add_neg, add_comm, add_left_comm, forall_const, eq_self_iff_true, neg_add_rev],
  lie_self     := by simp only [ring_commutator.commutator, forall_const, sub_self],
  leibniz_lie  := λ x y z, by { repeat {rw ring_commutator.commutator}, noncomm_ring, } }

lemma of_associative_ring_bracket (x y : A) : ⁅x, y⁆ = x*y - y*x := rfl

end lie_ring

/-- An Abelian Lie algebra is one in which all brackets vanish. -/
class is_lie_abelian (L : Type v) [has_bracket L L] [has_zero L] : Prop :=
(abelian : ∀ (x y : L), ⁅x, y⁆ = 0)

lemma commutative_ring_iff_abelian_lie_ring : is_commutative A (*) ↔ is_lie_abelian A :=
begin
  have h₁ : is_commutative A (*) ↔ ∀ (a b : A), a * b = b * a := ⟨λ h, h.1, λ h, ⟨h⟩⟩,
  have h₂ : is_lie_abelian A ↔ ∀ (a b : A), ⁅a, b⁆ = 0 := ⟨λ h, h.1, λ h, ⟨h⟩⟩,
  simp only [h₁, h₂, lie_ring.of_associative_ring_bracket, sub_eq_zero],
end

namespace lie_algebra

variables {R : Type u} [comm_ring R] [algebra R A]

/-- An associative algebra gives rise to a Lie algebra by taking the bracket to be the ring
commutator. -/
@[priority 100]
instance of_associative_algebra : lie_algebra R A :=
{ lie_smul := λ t x y,
    by rw [lie_ring.of_associative_ring_bracket, lie_ring.of_associative_ring_bracket,
           algebra.mul_smul_comm, algebra.smul_mul_assoc, smul_sub], }

/-- The map `of_associative_algebra` associating a Lie algebra to an associative algebra is
functorial. -/
def of_associative_algebra_hom {B : Type w} [ring B] [algebra R B] (f : A →ₐ[R] B) : A →ₗ⁅R⁆ B :=
 { map_lie := λ x y, show f ⁅x,y⁆ = ⁅f x,f y⁆,
     by simp only [lie_ring.of_associative_ring_bracket, alg_hom.map_sub, alg_hom.map_mul],
  ..f.to_linear_map, }

@[simp] lemma of_associative_algebra_hom_id : of_associative_algebra_hom (alg_hom.id R A) = 1 := rfl

@[simp] lemma of_associative_algebra_hom_apply {B : Type w} [ring B] [algebra R B]
  (f : A →ₐ[R] B) (x : A) : of_associative_algebra_hom f x = f x := rfl

@[simp] lemma of_associative_algebra_hom_comp {B : Type w} {C : Type w₁}
  [ring B] [ring C] [algebra R B] [algebra R C] (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
  of_associative_algebra_hom (g.comp f) =
  (of_associative_algebra_hom g).comp (of_associative_algebra_hom f) := rfl

end lie_algebra

end of_associative

section adjoint_action

variables (R : Type u) (L : Type v) (M : Type w)
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]
variables [lie_ring_module L M] [lie_module R L M]

/-- A Lie module yields a Lie algebra morphism into the linear endomorphisms of the module. -/
def lie_module.to_endo_morphism : L →ₗ⁅R⁆ module.End R M :=
{ to_fun    := λ x,
  { to_fun    := λ m, ⁅x, m⁆,
    map_add'  := lie_add x,
    map_smul' := λ t, lie_smul t x, },
  map_add'  := λ x y, by { ext m, apply add_lie, },
  map_smul' := λ t x, by { ext m, apply smul_lie, },
  map_lie   := λ x y, by { ext m, apply lie_lie, }, }

/-- The adjoint action of a Lie algebra on itself. -/
def lie_algebra.ad : L →ₗ⁅R⁆ module.End R L := lie_module.to_endo_morphism R L L

@[simp] lemma lie_algebra.ad_apply (x y : L) : lie_algebra.ad R L x y = ⁅x, y⁆ := rfl

end adjoint_action

section lie_subalgebra

variables (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L]

set_option old_structure_cmd true
/-- A Lie subalgebra of a Lie algebra is submodule that is closed under the Lie bracket.
This is a sufficient condition for the subset itself to form a Lie algebra. -/
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
instance lie_subalgebra_lie_ring (L' : lie_subalgebra R L) : lie_ring L' :=
{ bracket      := λ x y, ⟨⁅x.val, y.val⁆, L'.lie_mem x.property y.property⟩,
  lie_add      := by { intros, apply set_coe.ext, apply lie_add, },
  add_lie      := by { intros, apply set_coe.ext, apply add_lie, },
  lie_self     := by { intros, apply set_coe.ext, apply lie_self, },
  leibniz_lie  := by { intros, apply set_coe.ext, apply leibniz_lie, } }

/-- A Lie subalgebra forms a new Lie algebra. -/
instance lie_subalgebra_lie_algebra (L' : lie_subalgebra R L) :
    @lie_algebra R L' _ (lie_subalgebra_lie_ring _ _ _) :=
{ lie_smul := by { intros, apply set_coe.ext, apply lie_smul } }

@[simp] lemma lie_subalgebra.mem_coe {L' : lie_subalgebra R L} {x : L} :
  x ∈ (L' : set L) ↔ x ∈ L' := iff.rfl

@[simp] lemma lie_subalgebra.mem_coe' {L' : lie_subalgebra R L} {x : L} :
  x ∈ (L' : submodule R L) ↔ x ∈ L' := iff.rfl

@[simp, norm_cast] lemma lie_subalgebra.coe_bracket (L' : lie_subalgebra R L) (x y : L') :
  (↑⁅x, y⁆ : L) = ⁅(↑x : L), ↑y⁆ := rfl

@[ext] lemma lie_subalgebra.ext (L₁' L₂' : lie_subalgebra R L) (h : ∀ x, x ∈ L₁' ↔ x ∈ L₂') :
  L₁' = L₂' :=
by { cases L₁', cases L₂', simp only [], ext x, exact h x, }

lemma lie_subalgebra.ext_iff (L₁' L₂' : lie_subalgebra R L) : L₁' = L₂' ↔ ∀ x, x ∈ L₁' ↔ x ∈ L₂' :=
⟨λ h x, by rw h, lie_subalgebra.ext R L L₁' L₂'⟩

/-- A subalgebra of an associative algebra is a Lie subalgebra of the associated Lie algebra. -/
def lie_subalgebra_of_subalgebra (A : Type v) [ring A] [algebra R A]
  (A' : subalgebra R A) : lie_subalgebra R A :=
{ lie_mem := λ x y hx hy, by {
    change ⁅x, y⁆ ∈ A', change x ∈ A' at hx, change y ∈ A' at hy,
    rw lie_ring.of_associative_ring_bracket,
    have hxy := A'.mul_mem hx hy,
    have hyx := A'.mul_mem hy hx,
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
  (↑⁅x, y⁆ : L₂) = ⁅(↑x : L₂), ↑y⁆ := rfl

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
iff.rfl

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

section lie_submodule

variables (R : Type u) (L : Type v) (M : Type w)
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]

/-- A Lie submodule of a Lie module is a submodule that is closed under the Lie bracket.
This is a sufficient condition for the subset itself to form a Lie module. -/
structure lie_submodule [lie_ring_module L M] [lie_module R L M] extends submodule R M :=
(lie_mem : ∀ {x : L} {m : M}, m ∈ carrier → ⁅x, m⁆ ∈ carrier)

/-- The zero module is a Lie submodule of any Lie module. -/
instance [lie_ring_module L M] [lie_module R L M] : has_zero (lie_submodule R L M) :=
⟨{ lie_mem := λ x m h, by { rw ((submodule.mem_bot R).1 h), apply lie_zero, },
   ..(0 : submodule R M)}⟩

instance [lie_ring_module L M] [lie_module R L M] : inhabited (lie_submodule R L M) := ⟨0⟩

instance lie_submodule_coe_submodule [lie_ring_module L M] [lie_module R L M] :
  has_coe (lie_submodule R L M) (submodule R M) :=
⟨lie_submodule.to_submodule⟩

instance lie_submodule_has_mem [lie_ring_module L M] [lie_module R L M] :
  has_mem M (lie_submodule R L M) :=
⟨λ x N, x ∈ (N : set M)⟩

instance lie_submodule_act [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) :
  lie_ring_module L N :=
{ bracket     := λ (x : L) (m : N), ⟨⁅x, m.val⁆, N.lie_mem m.property⟩,
  add_lie     := by { intros x y m, apply set_coe.ext, apply add_lie, },
  lie_add     := by { intros x m n, apply set_coe.ext, apply lie_add, },
  leibniz_lie := by { intros x y m, apply set_coe.ext, apply leibniz_lie, }, }

instance lie_submodule_lie_module
  [lie_ring_module L M] [lie_module R L M] (N : lie_submodule R L M) : lie_module R L N :=
{ lie_smul := by { intros t x y, apply set_coe.ext, apply lie_smul, },
  smul_lie := by { intros t x y, apply set_coe.ext, apply smul_lie, }, }

/-- A Lie module is irreducible if its only non-trivial Lie submodule is itself. -/
class lie_module.is_irreducible [lie_ring_module L M] [lie_module R L M] : Prop :=
(irreducible : ∀ (M' : lie_submodule R L M), (∃ (m : M'), m ≠ 0) → (∀ (m : M), m ∈ M'))

/-- A Lie algebra is simple if it is irreducible as a Lie module over itself via the adjoint
action, and it is non-Abelian. -/
class lie_algebra.is_simple : Prop :=
(simple : lie_module.is_irreducible R L L ∧ ¬is_lie_abelian L)

variables (L)

/-- An ideal of a Lie algebra is a Lie submodule of the Lie algebra as a Lie module over itself. -/
abbreviation lie_ideal := lie_submodule R L L

lemma lie_mem_right (I : lie_ideal R L) (x y : L) (h : y ∈ I) : ⁅x, y⁆ ∈ I := I.lie_mem h

lemma lie_mem_left (I : lie_ideal R L) (x y : L) (h : x ∈ I) : ⁅x, y⁆ ∈ I :=
 by { rw [←lie_skew, ←neg_lie], apply lie_mem_right, assumption, }

/-- An ideal of a Lie algebra is a Lie subalgebra. -/
def lie_ideal_subalgebra (I : lie_ideal R L) : lie_subalgebra R L :=
{ lie_mem := by { intros x y hx hy, apply lie_mem_right, exact hy, },
  ..I.to_submodule, }

end lie_submodule

namespace lie_submodule

variables {R : Type u} {L : Type v} {M : Type v}
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]
variables [lie_ring_module L M] [lie_module R L M]
variables (N : lie_submodule R L M) (I : lie_ideal R L)

/-- The quotient of a Lie module by a Lie submodule. It is a Lie module. -/
abbreviation quotient := N.to_submodule.quotient

namespace quotient

variables {N I}

/-- Map sending an element of `M` to the corresponding element of `M/N`, when `N` is a
lie_submodule of the lie_module `N`. -/
abbreviation mk : M → N.quotient := submodule.quotient.mk

lemma is_quotient_mk (m : M) :
  quotient.mk' m = (mk m : N.quotient) := rfl

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there
is a natural linear map from `L` to the endomorphisms of `M` leaving `N` invariant. -/
def lie_submodule_invariant : L →ₗ[R] submodule.compatible_maps N.to_submodule N.to_submodule :=
  linear_map.cod_restrict _ (lie_module.to_endo_morphism R L M) N.lie_mem

variables (N)

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there
is a natural Lie algebra morphism from `L` to the linear endomorphism of the quotient `M/N`. -/
def action_as_endo_map : L →ₗ⁅R⁆ module.End R N.quotient :=
{ map_lie := λ x y, by { ext n, apply quotient.induction_on' n, intros m,
                         change mk ⁅⁅x, y⁆, m⁆ = mk (⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆),
                         congr, apply lie_lie, },
  ..linear_map.comp (submodule.mapq_linear (N : submodule R M) ↑N) lie_submodule_invariant }

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there is
a natural bracket action of `L` on the quotient `M/N`. -/
def action_as_endo_map_bracket : has_bracket L N.quotient := ⟨λ x n, action_as_endo_map N x n⟩

instance lie_quotient_lie_ring_module : lie_ring_module L N.quotient :=
{ bracket     := λ x n, (action_as_endo_map N : L →ₗ[R] module.End R N.quotient) x n,
  add_lie     := λ x y n, by { simp only [linear_map.map_add, linear_map.add_apply], },
  lie_add     := λ x m n, by { simp only [linear_map.map_add, linear_map.add_apply], },
  leibniz_lie := λ x y m, show action_as_endo_map _ _ _ = _,
  { simp only [lie_algebra.map_lie, lie_ring.of_associative_ring_bracket, sub_add_cancel,
      lie_algebra.coe_to_linear_map, linear_map.mul_app, linear_map.sub_apply], } }

/-- The quotient of a Lie module by a Lie submodule, is a Lie module. -/
instance lie_quotient_lie_module : lie_module R L N.quotient :=
{ smul_lie := λ t x m, show (_ : L →ₗ[R] module.End R N.quotient) _ _ = _,
  { simp only [linear_map.map_smul], refl, },
  lie_smul := λ x t m, show (_ : L →ₗ[R] module.End R N.quotient) _ _ = _,
  { simp only [linear_map.map_smul], refl, }, }

instance lie_quotient_has_bracket : has_bracket (quotient I) (quotient I) :=
⟨begin
  intros x y,
  apply quotient.lift_on₂' x y (λ x' y', mk ⁅x', y'⁆),
  intros x₁ x₂ y₁ y₂ h₁ h₂,
  apply (submodule.quotient.eq I.to_submodule).2,
  have h : ⁅x₁, x₂⁆ - ⁅y₁, y₂⁆ = ⁅x₁, x₂ - y₂⁆ + ⁅x₁ - y₁, y₂⁆ := by simp [-lie_skew, sub_eq_add_neg, add_assoc],
  rw h,
  apply submodule.add_mem,
  { apply lie_mem_right R L I x₁ (x₂ - y₂) h₂, },
  { apply lie_mem_left R L I (x₁ - y₁) y₂ h₁, },
end⟩

@[simp] lemma mk_bracket (x y : L) :
  mk ⁅x, y⁆ = ⁅(mk x : quotient I), (mk y : quotient I)⁆ := rfl

instance lie_quotient_lie_ring : lie_ring (quotient I) :=
{ add_lie  := by { intros x' y' z', apply quotient.induction_on₃' x' y' z', intros x y z,
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
  leibniz_lie := by { intros x' y' z', apply quotient.induction_on₃' x' y' z', intros x y z,
                   repeat { rw is_quotient_mk <|>
                            rw ←mk_bracket <|>
                            rw ←submodule.quotient.mk_add, },
                   apply congr_arg, apply leibniz_lie, } }

instance lie_quotient_lie_algebra : lie_algebra R (quotient I) :=
{ lie_smul := by { intros t x' y', apply quotient.induction_on₂' x' y', intros x y,
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
{ map_lie := λ f g, show e.conj ⁅f, g⁆ = ⁅e.conj f, e.conj g⁆,
    by simp only [lie_ring.of_associative_ring_bracket, linear_map.mul_eq_comp, e.conj_comp,
                  linear_equiv.map_sub],
  ..e.conj }

@[simp] lemma lie_conj_apply (f : module.End R M₁) : e.lie_conj f = e.conj f := rfl

@[simp] lemma lie_conj_symm : e.lie_conj.symm = e.symm.lie_conj := rfl

end linear_equiv

namespace alg_equiv

variables {R : Type u} {A₁ : Type v} {A₂ : Type w}
variables [comm_ring R] [ring A₁] [ring A₂] [algebra R A₁] [algebra R A₂]
variables (e : A₁ ≃ₐ[R] A₂)

/-- An equivalence of associative algebras is an equivalence of associated Lie algebras. -/
def to_lie_equiv : A₁ ≃ₗ⁅R⁆ A₂ :=
{ to_fun  := e.to_fun,
  map_lie := λ x y, by simp [lie_ring.of_associative_ring_bracket],
  ..e.to_linear_equiv }

@[simp] lemma to_lie_equiv_apply (x : A₁) : e.to_lie_equiv x = e x := rfl

@[simp] lemma to_lie_equiv_symm_apply (x : A₂) : e.to_lie_equiv.symm x = e.symm x := rfl

end alg_equiv

section matrices
open_locale matrix

variables {R : Type u} [comm_ring R]
variables {n : Type w} [decidable_eq n] [fintype n]

/-! ### Matrices

An important class of Lie algebras are those arising from the associative algebra structure on
square matrices over a commutative ring.
-/

/-- The natural equivalence between linear endomorphisms of finite free modules and square matrices
is compatible with the Lie algebra structures. -/
def lie_equiv_matrix' : module.End R (n → R) ≃ₗ⁅R⁆ matrix n n R :=
{ map_lie := λ T S,
  begin
    let f := @linear_map.to_matrix' R _ n n _ _ _,
    change f (T.comp S - S.comp T) = (f T) * (f S) - (f S) * (f T),
    have h : ∀ (T S : module.End R _), f (T.comp S) = (f T) ⬝ (f S) := linear_map.to_matrix'_comp,
    rw [linear_equiv.map_sub, h, h, matrix.mul_eq_mul, matrix.mul_eq_mul],
  end,
  ..linear_map.to_matrix' }

@[simp] lemma lie_equiv_matrix'_apply (f : module.End R (n → R)) :
  lie_equiv_matrix' f = f.to_matrix' := rfl

@[simp] lemma lie_equiv_matrix'_symm_apply (A : matrix n n R) :
  (@lie_equiv_matrix' R _ n _ _).symm A = A.to_lin' := rfl

/-- An invertible matrix induces a Lie algebra equivalence from the space of matrices to itself. -/
noncomputable def matrix.lie_conj (P : matrix n n R) (h : is_unit P) :
  matrix n n R ≃ₗ⁅R⁆ matrix n n R :=
((@lie_equiv_matrix' R _ n _ _).symm.trans (P.to_linear_equiv h).lie_conj).trans lie_equiv_matrix'

@[simp] lemma matrix.lie_conj_apply (P A : matrix n n R) (h : is_unit P) :
  P.lie_conj h A = P ⬝ A ⬝ P⁻¹ :=
by simp [linear_equiv.conj_apply, matrix.lie_conj, linear_map.to_matrix'_comp,
         linear_map.to_matrix'_to_lin']

@[simp] lemma matrix.lie_conj_symm_apply (P A : matrix n n R) (h : is_unit P) :
  (P.lie_conj h).symm A = P⁻¹ ⬝ A ⬝ P :=
by simp [linear_equiv.symm_conj_apply, matrix.lie_conj, linear_map.to_matrix'_comp,
         linear_map.to_matrix'_to_lin']

/-- For square matrices, the natural map that reindexes a matrix's rows and columns with equivalent
types is an equivalence of Lie algebras. -/
def matrix.reindex_lie_equiv {m : Type w₁} [decidable_eq m] [fintype m]
  (e : n ≃ m) : matrix n n R ≃ₗ⁅R⁆ matrix m m R :=
{ map_lie := λ M N, by simp only [lie_ring.of_associative_ring_bracket, matrix.reindex_mul,
    matrix.mul_eq_mul, linear_equiv.map_sub, linear_equiv.to_fun_apply],
..(matrix.reindex_linear_equiv e e) }

@[simp] lemma matrix.reindex_lie_equiv_apply {m : Type w₁} [decidable_eq m] [fintype m]
  (e : n ≃ m) (M : matrix n n R) :
  matrix.reindex_lie_equiv e M = λ i j, M (e.symm i) (e.symm j) :=
rfl

@[simp] lemma matrix.reindex_lie_equiv_symm_apply {m : Type w₁} [decidable_eq m] [fintype m]
  (e : n ≃ m) (M : matrix m m R) :
  (matrix.reindex_lie_equiv e).symm M = λ i j, M (e i) (e j) :=
rfl

end matrices
