/-
Copyright (c) 2019 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import data.bracket
import algebra.algebra.basic
import tactic.noncomm_ring

/-!
# Lie algebras

This file defines Lie rings and Lie algebras over a commutative ring together with their
modules, morphisms and equivalences, as well as various lemmas to make these definitions usable.

## Main definitions

  * `lie_ring`
  * `lie_algebra`
  * `lie_ring_module`
  * `lie_module`
  * `lie_hom`
  * `lie_equiv`
  * `lie_module_hom`
  * `lie_module_equiv`

## Notation

Working over a fixed commutative ring `R`, we introduce the notations:
 * `L →ₗ⁅R⁆ L'` for a morphism of Lie algebras,
 * `L ≃ₗ⁅R⁆ L'` for an equivalence of Lie algebras,
 * `M →ₗ⁅R,L⁆ N` for a morphism of Lie algebra modules `M`, `N` over a Lie algebra `L`,
 * `M ≃ₗ⁅R,L⁆ N` for an equivalence of Lie algebra modules `M`, `N` over a Lie algebra `L`.

## Implementation notes

Lie algebras are defined as modules with a compatible Lie ring structure and thus, like modules,
are partially unbundled.

## References
* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*](bourbaki1975)

## Tags

lie bracket, jacobi identity, lie ring, lie algebra, lie module
-/

universes u v w w₁ w₂

/-- A Lie ring is an additive group with compatible product, known as the bracket, satisfying the
Jacobi identity. The bracket is not associative unless it is identically zero. -/
@[protect_proj] class lie_ring (L : Type v) extends add_comm_group L, has_bracket L L :=
(add_lie : ∀ (x y z : L), ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆)
(lie_add : ∀ (x y z : L), ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆)
(lie_self : ∀ (x : L), ⁅x, x⁆ = 0)
(leibniz_lie : ∀ (x y z : L), ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆)

/-- A Lie algebra is a module with compatible product, known as the bracket, satisfying the Jacobi
identity. Forgetting the scalar multiplication, every Lie algebra is a Lie ring. -/
@[protect_proj] class lie_algebra (R : Type u) (L : Type v) [comm_ring R] [lie_ring L]
  extends semimodule R L :=
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
  [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]
  [lie_ring_module L M] :=
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
by { rw [←sub_eq_zero, sub_neg_eq_add, ←add_lie], simp, }

@[simp] lemma lie_neg : ⁅x, -m⁆ = -⁅x, m⁆ :=
by { rw [←sub_eq_zero, sub_neg_eq_add, ←lie_add], simp, }

@[simp] lemma gsmul_lie (a : ℤ) : ⁅a • x, m⁆ = a • ⁅x, m⁆ :=
add_monoid_hom.map_gsmul ⟨λ (x : L), ⁅x, m⁆, zero_lie m, λ _ _, add_lie _ _ _⟩ _ _

@[simp] lemma lie_gsmul (a : ℤ) : ⁅x, a • m⁆ = a • ⁅x, m⁆ :=
add_monoid_hom.map_gsmul ⟨λ (m : M), ⁅x, m⁆, lie_zero x, λ _ _, lie_add _ _ _⟩ _ _

@[simp] lemma lie_lie : ⁅⁅x, y⁆, m⁆ = ⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆ :=
by rw [leibniz_lie, add_sub_cancel]

lemma lie_jacobi : ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 :=
by { rw [← neg_neg ⁅x, y⁆, lie_neg z, lie_skew y x, ← lie_skew, lie_lie], abel, }

end basic_properties

set_option old_structure_cmd true
/-- A morphism of Lie algebras is a linear map respecting the bracket operations. -/
structure lie_hom (R : Type u) (L : Type v) (L' : Type w)
  [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L']
  extends L →ₗ[R] L' :=
(map_lie' : ∀ {x y : L}, to_fun ⁅x, y⁆ = ⁅to_fun x, to_fun y⁆)

attribute [nolint doc_blame] lie_hom.to_linear_map

notation L ` →ₗ⁅`:25 R:25 `⁆ `:0 L':0 := lie_hom R L L'

namespace lie_hom

variables {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}
variables [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_ring L₃]
variables [lie_algebra R L₁] [lie_algebra R L₂] [lie_algebra R L₃]

instance : has_coe (L₁ →ₗ⁅R⁆ L₂) (L₁ →ₗ[R] L₂) := ⟨lie_hom.to_linear_map⟩

/-- see Note [function coercion] -/
instance : has_coe_to_fun (L₁ →ₗ⁅R⁆ L₂) := ⟨_, lie_hom.to_fun⟩

initialize_simps_projections lie_hom (to_fun → apply)

@[simp] lemma coe_mk (f : L₁ → L₂) (h₁ h₂ h₃) :
  ((⟨f, h₁, h₂, h₃⟩ : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) = f := rfl

@[simp, norm_cast] lemma coe_to_linear_map (f : L₁ →ₗ⁅R⁆ L₂) : ((f : L₁ →ₗ[R] L₂) : L₁ → L₂) = f :=
rfl

@[simp] lemma map_smul (f : L₁ →ₗ⁅R⁆ L₂) (c : R) (x : L₁) : f (c • x) = c • f x :=
linear_map.map_smul (f : L₁ →ₗ[R] L₂) c x

@[simp] lemma map_add (f : L₁ →ₗ⁅R⁆ L₂) (x y : L₁) : f (x + y) = (f x) + (f y) :=
linear_map.map_add (f : L₁ →ₗ[R] L₂) x y

@[simp] lemma map_lie (f : L₁ →ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x, f y⁆ := lie_hom.map_lie' f

@[simp] lemma map_zero (f : L₁ →ₗ⁅R⁆ L₂) : f 0 = 0 := (f : L₁ →ₗ[R] L₂).map_zero

/-- The constant 0 map is a Lie algebra morphism. -/
instance : has_zero (L₁ →ₗ⁅R⁆ L₂) := ⟨{ map_lie' := by simp, ..(0 : L₁ →ₗ[R] L₂)}⟩

/-- The identity map is a Lie algebra morphism. -/
instance : has_one (L₁ →ₗ⁅R⁆ L₁) := ⟨{ map_lie' := by simp, ..(1 : L₁ →ₗ[R] L₁)}⟩

instance : inhabited (L₁ →ₗ⁅R⁆ L₂) := ⟨0⟩

lemma coe_injective : function.injective (λ f : L₁ →ₗ⁅R⁆ L₂, show L₁ → L₂, from f) :=
by rintro ⟨f, _⟩ ⟨g, _⟩ ⟨h⟩; congr

@[ext] lemma ext {f g : L₁ →ₗ⁅R⁆ L₂} (h : ∀ x, f x = g x) : f = g :=
coe_injective $ funext h

lemma ext_iff {f g : L₁ →ₗ⁅R⁆ L₂} : f = g ↔ ∀ x, f x = g x :=
⟨by { rintro rfl x, refl }, ext⟩

/-- The composition of morphisms is a morphism. -/
def comp (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) : L₁ →ₗ⁅R⁆ L₃ :=
{ map_lie' := λ x y, by { change f (g ⁅x, y⁆) = ⁅f (g x), f (g y)⁆, rw [map_lie, map_lie], },
  ..linear_map.comp f.to_linear_map g.to_linear_map }

@[simp] lemma comp_apply (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) (x : L₁) :
  f.comp g x = f (g x) := rfl

@[norm_cast]
lemma comp_coe (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) :
  (f : L₂ → L₃) ∘ (g : L₁ → L₂) = f.comp g := rfl

/-- The inverse of a bijective morphism is a morphism. -/
def inverse (f : L₁ →ₗ⁅R⁆ L₂) (g : L₂ → L₁)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) : L₂ →ₗ⁅R⁆ L₁ :=
{ map_lie' := λ x y,
  calc g ⁅x, y⁆ = g ⁅f (g x), f (g y)⁆ : by { conv_lhs { rw [←h₂ x, ←h₂ y], }, }
            ... = g (f ⁅g x, g y⁆) : by rw map_lie
            ... = ⁅g x, g y⁆ : (h₁ _),
  ..linear_map.inverse f.to_linear_map g h₁ h₂ }

end lie_hom

/-- An equivalence of Lie algebras is a morphism which is also a linear equivalence. We could
instead define an equivalence to be a morphism which is also a (plain) equivalence. However it is
more convenient to define via linear equivalence to get `.to_linear_equiv` for free. -/
structure lie_equiv (R : Type u) (L : Type v) (L' : Type w)
  [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L']
  extends L →ₗ⁅R⁆ L', L ≃ₗ[R] L'

attribute [nolint doc_blame] lie_equiv.to_lie_hom
attribute [nolint doc_blame] lie_equiv.to_linear_equiv

notation L ` ≃ₗ⁅`:50 R `⁆ ` L' := lie_equiv R L L'

namespace lie_equiv

variables {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}
variables [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_ring L₃]
variables [lie_algebra R L₁] [lie_algebra R L₂] [lie_algebra R L₃]

instance has_coe_to_lie_hom : has_coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ →ₗ⁅R⁆ L₂) := ⟨to_lie_hom⟩
instance has_coe_to_linear_equiv : has_coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ ≃ₗ[R] L₂) := ⟨to_linear_equiv⟩

/-- see Note [function coercion] -/
instance : has_coe_to_fun (L₁ ≃ₗ⁅R⁆ L₂) := ⟨_, to_fun⟩

@[simp, norm_cast] lemma coe_to_lie_equiv (e : L₁ ≃ₗ⁅R⁆ L₂) : ((e : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) = e :=
  rfl

@[simp, norm_cast] lemma coe_to_linear_equiv (e : L₁ ≃ₗ⁅R⁆ L₂) :
  ((e : L₁ ≃ₗ[R] L₂) : L₁ → L₂) = e := rfl

instance : has_one (L₁ ≃ₗ⁅R⁆ L₁) :=
⟨{ map_lie' := λ x y,
    by { change ((1 : L₁→ₗ[R] L₁) ⁅x, y⁆) = ⁅(1 : L₁→ₗ[R] L₁) x, (1 : L₁→ₗ[R] L₁) y⁆, simp, },
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
{ ..lie_hom.inverse e.to_lie_hom e.inv_fun e.left_inv e.right_inv,
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
{ ..lie_hom.comp e₂.to_lie_hom e₁.to_lie_hom,
  ..linear_equiv.trans e₁.to_linear_equiv e₂.to_linear_equiv }

@[simp] lemma trans_apply (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) (x : L₁) :
  (e₁.trans e₂) x = e₂ (e₁ x) := rfl

@[simp] lemma symm_trans_apply (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) (x : L₃) :
  (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) := rfl

lemma bijective (e : L₁ ≃ₗ⁅R⁆ L₂) : function.bijective ((e : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) :=
e.to_linear_equiv.bijective

lemma injective (e : L₁ ≃ₗ⁅R⁆ L₂) : function.injective ((e : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) :=
e.to_linear_equiv.injective

lemma surjective (e : L₁ ≃ₗ⁅R⁆ L₂) : function.surjective ((e : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) :=
e.to_linear_equiv.surjective

end lie_equiv

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
(map_lie' : ∀ {x : L} {m : M}, to_fun ⁅x, m⁆ = ⁅x, to_fun m⁆)

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

@[simp] lemma map_lie (f : M →ₗ⁅R,L⁆ N) (x : L) (m : M) : f ⁅x, m⁆ = ⁅x, f m⁆ :=
lie_module_hom.map_lie' f

/-- The constant 0 map is a Lie module morphism. -/
instance : has_zero (M →ₗ⁅R,L⁆ N) := ⟨{ map_lie' := by simp, ..(0 : M →ₗ[R] N) }⟩

/-- The identity map is a Lie module morphism. -/
instance : has_one (M →ₗ⁅R,L⁆ M) := ⟨{ map_lie' := by simp, ..(1 : M →ₗ[R] M) }⟩

instance : inhabited (M →ₗ⁅R,L⁆ N) := ⟨0⟩

lemma coe_injective : function.injective (λ f : M →ₗ⁅R,L⁆ N, show M → N, from f) :=
by { rintros ⟨f, _⟩ ⟨g, _⟩ ⟨h⟩, congr, }

@[ext] lemma ext {f g : M →ₗ⁅R,L⁆ N} (h : ∀ m, f m = g m) : f = g :=
coe_injective $ funext h

lemma ext_iff {f g : M →ₗ⁅R,L⁆ N} : f = g ↔ ∀ m, f m = g m :=
⟨by { rintro rfl m, refl, }, ext⟩

/-- The composition of Lie module morphisms is a morphism. -/
def comp (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) : M →ₗ⁅R,L⁆ P :=
{ map_lie' := λ x m, by { change f (g ⁅x, m⁆) = ⁅x, f (g m)⁆, rw [map_lie, map_lie], },
  ..linear_map.comp f.to_linear_map g.to_linear_map }

@[simp] lemma comp_apply (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) (m : M) :
  f.comp g m = f (g m) := rfl

@[norm_cast] lemma comp_coe (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) :
  (f : N → P) ∘ (g : M → N) = f.comp g := rfl

/-- The inverse of a bijective morphism of Lie modules is a morphism of Lie modules. -/
def inverse (f : M →ₗ⁅R,L⁆ N) (g : N → M)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) : N →ₗ⁅R,L⁆ M :=
{ map_lie' := λ x n,
    calc g ⁅x, n⁆ = g ⁅x, f (g n)⁆ : by rw h₂
              ... = g (f ⁅x, g n⁆) : by rw map_lie
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

@[simp, norm_cast] lemma coe_to_lie_module_hom (e : M ≃ₗ⁅R,L⁆ N) :
  ((e : M →ₗ⁅R,L⁆ N) : M → N) = e := rfl

@[simp, norm_cast] lemma coe_to_linear_equiv (e : M ≃ₗ⁅R,L⁆ N) : ((e : M ≃ₗ[R] N) : M → N) = e :=
rfl

instance : has_one (M ≃ₗ⁅R,L⁆ M) := ⟨{ map_lie' := λ x m, rfl, ..(1 : M ≃ₗ[R] M) }⟩

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
