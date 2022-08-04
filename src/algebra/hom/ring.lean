/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Jireh Loreaux
-/
import algebra.ring.basic

/-!
# Homomorphisms of semirings and rings

This file defines bundled homomorphisms of (non-unital) semirings and rings. As with monoid and
groups, we use the same structure `ring_hom a β`, a.k.a. `α →+* β`, for both types of homomorphisms.

The unbundled homomorphisms are defined in `deprecated.ring`. They are deprecated and the plan is to
slowly remove them from mathlib.

## Main definitions

* `non_unital_ring_hom`: Non-unital (semi)ring homomorphisms. Additive monoid homomorphism which
  preserve multiplication.
* `ring_hom`: (Semi)ring homomorphisms. Monoid homomorphisms which are also additive monoid
  homomorphism.

## Notations

* `→ₙ+*`: Non-unital (semi)ring homs
* `→+*`: (Semi)ring homs

## Implementation notes

* There's a coercion from bundled homs to fun, and the canonical notation is to
  use the bundled hom as a function via this coercion.

* There is no `semiring_hom` -- the idea is that `ring_hom` is used.
  The constructor for a `ring_hom` between semirings needs a proof of `map_zero`,
  `map_one` and `map_add` as well as `map_mul`; a separate constructor
  `ring_hom.mk'` will construct ring homs between rings from monoid homs given
  only a proof that addition is preserved.

## Tags

`ring_hom`, `semiring_hom`
-/

set_option old_structure_cmd true

open function

variables {F α β γ : Type*}

/-- Bundled non-unital semiring homomorphisms `α →ₙ+* β`; use this for bundled non-unital ring
homomorphisms too.

When possible, instead of parametrizing results over `(f : α →ₙ+* β)`,
you should parametrize over `(F : Type*) [non_unital_ring_hom_class F α β] (f : F)`.

When you extend this structure, make sure to extend `non_unital_ring_hom_class`. -/
structure non_unital_ring_hom (α β : Type*) [non_unital_non_assoc_semiring α]
  [non_unital_non_assoc_semiring β] extends α →ₙ* β, α →+ β

infixr ` →ₙ+* `:25 := non_unital_ring_hom

/-- Reinterpret a non-unital ring homomorphism `f : α →ₙ+* β` as a semigroup
homomorphism `α →ₙ* β`. The `simp`-normal form is `(f : α →ₙ* β)`. -/
add_decl_doc non_unital_ring_hom.to_mul_hom

/-- Reinterpret a non-unital ring homomorphism `f : α →ₙ+* β` as an additive
monoid homomorphism `α →+ β`. The `simp`-normal form is `(f : α →+ β)`. -/
add_decl_doc non_unital_ring_hom.to_add_monoid_hom

section non_unital_ring_hom_class

/-- `non_unital_ring_hom_class F α β` states that `F` is a type of non-unital (semi)ring
homomorphisms. You should extend this class when you extend `non_unital_ring_hom`. -/
class non_unital_ring_hom_class (F : Type*) (α β : out_param Type*)
  [non_unital_non_assoc_semiring α] [non_unital_non_assoc_semiring β]
  extends mul_hom_class F α β, add_monoid_hom_class F α β

variables [non_unital_non_assoc_semiring α] [non_unital_non_assoc_semiring β]
  [non_unital_ring_hom_class F α β]

instance : has_coe_t F (α →ₙ+* β) :=
⟨λ f, { to_fun := f, map_zero' := map_zero f, map_mul' := map_mul f, map_add' := map_add f }⟩

end non_unital_ring_hom_class

namespace non_unital_ring_hom

section coe

/-!
Throughout this section, some `semiring` arguments are specified with `{}` instead of `[]`.
See note [implicit instance arguments].
-/
variables {rα : non_unital_non_assoc_semiring α} {rβ : non_unital_non_assoc_semiring β}

include rα rβ

instance : non_unital_ring_hom_class (α →ₙ+* β) α β :=
{ coe := non_unital_ring_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_add := non_unital_ring_hom.map_add',
  map_zero := non_unital_ring_hom.map_zero',
  map_mul := non_unital_ring_hom.map_mul' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (α →ₙ+* β) (λ _, α → β) := ⟨non_unital_ring_hom.to_fun⟩

@[simp] lemma to_fun_eq_coe (f : α →ₙ+* β) : f.to_fun = f := rfl

@[simp] lemma coe_mk (f : α → β) (h₁ h₂ h₃) : ⇑(⟨f, h₁, h₂, h₃⟩ : α →ₙ+* β) = f := rfl

@[simp] lemma coe_coe [non_unital_ring_hom_class F α β] (f : F) : ((f : α →ₙ+* β) : α → β) = f :=
rfl

@[simp] lemma coe_to_mul_hom (f : α →ₙ+* β) : ⇑f.to_mul_hom = f := rfl

@[simp] lemma coe_mul_hom_mk (f : α → β) (h₁ h₂ h₃) :
  ((⟨f, h₁, h₂, h₃⟩ : α →ₙ+* β) : α →ₙ* β) = ⟨f, h₁⟩ := rfl

@[simp] lemma coe_to_add_monoid_hom (f : α →ₙ+* β) : ⇑f.to_add_monoid_hom = f := rfl

@[simp] lemma coe_add_monoid_hom_mk (f : α → β) (h₁ h₂ h₃) :
  ((⟨f, h₁, h₂, h₃⟩ : α →ₙ+* β) : α →+ β) = ⟨f, h₂, h₃⟩ := rfl

/-- Copy of a `ring_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : α →ₙ+* β) (f' : α → β) (h : f' = f) : α →ₙ+* β :=
{ ..f.to_mul_hom.copy f' h, ..f.to_add_monoid_hom.copy f' h }

end coe

variables [rα : non_unital_non_assoc_semiring α] [rβ : non_unital_non_assoc_semiring β]

section
include rα rβ

variables (f : α →ₙ+* β) {x y : α} {rα rβ}

@[ext] lemma ext ⦃f g : α →ₙ+* β⦄ : (∀ x, f x = g x) → f = g := fun_like.ext _ _

lemma ext_iff {f g : α →ₙ+* β} : f = g ↔ ∀ x, f x = g x := fun_like.ext_iff

@[simp] lemma mk_coe (f : α →ₙ+* β) (h₁ h₂ h₃) : non_unital_ring_hom.mk f h₁ h₂ h₃ = f :=
ext $ λ _, rfl

lemma coe_add_monoid_hom_injective : injective (coe : (α →ₙ+* β) → (α →+ β)) :=
λ f g h, ext $ add_monoid_hom.congr_fun h

lemma coe_mul_hom_injective : injective (coe : (α →ₙ+* β) → (α →ₙ* β)) :=
λ f g h, ext $ mul_hom.congr_fun h

end

/-- The identity non-unital ring homomorphism from a non-unital semiring to itself. -/
protected def id (α : Type*) [non_unital_non_assoc_semiring α] : α →ₙ+* α :=
by refine {to_fun := id, ..}; intros; refl

include rα rβ

instance : has_zero (α →ₙ+* β) :=
⟨{ to_fun := 0,
   map_mul' := λ x y, (mul_zero (0 : β)).symm,
   map_zero' := rfl,
   map_add' := λ x y, (add_zero (0 : β)).symm }⟩

instance : inhabited (α →ₙ+* β) := ⟨0⟩

@[simp] lemma coe_zero : ⇑(0 : α →ₙ+* β) = 0 := rfl
@[simp] lemma zero_apply (x : α) : (0 : α →ₙ+* β) x = 0 := rfl

omit rβ

@[simp] lemma id_apply (x : α) : non_unital_ring_hom.id α x = x := rfl
@[simp] lemma coe_add_monoid_hom_id :
  (non_unital_ring_hom.id α : α →+ α) = add_monoid_hom.id α := rfl
@[simp] lemma coe_mul_hom_id : (non_unital_ring_hom.id α : α →ₙ* α) = mul_hom.id α := rfl

variable {rγ : non_unital_non_assoc_semiring γ}
include rβ rγ

/-- Composition of non-unital ring homomorphisms is a non-unital ring homomorphism. -/
def comp (g : β →ₙ+* γ) (f : α →ₙ+* β) : α →ₙ+* γ :=
{ ..g.to_mul_hom.comp f.to_mul_hom, ..g.to_add_monoid_hom.comp f.to_add_monoid_hom }

/-- Composition of non-unital ring homomorphisms is associative. -/
lemma comp_assoc {δ} {rδ : non_unital_non_assoc_semiring δ} (f : α →ₙ+* β) (g : β →ₙ+* γ)
  (h : γ →ₙ+* δ) : (h.comp g).comp f = h.comp (g.comp f) := rfl

@[simp] lemma coe_comp (g : β →ₙ+* γ) (f : α →ₙ+* β) : ⇑(g.comp f) = g ∘ f := rfl
@[simp] lemma comp_apply (g : β →ₙ+* γ) (f : α →ₙ+* β) (x : α) : g.comp f x = g (f x) := rfl

@[simp] lemma coe_comp_add_monoid_hom (g : β →ₙ+* γ) (f : α →ₙ+* β) :
  (g.comp f : α →+ γ) = (g : β →+ γ).comp f := rfl
@[simp] lemma coe_comp_mul_hom (g : β →ₙ+* γ) (f : α →ₙ+* β) :
  (g.comp f : α →ₙ* γ) = (g : β →ₙ* γ).comp f := rfl

@[simp] lemma comp_zero (g : β →ₙ+* γ) : g.comp (0 : α →ₙ+* β) = 0 := by { ext, simp }
@[simp] lemma zero_comp (f : α →ₙ+* β) : (0 : β →ₙ+* γ).comp f = 0 := by { ext, refl }

omit rγ

@[simp] lemma comp_id (f : α →ₙ+* β) : f.comp (non_unital_ring_hom.id α) = f := ext $ λ x, rfl
@[simp] lemma id_comp (f : α →ₙ+* β) : (non_unital_ring_hom.id β).comp f = f := ext $ λ x, rfl

omit rβ

instance : monoid_with_zero (α →ₙ+* α) :=
{ one := non_unital_ring_hom.id α,
  mul := comp,
  mul_one := comp_id,
  one_mul := id_comp,
  mul_assoc := λ f g h, comp_assoc _ _ _,
  zero := 0,
  mul_zero := comp_zero,
  zero_mul := zero_comp }

lemma one_def : (1 : α →ₙ+* α) = non_unital_ring_hom.id α := rfl

@[simp] lemma coe_one : ⇑(1 : α →ₙ+* α) = id := rfl

lemma mul_def (f g : α →ₙ+* α) : f * g = f.comp g := rfl

@[simp] lemma coe_mul (f g : α →ₙ+* α) : ⇑(f * g) = f ∘ g := rfl

include rβ rγ

lemma cancel_right {g₁ g₂ : β →ₙ+* γ} {f : α →ₙ+* β} (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ext $ hf.forall.2 (ext_iff.1 h), λ h, h ▸ rfl⟩

lemma cancel_left {g : β →ₙ+* γ} {f₁ f₂ : α →ₙ+* β} (hg : injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, ext $ λ x, hg $ by rw [← comp_apply, h, comp_apply], λ h, h ▸ rfl⟩

omit rα rβ rγ

end non_unital_ring_hom

/-- Bundled semiring homomorphisms; use this for bundled ring homomorphisms too.

This extends from both `monoid_hom` and `monoid_with_zero_hom` in order to put the fields in a
sensible order, even though `monoid_with_zero_hom` already extends `monoid_hom`. -/
structure ring_hom (α : Type*) (β : Type*) [non_assoc_semiring α] [non_assoc_semiring β]
  extends α →* β, α →+ β, α →ₙ+* β, α →*₀ β

infixr ` →+* `:25 := ring_hom

/-- Reinterpret a ring homomorphism `f : α →+* β` as a monoid with zero homomorphism `α →*₀ β`.
The `simp`-normal form is `(f : α →*₀ β)`. -/
add_decl_doc ring_hom.to_monoid_with_zero_hom

/-- Reinterpret a ring homomorphism `f : α →+* β` as a monoid homomorphism `α →* β`.
The `simp`-normal form is `(f : α →* β)`. -/
add_decl_doc ring_hom.to_monoid_hom

/-- Reinterpret a ring homomorphism `f : α →+* β` as an additive monoid homomorphism `α →+ β`.
The `simp`-normal form is `(f : α →+ β)`. -/
add_decl_doc ring_hom.to_add_monoid_hom

/-- Reinterpret a ring homomorphism `f : α →+* β` as a non-unital ring homomorphism `α →ₙ+* β`. The
`simp`-normal form is `(f : α →ₙ+* β)`. -/
add_decl_doc ring_hom.to_non_unital_ring_hom

section ring_hom_class

/-- `ring_hom_class F α β` states that `F` is a type of (semi)ring homomorphisms.
You should extend this class when you extend `ring_hom`.

This extends from both `monoid_hom_class` and `monoid_with_zero_hom_class` in
order to put the fields in a sensible order, even though
`monoid_with_zero_hom_class` already extends `monoid_hom_class`. -/
class ring_hom_class (F : Type*) (α β : out_param Type*)
  [non_assoc_semiring α] [non_assoc_semiring β]
  extends monoid_hom_class F α β, add_monoid_hom_class F α β, monoid_with_zero_hom_class F α β

variables [non_assoc_semiring α] [non_assoc_semiring β] [ring_hom_class F α β]

/-- Ring homomorphisms preserve `bit1`. -/
@[simp] lemma map_bit1 (f : F) (a : α) : (f (bit1 a) : β) = bit1 (f a) := by simp [bit1]

instance : has_coe_t F (α →+* β) :=
⟨λ f, { to_fun := f, map_zero' := map_zero f, map_one' := map_one f, map_mul' := map_mul f,
  map_add' := map_add f }⟩

@[priority 100]
instance ring_hom_class.to_non_unital_ring_hom_class : non_unital_ring_hom_class F α β :=
{ .. ‹ring_hom_class F α β› }

end ring_hom_class

namespace ring_hom

section coe

/-!
Throughout this section, some `semiring` arguments are specified with `{}` instead of `[]`.
See note [implicit instance arguments].
-/
variables {rα : non_assoc_semiring α} {rβ : non_assoc_semiring β}

include rα rβ

instance : ring_hom_class (α →+* β) α β :=
{ coe := ring_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_add := ring_hom.map_add',
  map_zero := ring_hom.map_zero',
  map_mul := ring_hom.map_mul',
  map_one := ring_hom.map_one' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly.
-/
instance : has_coe_to_fun (α →+* β) (λ _, α → β) := ⟨ring_hom.to_fun⟩

initialize_simps_projections ring_hom (to_fun → apply)

@[simp] lemma to_fun_eq_coe (f : α →+* β) : f.to_fun = f := rfl

@[simp] lemma coe_mk (f : α → β) (h₁ h₂ h₃ h₄) : ⇑(⟨f, h₁, h₂, h₃, h₄⟩ : α →+* β) = f := rfl

@[simp] lemma coe_coe {F : Type*} [ring_hom_class F α β] (f : F) : ((f : α →+* β) : α → β) = f :=
rfl

instance has_coe_monoid_hom : has_coe (α →+* β) (α →* β) := ⟨ring_hom.to_monoid_hom⟩

@[simp, norm_cast] lemma coe_monoid_hom (f : α →+* β) : ⇑(f : α →* β) = f := rfl

@[simp] lemma to_monoid_hom_eq_coe (f : α →+* β) : f.to_monoid_hom = f := rfl
@[simp] lemma to_monoid_with_zero_hom_eq_coe (f : α →+* β) :
  (f.to_monoid_with_zero_hom : α → β) = f := rfl

@[simp] lemma coe_monoid_hom_mk (f : α → β) (h₁ h₂ h₃ h₄) :
  ((⟨f, h₁, h₂, h₃, h₄⟩ : α →+* β) : α →* β) = ⟨f, h₁, h₂⟩ := rfl

@[simp, norm_cast] lemma coe_add_monoid_hom (f : α →+* β) : ⇑(f : α →+ β) = f := rfl

@[simp] lemma to_add_monoid_hom_eq_coe (f : α →+* β) : f.to_add_monoid_hom = f := rfl

@[simp] lemma coe_add_monoid_hom_mk (f : α → β) (h₁ h₂ h₃ h₄) :
  ((⟨f, h₁, h₂, h₃, h₄⟩ : α →+* β) : α →+ β) = ⟨f, h₃, h₄⟩ := rfl

/-- Copy of a `ring_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
def copy (f : α →+* β) (f' : α → β) (h : f' = f) : α →+* β :=
{ ..f.to_monoid_with_zero_hom.copy f' h, ..f.to_add_monoid_hom.copy f' h }

end coe

variables [rα : non_assoc_semiring α] [rβ : non_assoc_semiring β]

section
include rα rβ

variables (f : α →+* β) {x y : α} {rα rβ}

lemma congr_fun {f g : α →+* β} (h : f = g) (x : α) : f x = g x := fun_like.congr_fun h x
lemma congr_arg (f : α →+* β) {x y : α} (h : x = y) : f x = f y := fun_like.congr_arg f h

lemma coe_inj ⦃f g : α →+* β⦄ (h : (f : α → β) = g) : f = g := fun_like.coe_injective h

@[ext] lemma ext ⦃f g : α →+* β⦄ : (∀ x, f x = g x) → f = g := fun_like.ext _ _

lemma ext_iff {f g : α →+* β} : f = g ↔ ∀ x, f x = g x := fun_like.ext_iff

@[simp] lemma mk_coe (f : α →+* β) (h₁ h₂ h₃ h₄) : ring_hom.mk f h₁ h₂ h₃ h₄ = f := ext $ λ _, rfl

lemma coe_add_monoid_hom_injective : injective (coe : (α →+* β) → (α →+ β)) :=
λ f g h, ext $ add_monoid_hom.congr_fun h

lemma coe_monoid_hom_injective : injective (coe : (α →+* β) → (α →* β)) :=
λ f g h, ext $ monoid_hom.congr_fun h

/-- Ring homomorphisms map zero to zero. -/
protected lemma map_zero (f : α →+* β) : f 0 = 0 := map_zero f

/-- Ring homomorphisms map one to one. -/
protected lemma map_one (f : α →+* β) : f 1 = 1 := map_one f

/-- Ring homomorphisms preserve addition. -/
protected lemma map_add (f : α →+* β) : ∀ a b, f (a + b) = f a + f b := map_add f

/-- Ring homomorphisms preserve multiplication. -/
protected lemma map_mul (f : α →+* β) : ∀ a b, f (a * b) = f a * f b := map_mul f

/-- Ring homomorphisms preserve `bit0`. -/
protected lemma map_bit0 (f : α →+* β) : ∀ a, f (bit0 a) = bit0 (f a) := map_bit0 f

/-- Ring homomorphisms preserve `bit1`. -/
protected lemma map_bit1 (f : α →+* β) : ∀ a, f (bit1 a) = bit1 (f a) := map_bit1 f

/-- `f : α →+* β` has a trivial codomain iff `f 1 = 0`. -/
lemma codomain_trivial_iff_map_one_eq_zero : (0 : β) = 1 ↔ f 1 = 0 := by rw [map_one, eq_comm]

/-- `f : α →+* β` has a trivial codomain iff it has a trivial range. -/
lemma codomain_trivial_iff_range_trivial : (0 : β) = 1 ↔ ∀ x, f x = 0 :=
f.codomain_trivial_iff_map_one_eq_zero.trans
  ⟨λ h x, by rw [←mul_one x, map_mul, h, mul_zero], λ h, h 1⟩

/-- `f : α →+* β` has a trivial codomain iff its range is `{0}`. -/
lemma codomain_trivial_iff_range_eq_singleton_zero : (0 : β) = 1 ↔ set.range f = {0} :=
f.codomain_trivial_iff_range_trivial.trans
  ⟨ λ h, set.ext (λ y, ⟨λ ⟨x, hx⟩, by simp [←hx, h x], λ hy, ⟨0, by simpa using hy.symm⟩⟩),
    λ h x, set.mem_singleton_iff.mp (h ▸ set.mem_range_self x)⟩

/-- `f : α →+* β` doesn't map `1` to `0` if `β` is nontrivial -/
lemma map_one_ne_zero [nontrivial β] : f 1 ≠ 0 :=
mt f.codomain_trivial_iff_map_one_eq_zero.mpr zero_ne_one

/-- If there is a homomorphism `f : α →+* β` and `β` is nontrivial, then `α` is nontrivial. -/
lemma domain_nontrivial [nontrivial β] : nontrivial α :=
⟨⟨1, 0, mt (λ h, show f 1 = 0, by rw [h, map_zero]) f.map_one_ne_zero⟩⟩

end

/-- Ring homomorphisms preserve additive inverse. -/
protected theorem map_neg [non_assoc_ring α] [non_assoc_ring β] (f : α →+* β) (x : α) :
  f (-x) = -(f x) :=
map_neg f x

/-- Ring homomorphisms preserve subtraction. -/
protected theorem map_sub [non_assoc_ring α] [non_assoc_ring β] (f : α →+* β) (x y : α) :
  f (x - y) = (f x) - (f y) := map_sub f x y

/-- Makes a ring homomorphism from a monoid homomorphism of rings which preserves addition. -/
def mk' [non_assoc_semiring α] [non_assoc_ring β] (f : α →* β)
  (map_add : ∀ a b, f (a + b) = f a + f b) :
  α →+* β :=
{ ..add_monoid_hom.mk' f map_add, ..f }

section semiring
variables [semiring α] [semiring β]

lemma is_unit_map (f : α →+* β) {a : α} : is_unit a → is_unit (f a) := is_unit.map f

protected lemma map_dvd (f : α →+* β) {a b : α} : a ∣ b → f a ∣ f b := map_dvd f

end semiring

/-- The identity ring homomorphism from a semiring to itself. -/
def id (α : Type*) [non_assoc_semiring α] : α →+* α := by refine {to_fun := id, ..}; intros; refl

include rα

instance : inhabited (α →+* α) := ⟨id α⟩

@[simp] lemma id_apply (x : α) : ring_hom.id α x = x := rfl
@[simp] lemma coe_add_monoid_hom_id : (id α : α →+ α) = add_monoid_hom.id α := rfl
@[simp] lemma coe_monoid_hom_id : (id α : α →* α) = monoid_hom.id α := rfl

variable {rγ : non_assoc_semiring γ}
include rβ rγ

/-- Composition of ring homomorphisms is a ring homomorphism. -/
def comp (g : β →+* γ) (f : α →+* β) : α →+* γ :=
{ to_fun := g ∘ f,
  map_one' := by simp,
  ..g.to_non_unital_ring_hom.comp f.to_non_unital_ring_hom }

/-- Composition of semiring homomorphisms is associative. -/
lemma comp_assoc {δ} {rδ: non_assoc_semiring δ} (f : α →+* β) (g : β →+* γ) (h : γ →+* δ) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

@[simp] lemma coe_comp (hnp : β →+* γ) (hmn : α →+* β) : (hnp.comp hmn : α → γ) = hnp ∘ hmn := rfl

lemma comp_apply (hnp : β →+* γ) (hmn : α →+* β) (x : α) : (hnp.comp hmn : α → γ) x =
  (hnp (hmn x)) := rfl

omit rγ

@[simp] lemma comp_id (f : α →+* β) : f.comp (id α) = f := ext $ λ x, rfl

@[simp] lemma id_comp (f : α →+* β) : (id β).comp f = f := ext $ λ x, rfl

omit rβ

instance : monoid (α →+* α) :=
{ one := id α,
  mul := comp,
  mul_one := comp_id,
  one_mul := id_comp,
  mul_assoc := λ f g h, comp_assoc _ _ _ }

lemma one_def : (1 : α →+* α) = id α := rfl
lemma mul_def (f g : α →+* α) : f * g = f.comp g := rfl

@[simp] lemma coe_one : ⇑(1 : α →+* α) = _root_.id := rfl
@[simp] lemma coe_mul (f g : α →+* α) : ⇑(f * g) = f ∘ g := rfl

include rβ rγ

lemma cancel_right {g₁ g₂ : β →+* γ} {f : α →+* β} (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ring_hom.ext $ hf.forall.2 (ext_iff.1 h), λ h, h ▸ rfl⟩

lemma cancel_left {g : β →+* γ} {f₁ f₂ : α →+* β} (hg : injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, ring_hom.ext $ λ x, hg $ by rw [← comp_apply, h, comp_apply], λ h, h ▸ rfl⟩

end ring_hom

/-- Pullback `is_domain` instance along an injective function. -/
protected theorem function.injective.is_domain [ring α] [is_domain α] [ring β] (f : β →+* α)
  (hf : injective f) :
  is_domain β :=
{ .. pullback_nonzero f f.map_zero f.map_one, .. hf.no_zero_divisors f f.map_zero f.map_mul }

namespace add_monoid_hom
variables [comm_ring α] [is_domain α] [comm_ring β] (f : β →+ α)

/-- Make a ring homomorphism from an additive group homomorphism from a commutative ring to an
integral domain that commutes with self multiplication, assumes that two is nonzero and `1` is sent
to `1`. -/
def mk_ring_hom_of_mul_self_of_two_ne_zero (h : ∀ x, f (x * x) = f x * f x) (h_two : (2 : α) ≠ 0)
  (h_one : f 1 = 1) : β →+* α :=
{ map_one' := h_one,
  map_mul' := λ x y, begin
    have hxy := h (x + y),
    rw [mul_add, add_mul, add_mul, f.map_add, f.map_add, f.map_add, f.map_add, h x, h y, add_mul,
      mul_add, mul_add, ← sub_eq_zero, add_comm, ← sub_sub, ← sub_sub, ← sub_sub,
      mul_comm y x, mul_comm (f y) (f x)] at hxy,
    simp only [add_assoc, add_sub_assoc, add_sub_cancel'_right] at hxy,
    rw [sub_sub, ← two_mul, ← add_sub_assoc, ← two_mul, ← mul_sub, mul_eq_zero, sub_eq_zero,
      or_iff_not_imp_left] at hxy,
    exact hxy h_two,
  end,
  ..f }

@[simp] lemma coe_fn_mk_ring_hom_of_mul_self_of_two_ne_zero (h h_two h_one) :
  (f.mk_ring_hom_of_mul_self_of_two_ne_zero h h_two h_one : β → α) = f := rfl

@[simp] lemma coe_add_monoid_hom_mk_ring_hom_of_mul_self_of_two_ne_zero (h h_two h_one) :
  (f.mk_ring_hom_of_mul_self_of_two_ne_zero h h_two h_one : β →+ α) = f :=
by { ext, refl }

end add_monoid_hom
