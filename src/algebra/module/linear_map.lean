/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
import algebra.group.hom
import algebra.module.basic
import algebra.group_action_hom
import algebra.ring.comp_typeclasses

/-!
# (Semi)linear maps

In this file we define

* `linear_map σ M M₂`, `M →ₛₗ[σ] M₂` : a semilinear map between two `module`s. Here,
  `σ` is a `ring_hom` from `R` to `R₂` and an `f : M →ₛₗ[σ] M₂` satisfies
  `f (c • x) = (σ c) • (f x)`. We recover plain linear maps by choosing `σ` to be `ring_hom.id R`.
  This is denoted by `M →ₗ[R] M₂`.

* `is_linear_map R f` : predicate saying that `f : M → M₂` is a linear map. (Note that this
  was not generalized to semilinear maps.)

## Implementation notes

To ensure that composition works smoothly for semilinear maps, we use the typeclasses
`ring_hom_comp_triple`, `ring_hom_inv_pair` and `ring_hom_surjective` from
`algebra/ring/comp_typeclasses`.

## Notation

* Throughout the file, we denote regular linear maps by `fₗ`, `gₗ`, etc, and semilinear maps
  by `f`, `g`, etc.

## TODO

* Parts of this file have not yet been generalized to semilinear maps (i.e. `compatible_smul`)

## Tags

linear map
-/

open function
open_locale big_operators

universes u u' v w x y z
variables {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variables {k : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variables {N₁ : Type*} {N₂ : Type*} {N₃ : Type*} {N₄ : Type*} {ι : Type*}

/-- A map `f` between modules over a semiring is linear if it satisfies the two properties
`f (x + y) = f x + f y` and `f (c • x) = c • f x`. The predicate `is_linear_map R f` asserts this
property. A bundled version is available with `linear_map`, and should be favored over
`is_linear_map` most of the time. -/
structure is_linear_map (R : Type u) {M : Type v} {M₂ : Type w}
  [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [module R M] [module R M₂]
  (f : M → M₂) : Prop :=
(map_add : ∀ x y, f (x + y) = f x + f y)
(map_smul : ∀ (c : R) x, f (c • x) = c • f x)

section

set_option old_structure_cmd true

/-- A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`. Elements of `linear_map σ M M₂` (available under the notation
`M →ₛₗ[σ] M₂`) are bundled versions of such maps. For plain linear maps (i.e. for which
`σ = ring_hom.id R`), the notation `M →ₗ[R] M₂` is available. An unbundled version of plain linear
maps is available with the predicate `is_linear_map`, but it should be avoided most of the time. -/
structure linear_map {R : Type*} {S : Type*} [semiring R] [semiring S] (σ : R →+* S)
  (M : Type*) (M₂ : Type*)
  [add_comm_monoid M] [add_comm_monoid M₂] [module R M] [module S M₂]
  extends add_hom M M₂ :=
(map_smul' : ∀ (r : R) (x : M), to_fun (r • x) = (σ r) • to_fun x)

end

/-- The `add_hom` underlying a `linear_map`. -/
add_decl_doc linear_map.to_add_hom

notation M ` →ₛₗ[`:25 σ:25 `] `:0 M₂:0 := linear_map σ M M₂
notation M ` →ₗ[`:25 R:25 `] `:0 M₂:0 := linear_map (ring_hom.id R) M M₂

namespace linear_map

section add_comm_monoid

variables [semiring R] [semiring S]

section
variables [add_comm_monoid M] [add_comm_monoid M₁] [add_comm_monoid M₂] [add_comm_monoid M₃]
variables [add_comm_monoid N₁] [add_comm_monoid N₂] [add_comm_monoid N₃]
variables [module R M] [module R M₂] [module S M₃]

/-- The `distrib_mul_action_hom` underlying a `linear_map`. -/
def to_distrib_mul_action_hom (f : M →ₗ[R] M₂) : distrib_mul_action_hom R M M₂ :=
{ map_zero' := zero_smul R (0 : M) ▸ zero_smul R (f.to_fun 0) ▸ f.map_smul' 0 0, ..f }

instance {σ : R →+* S} : has_coe_to_fun (M →ₛₗ[σ] M₃) := ⟨_, to_fun⟩

initialize_simps_projections linear_map (to_fun → apply)

@[simp] lemma coe_mk {σ : R →+* S} (f : M → M₃) (h₁ h₂) :
  ⇑(linear_map.mk f h₁ h₂ : M →ₛₗ[σ] M₃) = f := rfl

/-- Identity map as a `linear_map` -/
def id : M →ₗ[R] M :=
{ to_fun := id, ..distrib_mul_action_hom.id R }

lemma id_apply (x : M) :
  @id R M _ _ _ x = x := rfl

@[simp, norm_cast] lemma id_coe : ((linear_map.id : M →ₗ[R] M) : M → M) = _root_.id :=
by { ext x, refl }

end

section
variables [add_comm_monoid M] [add_comm_monoid M₁] [add_comm_monoid M₂] [add_comm_monoid M₃]
variables [add_comm_monoid N₁] [add_comm_monoid N₂] [add_comm_monoid N₃]
variables [module R M] [module R M₂] [module S M₃]
variables (σ : R →+* S)
variables (fₗ gₗ : M →ₗ[R] M₂) (f g : M →ₛₗ[σ] M₃)

@[simp] lemma to_fun_eq_coe : f.to_fun = ⇑f := rfl

theorem is_linear : is_linear_map R fₗ := ⟨fₗ.map_add', fₗ.map_smul'⟩

variables {fₗ gₗ f g σ}

theorem coe_injective : @injective (M →ₛₗ[σ] M₃) (M → M₃) coe_fn :=
by rintro ⟨f, _⟩ ⟨g, _⟩ ⟨h⟩; congr

@[ext] theorem ext (H : ∀ x, f x = g x) : f = g :=
coe_injective $ funext H

protected lemma congr_arg : Π {x x' : M}, x = x' → f x = f x'
| _ _ rfl := rfl

/-- If two linear maps are equal, they are equal at each point. -/
protected lemma congr_fun (h : f = g) (x : M) : f x = g x := h ▸ rfl

theorem ext_iff : f = g ↔ ∀ x, f x = g x :=
⟨by { rintro rfl x, refl }, ext⟩

@[simp] lemma mk_coe (f : M →ₛₗ[σ] M₃) (h₁ h₂) :
  (linear_map.mk f h₁ h₂ : M →ₛₗ[σ] M₃) = f := ext $ λ _, rfl

variables (fₗ gₗ f g)

@[simp] lemma map_add (x y : M) : f (x + y) = f x + f y := f.map_add' x y

@[simp] lemma map_smulₛₗ (c : R) (x : M) : f (c • x) = (σ c) • f x := f.map_smul' c x

lemma map_smul (c : R) (x : M) : fₗ (c • x) = c • fₗ x := fₗ.map_smul' c x

lemma map_smul_inv {σ' : S →+* R} [ring_hom_inv_pair σ σ'] (c : S) (x : M) :
  c • f x = f (σ' c • x) :=
by simp

@[simp] lemma map_zero : f 0 = 0 :=
by { rw [←zero_smul R (0 : M), map_smulₛₗ], simp }

@[simp] lemma map_eq_zero_iff (h : function.injective f) {x : M} : f x = 0 ↔ x = 0 :=
⟨λ w, by { apply h, simp [w], }, λ w, by { subst w, simp, }⟩

variables (M M₂)
/--
A typeclass for `has_scalar` structures which can be moved through a `linear_map`.
This typeclass is generated automatically from a `is_scalar_tower` instance, but exists so that
we can also add an instance for `add_comm_group.int_module`, allowing `z •` to be moved even if
`R` does not support negation.
-/
class compatible_smul (R S : Type*) [semiring S] [has_scalar R M]
  [module S M] [has_scalar R M₂] [module S M₂] :=
(map_smul : ∀ (fₗ : M →ₗ[S] M₂) (c : R) (x : M), fₗ (c • x) = c • fₗ x)
variables {M M₂}

@[priority 100]
instance is_scalar_tower.compatible_smul
  {R S : Type*} [semiring S] [has_scalar R S]
  [has_scalar R M] [module S M] [is_scalar_tower R S M]
  [has_scalar R M₂] [module S M₂] [is_scalar_tower R S M₂] : compatible_smul M M₂ R S :=
⟨λ fₗ c x, by rw [← smul_one_smul S c x, ← smul_one_smul S c (fₗ x), map_smul]⟩

@[simp, priority 900]
lemma map_smul_of_tower {R S : Type*} [semiring S] [has_scalar R M]
  [module S M] [has_scalar R M₂] [module S M₂]
  [compatible_smul M M₂ R S] (fₗ : M →ₗ[S] M₂) (c : R) (x : M) :
  fₗ (c • x) = c • fₗ x :=
compatible_smul.map_smul fₗ c x

/-- convert a linear map to an additive map -/
def to_add_monoid_hom : M →+ M₃ :=
{ to_fun := f,
  map_zero' := f.map_zero,
  map_add' := f.map_add }

@[simp] lemma to_add_monoid_hom_coe : ⇑f.to_add_monoid_hom = f := rfl

section restrict_scalars

variables (R) [module S M] [module S M₂] [compatible_smul M M₂ R S]

/-- If `M` and `M₂` are both `R`-modules and `S`-modules and `R`-module structures
are defined by an action of `R` on `S` (formally, we have two scalar towers), then any `S`-linear
map from `M` to `M₂` is `R`-linear.

See also `linear_map.map_smul_of_tower`. -/
@[simps]
def restrict_scalars (fₗ : M →ₗ[S] M₂) : M →ₗ[R] M₂ :=
{ to_fun := fₗ,
  map_add' := fₗ.map_add,
  map_smul' := fₗ.map_smul_of_tower }

lemma restrict_scalars_injective :
  function.injective (restrict_scalars R : (M →ₗ[S] M₂) → (M →ₗ[R] M₂)) :=
λ fₗ gₗ h, ext (linear_map.congr_fun h : _)

@[simp]
lemma restrict_scalars_inj (fₗ gₗ : M →ₗ[S] M₂) :
  fₗ.restrict_scalars R = gₗ.restrict_scalars R ↔ fₗ = gₗ :=
(restrict_scalars_injective R).eq_iff

end restrict_scalars

variable {R}

@[simp] lemma map_sum {ι} {t : finset ι} {g : ι → M} :
  f (∑ i in t, g i) = (∑ i in t, f (g i)) :=
f.to_add_monoid_hom.map_sum _ _

theorem to_add_monoid_hom_injective :
  function.injective (to_add_monoid_hom : (M →ₛₗ[σ] M₃) → (M →+ M₃)) :=
λ f g h, ext $ add_monoid_hom.congr_fun h

/-- If two `σ`-linear maps from `R` are equal on `1`, then they are equal. -/
@[ext] theorem ext_ring {f g : R →ₛₗ[σ] M₃} (h : f 1 = g 1) : f = g :=
ext $ λ x, by rw [← mul_one x, ← smul_eq_mul, f.map_smulₛₗ, g.map_smulₛₗ, h]

theorem ext_ring_iff {σ : R →+* R} {f g : R →ₛₗ[σ] M} : f = g ↔ f 1 = g 1 :=
⟨λ h, h ▸ rfl, ext_ring⟩

end

section

variables [semiring R₁] [semiring R₂] [semiring R₃]
variables [add_comm_monoid M] [add_comm_monoid M₁] [add_comm_monoid M₂] [add_comm_monoid M₃]
variables {module_M₁ : module R₁ M₁} {module_M₂ : module R₂ M₂} {module_M₃ : module R₃ M₃}
variables {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}
variables [ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃]
variables (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₂] M₂)

include module_M₁ module_M₂ module_M₃
/-- Composition of two linear maps is a linear map -/
def comp : M₁ →ₛₗ[σ₁₃] M₃ :=
{ to_fun := f ∘ g,
  map_add' := by simp only [map_add, forall_const, eq_self_iff_true, comp_app],
  map_smul' := λ r x, by rw [comp_app, map_smulₛₗ, map_smulₛₗ, ring_hom_comp_triple.comp_apply] }
omit module_M₁ module_M₂ module_M₃

infixr ` ∘ₗ `:80 := @linear_map.comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (ring_hom.id _) (ring_hom.id _) (ring_hom.id _) ring_hom_comp_triple.ids

include σ₁₃
lemma comp_apply (x : M₁) : f.comp g x = f (g x) := rfl
omit σ₁₃

include σ₁₃
@[simp, norm_cast] lemma coe_comp : (f.comp g : M₁ → M₃) = f ∘ g := rfl
omit σ₁₃

@[simp] theorem comp_id : f.comp id = f :=
linear_map.ext $ λ x, rfl

@[simp] theorem id_comp : id.comp f = f :=
linear_map.ext $ λ x, rfl

end

variables [add_comm_monoid M] [add_comm_monoid M₁] [add_comm_monoid M₂] [add_comm_monoid M₃]

/-- If a function `g` is a left and right inverse of a linear map `f`, then `g` is linear itself. -/
def inverse [module R M] [module S M₂] {σ : R →+* S} {σ' : S →+* R} [ring_hom_inv_pair σ σ']
  (f : M →ₛₗ[σ] M₂) (g : M₂ → M) (h₁ : left_inverse g f) (h₂ : right_inverse g f) :
  M₂ →ₛₗ[σ'] M :=
by dsimp [left_inverse, function.right_inverse] at h₁ h₂; exact
  { to_fun := g,
    map_add' := λ x y, by { rw [← h₁ (g (x + y)), ← h₁ (g x + g y)]; simp [h₂] },
    map_smul' := λ a b, by { rw [← h₁ (g (a • b)), ← h₁ ((σ' a) • g b)], simp [h₂] } }

end add_comm_monoid

section add_comm_group

variables [semiring R] [semiring S] [add_comm_group M] [add_comm_group M₂]
variables {module_M : module R M} {module_M₂ : module S M₂} {σ : R →+* S}
variables (f : M →ₛₗ[σ] M₂)

@[simp] lemma map_neg (x : M) : f (- x) = - f x :=
f.to_add_monoid_hom.map_neg x

@[simp] lemma map_sub (x y : M) : f (x - y) = f x - f y :=
f.to_add_monoid_hom.map_sub x y

instance compatible_smul.int_module
  {S : Type*} [semiring S] [module S M] [module S M₂] : compatible_smul M M₂ ℤ S :=
⟨λ fₗ c x, begin
  induction c using int.induction_on,
  case hz : { simp },
  case hp : n ih { simp [add_smul, ih] },
  case hn : n ih { simp [sub_smul, ih] }
end⟩

instance compatible_smul.units {R S : Type*}
  [monoid R] [mul_action R M] [mul_action R M₂] [semiring S] [module S M] [module S M₂]
  [compatible_smul M M₂ R S] :
  compatible_smul M M₂ (units R) S :=
⟨λ fₗ c x, (compatible_smul.map_smul fₗ (c : R) x : _)⟩

end add_comm_group

end linear_map

namespace module

/-- `g : R →+* S` is `R`-linear when the module structure on `S` is `module.comp_hom S g` . -/
@[simps]
def comp_hom.to_linear_map {R S : Type*} [semiring R] [semiring S] (g : R →+* S) :
  (by haveI := comp_hom S g; exact (R →ₗ[R] S)) :=
by exact {
  to_fun := (g : R → S),
  map_add' := g.map_add,
  map_smul' := g.map_mul }

end module

namespace distrib_mul_action_hom

variables [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [module R M] [module R M₂]

/-- A `distrib_mul_action_hom` between two modules is a linear map. -/
def to_linear_map (fₗ : M →+[R] M₂) : M →ₗ[R] M₂ := { ..fₗ }

instance : has_coe (M →+[R] M₂) (M →ₗ[R] M₂) := ⟨to_linear_map⟩

@[simp] lemma to_linear_map_eq_coe (f : M →+[R] M₂) :
  f.to_linear_map = ↑f :=
rfl

@[simp, norm_cast] lemma coe_to_linear_map (f : M →+[R] M₂) :
  ((f : M →ₗ[R] M₂) : M → M₂) = f :=
rfl

lemma to_linear_map_injective {f g : M →+[R] M₂} (h : (f : M →ₗ[R] M₂) = (g : M →ₗ[R] M₂)) :
  f = g :=
by { ext m, exact linear_map.congr_fun h m, }

end distrib_mul_action_hom

namespace is_linear_map

section add_comm_monoid
variables [semiring R] [add_comm_monoid M] [add_comm_monoid M₂]
variables [module R M] [module R M₂]
include R

/-- Convert an `is_linear_map` predicate to a `linear_map` -/
def mk' (f : M → M₂) (H : is_linear_map R f) : M →ₗ[R] M₂ :=
{ to_fun := f, map_add' := H.1, map_smul' := H.2 }

@[simp] theorem mk'_apply {f : M → M₂} (H : is_linear_map R f) (x : M) :
  mk' f H x = f x := rfl

lemma is_linear_map_smul {R M : Type*} [comm_semiring R] [add_comm_monoid M] [module R M]
  (c : R) :
  is_linear_map R (λ (z : M), c • z) :=
begin
  refine is_linear_map.mk (smul_add c) _,
  intros _ _,
  simp only [smul_smul, mul_comm]
end

lemma is_linear_map_smul' {R M : Type*} [semiring R] [add_comm_monoid M] [module R M] (a : M) :
  is_linear_map R (λ (c : R), c • a) :=
is_linear_map.mk (λ x y, add_smul x y a) (λ x y, mul_smul x y a)

variables {f : M → M₂} (lin : is_linear_map R f)
include M M₂ lin

lemma map_zero : f (0 : M) = (0 : M₂) := (lin.mk' f).map_zero

end add_comm_monoid

section add_comm_group

variables [semiring R] [add_comm_group M] [add_comm_group M₂]
variables [module R M] [module R M₂]
include R

lemma is_linear_map_neg :
  is_linear_map R (λ (z : M), -z) :=
is_linear_map.mk neg_add (λ x y, (smul_neg x y).symm)

variables {f : M → M₂} (lin : is_linear_map R f)
include M M₂ lin

lemma map_neg (x : M) : f (- x) = - f x := (lin.mk' f).map_neg x

lemma map_sub (x y) : f (x - y) = f x - f y := (lin.mk' f).map_sub x y

end add_comm_group

end is_linear_map

/-- Linear endomorphisms of a module, with associated ring structure
`module.End.semiring` and algebra structure `module.End.algebra`. -/
abbreviation module.End (R : Type u) (M : Type v)
  [semiring R] [add_comm_monoid M] [module R M] := M →ₗ[R] M

/-- Reinterpret an additive homomorphism as a `ℕ`-linear map. -/
def add_monoid_hom.to_nat_linear_map [add_comm_monoid M] [add_comm_monoid M₂] (f : M →+ M₂) :
  M →ₗ[ℕ] M₂ :=
{ to_fun := f, map_add' := f.map_add, map_smul' := f.map_nat_module_smul }

lemma add_monoid_hom.to_nat_linear_map_injective [add_comm_monoid M] [add_comm_monoid M₂] :
  function.injective (@add_monoid_hom.to_nat_linear_map M M₂ _ _) :=
by { intros f g h, ext, exact linear_map.congr_fun h x }

/-- Reinterpret an additive homomorphism as a `ℤ`-linear map. -/
def add_monoid_hom.to_int_linear_map [add_comm_group M] [add_comm_group M₂] (f : M →+ M₂) :
  M →ₗ[ℤ] M₂ :=
{ to_fun := f, map_add' := f.map_add, map_smul' := f.map_int_module_smul }

lemma add_monoid_hom.to_int_linear_map_injective [add_comm_group M] [add_comm_group M₂] :
  function.injective (@add_monoid_hom.to_int_linear_map M M₂ _ _) :=
by { intros f g h, ext, exact linear_map.congr_fun h x }

@[simp] lemma add_monoid_hom.coe_to_int_linear_map [add_comm_group M] [add_comm_group M₂]
  (f : M →+ M₂) :
  ⇑f.to_int_linear_map = f := rfl

/-- Reinterpret an additive homomorphism as a `ℚ`-linear map. -/
def add_monoid_hom.to_rat_linear_map [add_comm_group M] [module ℚ M]
  [add_comm_group M₂] [module ℚ M₂] (f : M →+ M₂) :
  M →ₗ[ℚ] M₂ :=
{ map_smul' := f.map_rat_module_smul, ..f }

lemma add_monoid_hom.to_rat_linear_map_injective
  [add_comm_group M] [module ℚ M] [add_comm_group M₂] [module ℚ M₂] :
  function.injective (@add_monoid_hom.to_rat_linear_map M M₂ _ _ _ _) :=
by { intros f g h, ext, exact linear_map.congr_fun h x }

@[simp] lemma add_monoid_hom.coe_to_rat_linear_map [add_comm_group M] [module ℚ M]
  [add_comm_group M₂] [module ℚ M₂] (f : M →+ M₂) :
  ⇑f.to_rat_linear_map = f := rfl
