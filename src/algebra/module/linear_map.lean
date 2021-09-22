/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen
-/
import algebra.group.hom
import algebra.module.basic
import algebra.group_action_hom

/-!
# Linear maps

In this file we define

* `linear_map R M M₂`, `M →ₗ[R] M₂` : a linear map between two R-`module`s.

* `is_linear_map R f` : predicate saying that `f : M → M₂` is a linear map.

## Tags

linear map
-/

open function
open_locale big_operators

universes u u' v w x y z
variables {R : Type u} {k : Type u'} {S : Type v} {M : Type w} {M₂ : Type x} {M₃ : Type y}
  {ι : Type z}

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

/-- A map `f` between modules over a semiring is linear if it satisfies the two properties
`f (x + y) = f x + f y` and `f (c • x) = c • f x`. Elements of `linear_map R M M₂` (available under
the notation `M →ₗ[R] M₂`) are bundled versions of such maps. An unbundled version is available with
the predicate `is_linear_map`, but it should be avoided most of the time. -/
structure linear_map (R : Type u) (M : Type v) (M₂ : Type w)
  [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [module R M] [module R M₂]
  extends add_hom M M₂, M →[R] M₂

end

/-- The `add_hom` underlying a `linear_map`. -/
add_decl_doc linear_map.to_add_hom

/-- The `mul_action_hom` underlying a `linear_map`. -/
add_decl_doc linear_map.to_mul_action_hom

notation M ` →ₗ[`:25 R:25 `] `:0 M₂:0 := linear_map R M M₂

namespace linear_map

section add_comm_monoid

variables [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃]

section
variables [module R M] [module R M₂]

/-- The `distrib_mul_action_hom` underlying a `linear_map`. -/
def to_distrib_mul_action_hom (f : M →ₗ[R] M₂) : distrib_mul_action_hom R M M₂ :=
{ map_zero' := zero_smul R (0 : M) ▸ zero_smul R (f.to_fun 0) ▸ f.map_smul' 0 0, ..f }

instance : has_coe_to_fun (M →ₗ[R] M₂) (λ _, M → M₂) := ⟨to_fun⟩

initialize_simps_projections linear_map (to_fun → apply)

@[simp] lemma coe_mk (f : M → M₂) (h₁ h₂) :
  ((linear_map.mk f h₁ h₂ : M →ₗ[R] M₂) : M → M₂) = f := rfl


/-- Identity map as a `linear_map` -/
def id : M →ₗ[R] M :=
{ to_fun := id, ..distrib_mul_action_hom.id R }

lemma id_apply (x : M) :
  @id R M _ _ _ x = x := rfl

@[simp, norm_cast] lemma id_coe : ((linear_map.id : M →ₗ[R] M) : M → M) = _root_.id :=
by { ext x, refl }

end

section
variables [module R M] [module R M₂]
variables (f g : M →ₗ[R] M₂)

@[simp] lemma to_fun_eq_coe : f.to_fun = ⇑f := rfl

theorem is_linear : is_linear_map R f := ⟨f.map_add', f.map_smul'⟩

variables {f g}

theorem coe_injective : @injective (M →ₗ[R] M₂) (M → M₂) coe_fn :=
by rintro ⟨f, _⟩ ⟨g, _⟩ ⟨h⟩; congr

@[ext] theorem ext (H : ∀ x, f x = g x) : f = g :=
coe_injective $ funext H

protected lemma congr_arg : Π {x x' : M}, x = x' → f x = f x'
| _ _ rfl := rfl

/-- If two linear maps are equal, they are equal at each point. -/
protected lemma congr_fun (h : f = g) (x : M) : f x = g x := h ▸ rfl

theorem ext_iff : f = g ↔ ∀ x, f x = g x :=
⟨by { rintro rfl x, refl }, ext⟩

@[simp] lemma mk_coe (f : M →ₗ[R] M₂) (h₁ h₂) :
  (linear_map.mk f h₁ h₂ : M →ₗ[R] M₂) = f := ext $ λ _, rfl

variables (f g)

@[simp] lemma map_add (x y : M) : f (x + y) = f x + f y := f.map_add' x y

@[simp] lemma map_smul (c : R) (x : M) : f (c • x) = c • f x := f.map_smul' c x

@[simp] lemma map_zero : f 0 = 0 :=
f.to_distrib_mul_action_hom.map_zero

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
(map_smul : ∀ (f : M →ₗ[S] M₂) (c : R) (x : M), f (c • x) = c • f x)
variables {M M₂}

@[priority 100]
instance is_scalar_tower.compatible_smul
  {R S : Type*} [semiring S] [has_scalar R S]
  [has_scalar R M] [module S M] [is_scalar_tower R S M]
  [has_scalar R M₂] [module S M₂] [is_scalar_tower R S M₂] : compatible_smul M M₂ R S :=
⟨λ f c x, by rw [← smul_one_smul S c x, ← smul_one_smul S c (f x), map_smul]⟩

@[simp, priority 900]
lemma map_smul_of_tower {R S : Type*} [semiring S] [has_scalar R M]
  [module S M] [has_scalar R M₂] [module S M₂]
  [compatible_smul M M₂ R S] (f : M →ₗ[S] M₂) (c : R) (x : M) :
  f (c • x) = c • f x :=
compatible_smul.map_smul f c x

/-- convert a linear map to an additive map -/
def to_add_monoid_hom : M →+ M₂ :=
{ to_fun := f,
  map_zero' := f.map_zero,
  map_add' := f.map_add }

@[simp] lemma to_add_monoid_hom_coe : ⇑f.to_add_monoid_hom = f := rfl

section restrict_scalars

variables (R) [semiring S] [module S M] [module S M₂] [compatible_smul M M₂ R S]

/-- If `M` and `M₂` are both `R`-modules and `S`-modules and `R`-module structures
are defined by an action of `R` on `S` (formally, we have two scalar towers), then any `S`-linear
map from `M` to `M₂` is `R`-linear.

See also `linear_map.map_smul_of_tower`. -/
@[simps]
def restrict_scalars (f : M →ₗ[S] M₂) : M →ₗ[R] M₂ :=
{ to_fun := f,
  map_add' := f.map_add,
  map_smul' := f.map_smul_of_tower }

lemma restrict_scalars_injective :
  function.injective (restrict_scalars R : (M →ₗ[S] M₂) → (M →ₗ[R] M₂)) :=
λ f g h, ext (linear_map.congr_fun h : _)

@[simp]
lemma restrict_scalars_inj (f g : M →ₗ[S] M₂) :
  f.restrict_scalars R = g.restrict_scalars R ↔ f = g :=
(restrict_scalars_injective R).eq_iff

end restrict_scalars

variable {R}

@[simp] lemma map_sum {ι} {t : finset ι} {g : ι → M} :
  f (∑ i in t, g i) = (∑ i in t, f (g i)) :=
f.to_add_monoid_hom.map_sum _ _

theorem to_add_monoid_hom_injective :
  function.injective (to_add_monoid_hom : (M →ₗ[R] M₂) → (M →+ M₂)) :=
λ f g h, ext $ add_monoid_hom.congr_fun h

/-- If two `R`-linear maps from `R` are equal on `1`, then they are equal. -/
@[ext] theorem ext_ring {f g : R →ₗ[R] M} (h : f 1 = g 1) : f = g :=
ext $ λ x, by rw [← mul_one x, ← smul_eq_mul, f.map_smul, g.map_smul, h]

theorem ext_ring_iff {f g : R →ₗ[R] M} : f = g ↔ f 1 = g 1 :=
⟨λ h, h ▸ rfl, ext_ring⟩

end

section

variables {module_M : module R M} {module_M₂ : module R M₂}
{module_M₃ : module R M₃}
variables (f : M₂ →ₗ[R] M₃) (g : M →ₗ[R] M₂)

/-- Composition of two linear maps is a linear map -/
def comp : M →ₗ[R] M₃ :=
{ to_fun := f ∘ g, .. f.to_distrib_mul_action_hom.comp g.to_distrib_mul_action_hom }

infixr ` ∘ₗ `:80 := linear_map.comp

lemma comp_apply (x : M) : f.comp g x = f (g x) := rfl

@[simp, norm_cast] lemma coe_comp : (f.comp g : M → M₃) = f ∘ g := rfl

@[simp] theorem comp_id : f.comp id = f :=
linear_map.ext $ λ x, rfl

@[simp] theorem id_comp : id.comp f = f :=
linear_map.ext $ λ x, rfl

end

/-- If a function `g` is a left and right inverse of a linear map `f`, then `g` is linear itself. -/
def inverse [module R M] [module R M₂]
  (f : M →ₗ[R] M₂) (g : M₂ → M) (h₁ : left_inverse g f) (h₂ : right_inverse g f) :
  M₂ →ₗ[R] M :=
by dsimp [left_inverse, function.right_inverse] at h₁ h₂; exact
  { to_fun := g,
    map_add' := λ x y, by { rw [← h₁ (g (x + y)), ← h₁ (g x + g y)]; simp [h₂] },
    map_smul' := λ a b, by { rw [← h₁ (g (a • b)), ← h₁ (a • g b)]; simp [h₂] } }

end add_comm_monoid

section add_comm_group

variables [semiring R] [add_comm_group M] [add_comm_group M₂]
variables {module_M : module R M} {module_M₂ : module R M₂}
variables (f : M →ₗ[R] M₂)

@[simp] lemma map_neg (x : M) : f (- x) = - f x :=
f.to_add_monoid_hom.map_neg x

@[simp] lemma map_sub (x y : M) : f (x - y) = f x - f y :=
f.to_add_monoid_hom.map_sub x y

instance compatible_smul.int_module
  {S : Type*} [semiring S] [module S M] [module S M₂] : compatible_smul M M₂ ℤ S :=
⟨λ f c x, begin
  induction c using int.induction_on,
  case hz : { simp },
  case hp : n ih { simp [add_smul, ih] },
  case hn : n ih { simp [sub_smul, ih] }
end⟩

instance compatible_smul.units {R S : Type*}
  [monoid R] [mul_action R M] [mul_action R M₂] [semiring S] [module S M] [module S M₂]
  [compatible_smul M M₂ R S] :
  compatible_smul M M₂ (units R) S :=
⟨λ f c x, (compatible_smul.map_smul f (c : R) x : _)⟩

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
def to_linear_map (f : M →+[R] M₂) : M →ₗ[R] M₂ := { ..f }

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
`linear_map.endomorphism_semiring` and algebra structure `module.endomorphism_algebra`. -/
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
