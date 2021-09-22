/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen
-/
import algebra.group.hom
import algebra.module.basic
import algebra.module.pi
import algebra.group_action_hom

/-!
# Linear maps

In this file we define

* `linear_map R M M₂`, `M →ₗ[R] M₂` : a linear map between two R-`module`s.
* `is_linear_map R f` : predicate saying that `f : M → M₂` is a linear map.

We then provide `linear_map` with the following instances:

* `linear_map.add_comm_monoid` and `linear_map.add_comm_group`: the elementwise addition structures
  corresponding to addition in the codomain
* `linear_map.distrib_mul_action` and `linear_map.module`: the elementwise scalar action structures
  corresponding to applying the action in the codomain.
* `module.End.semiring` and `module.End.ring`: the (semi)ring of endomorphisms formed by taking the
  additive structure above with composition as multiplication.

## Tags

linear map
-/

open function
open_locale big_operators

universes u u' v w x y z
variables {R : Type u} {k : Type u'} {S : Type v} {T : Type*}
  {M : Type w} {M₂ : Type x} {M₃ : Type y} {N : Type*} {N₂ : Type*} {N₃ : Type*}
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

instance : has_coe_to_fun (M →ₗ[R] M₂) := ⟨_, to_fun⟩

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

namespace linear_map

variables [semiring R]
variables [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃]
variables [add_comm_group N] [add_comm_group N₂] [add_comm_group N₃]
variables [module R M] [module R M₂] [module R M₃]
variables [module R N] [module R N₂] [module R N₃]

/-! ### Arithmetic on the codomain -/
section arithmetic

/-- The constant 0 map is linear. -/
instance : has_zero (M →ₗ[R] M₂) :=
⟨{ to_fun := 0, map_add' := by simp, map_smul' := by simp }⟩

@[simp] lemma zero_apply (x : M) : (0 : M →ₗ[R] M₂) x = 0 := rfl

@[simp] theorem comp_zero (f : M →ₗ[R] M₂) : f.comp (0 : M₃ →ₗ[R] M) = 0 :=
ext $ assume c, by rw [comp_apply, zero_apply, zero_apply, f.map_zero]

@[simp] theorem zero_comp (f : M →ₗ[R] M₂) : (0 : M₂ →ₗ[R] M₃).comp f = 0 :=
rfl

instance : inhabited (M →ₗ[R] M₂) := ⟨0⟩

@[simp] lemma default_def : default (M →ₗ[R] M₂) = 0 := rfl

/-- The sum of two linear maps is linear. -/
instance : has_add (M →ₗ[R] M₂) :=
⟨λ f g, { to_fun := f + g,
          map_add' := by simp [add_comm, add_left_comm], map_smul' := by simp [smul_add] }⟩

@[simp] lemma add_apply (f g : M →ₗ[R] M₂) (x : M) : (f + g) x = f x + g x := rfl

lemma add_comp (f : M →ₗ[R] M₂) (g h : M₂ →ₗ[R] M₃) :
  (h + g).comp f = h.comp f + g.comp f := rfl

lemma comp_add (f g : M →ₗ[R] M₂) (h : M₂ →ₗ[R] M₃) :
  h.comp (f + g) = h.comp f + h.comp g := by { ext, simp }

/-- The type of linear maps is an additive monoid. -/
instance : add_comm_monoid (M →ₗ[R] M₂) :=
{ zero := 0,
  add := (+),
  add_assoc := by intros; ext; simp [add_comm, add_left_comm],
  zero_add := by intros; ext; simp [add_comm, add_left_comm],
  add_zero := by intros; ext; simp [add_comm, add_left_comm],
  add_comm := by intros; ext; simp [add_comm, add_left_comm],
  nsmul := λ n f, {
    to_fun := λ x, n • (f x),
    map_add' := λ x y, by rw [f.map_add, smul_add],
    map_smul' := λ c x, by rw [f.map_smul, smul_comm n c (f x)] },
  nsmul_zero' := λ f, by { ext x, simp },
  nsmul_succ' := λ n f, by { ext x, simp [nat.succ_eq_one_add, add_nsmul] } }

/-- The negation of a linear map is linear. -/
instance : has_neg (M →ₗ[R] N₂) :=
⟨λ f, { to_fun := -f, map_add' := by simp [add_comm], map_smul' := by simp }⟩

@[simp] lemma neg_apply (f : M →ₗ[R] N₂) (x : M) : (- f) x = - f x := rfl

@[simp] lemma neg_comp (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] N₃) : (- g).comp f = - g.comp f := rfl

@[simp] lemma comp_neg (f : M →ₗ[R] N₂) (g : N₂ →ₗ[R] N₃) : g.comp (- f) = - g.comp f :=
by { ext, simp }

/-- The negation of a linear map is linear. -/
instance : has_sub (M →ₗ[R] N₂) :=
⟨λ f g, { to_fun := f - g,
          map_add' := λ x y, by simp only [pi.sub_apply, map_add, add_sub_comm],
          map_smul' := λ r x, by simp only [pi.sub_apply, map_smul, smul_sub] }⟩

@[simp] lemma sub_apply (f g : M →ₗ[R] N₂) (x : M) : (f - g) x = f x - g x := rfl

lemma sub_comp (f : M →ₗ[R] M₂) (g h : M₂ →ₗ[R] N₃) :
  (g - h).comp f = g.comp f - h.comp f := rfl

lemma comp_sub (f g : M →ₗ[R] N₂) (h : N₂ →ₗ[R] N₃) :
  h.comp (g - f) = h.comp g - h.comp f := by { ext, simp }

/-- The type of linear maps is an additive group. -/
instance : add_comm_group (M →ₗ[R] N₂) :=
by refine
{ zero := 0,
  add := (+),
  neg := has_neg.neg,
  sub := has_sub.sub,
  sub_eq_add_neg := _,
  add_left_neg := _,
  nsmul := λ n f, {
    to_fun := λ x, n • (f x),
    map_add' := λ x y, by rw [f.map_add, smul_add],
    map_smul' := λ c x, by rw [f.map_smul, smul_comm n c (f x)] },
  gsmul := λ n f, {
    to_fun := λ x, n • (f x),
    map_add' := λ x y, by rw [f.map_add, smul_add],
    map_smul' := λ c x, by rw [f.map_smul, smul_comm n c (f x)] },
  gsmul_zero' := _,
  gsmul_succ' := _,
  gsmul_neg' := _,
  .. linear_map.add_comm_monoid };
intros; ext; simp [add_comm, add_left_comm, sub_eq_add_neg, add_smul, nat.succ_eq_add_one]

section has_scalar
variables [monoid S] [distrib_mul_action S M₂] [smul_comm_class R S M₂]
variables [monoid T] [distrib_mul_action T M₂] [smul_comm_class R T M₂]

instance : has_scalar S (M →ₗ[R] M₂) :=
⟨λ a f, { to_fun := a • f,
          map_add' := λ x y, by simp only [pi.smul_apply, f.map_add, smul_add],
          map_smul' := λ c x, by simp only [pi.smul_apply, f.map_smul, smul_comm c] }⟩

@[simp] lemma smul_apply (a : S) (f : M →ₗ[R] M₂) (x : M) : (a • f) x = a • f x := rfl

instance [smul_comm_class S T M₂] : smul_comm_class S T (M →ₗ[R] M₂) :=
⟨λ a b f, ext $ λ x, smul_comm _ _ _⟩

-- example application of this instance: if S -> T -> R are homomorphisms of commutative rings and
-- M and M₂ are R-modules then the S-module and T-module structures on Hom_R(M,M₂) are compatible.
instance [has_scalar S T] [is_scalar_tower S T M₂] : is_scalar_tower S T (M →ₗ[R] M₂) :=
{ smul_assoc := λ _ _ _, ext $ λ _, smul_assoc _ _ _ }

instance : distrib_mul_action S (M →ₗ[R] M₂) :=
{ one_smul := λ f, ext $ λ _, one_smul _ _,
  mul_smul := λ c c' f, ext $ λ _, mul_smul _ _ _,
  smul_add := λ c f g, ext $ λ x, smul_add _ _ _,
  smul_zero := λ c, ext $ λ x, smul_zero _ }

theorem smul_comp (a : S) (g : M₃ →ₗ[R] M₂) (f : M →ₗ[R] M₃) : (a • g).comp f = a • (g.comp f) :=
rfl

theorem comp_smul [distrib_mul_action S M₃] [smul_comm_class R S M₃] [compatible_smul M₃ M₂ S R]
  (g : M₃ →ₗ[R] M₂) (a : S) (f : M →ₗ[R] M₃) : g.comp (a • f) = a • (g.comp f) :=
ext $ λ x, g.map_smul_of_tower _ _

end has_scalar

section module
variables [semiring S] [module S M₂] [smul_comm_class R S M₂]

instance : module S (M →ₗ[R] M₂) :=
{ add_smul := λ a b f, ext $ λ x, add_smul _ _ _,
  zero_smul := λ f, ext $ λ x, zero_smul _ _ }

end module

end arithmetic

/-!
### Monoid structure of endomorphisms

Lemmas about `pow` such as `linear_map.pow_apply` appear in later files.
-/
section endomorphisms

instance : has_one (M →ₗ[R] M) := ⟨linear_map.id⟩
instance : has_mul (M →ₗ[R] M) := ⟨linear_map.comp⟩

lemma one_eq_id : (1 : M →ₗ[R] M) = id := rfl
lemma mul_eq_comp (f g : M →ₗ[R] M) : f * g = f.comp g := rfl

@[simp] lemma one_apply (x : M) : (1 : M →ₗ[R] M) x = x := rfl
@[simp] lemma mul_apply (f g : M →ₗ[R] M) (x : M) : (f * g) x = f (g x) := rfl

lemma coe_one : ⇑(1 : M →ₗ[R] M) = _root_.id := rfl
lemma coe_mul (f g : M →ₗ[R] M) : ⇑(f * g) = f ∘ g := rfl

instance _root_.module.End.monoid : monoid (M →ₗ[R] M) :=
by refine_struct { mul := (*), one := (1 : M →ₗ[R] M), npow := @npow_rec _ ⟨1⟩ ⟨(*)⟩ };
intros; try { refl }; apply linear_map.ext; simp {proj := ff}

instance _root_.module.End.semiring : semiring (M →ₗ[R] M) :=
{ mul := (*),
  one := (1 : M →ₗ[R] M),
  zero := 0,
  add := (+),
  npow := @npow_rec _ ⟨1⟩ ⟨(*)⟩,
  mul_zero := comp_zero,
  zero_mul := zero_comp,
  left_distrib := λ f g h, comp_add _ _ _,
  right_distrib := λ f g h, add_comp _ _ _,
  .. _root_.module.End.monoid,
  .. linear_map.add_comm_monoid }

instance _root_.module.End.ring : ring (N →ₗ[R] N) :=
{ ..module.End.semiring, ..linear_map.add_comm_group }

end endomorphisms

/-! ### Action by a `linear_map` -/

/-- The tautological action by `M →ₗ[R] M` on `M`.

This generalizes `function.End.apply_mul_action`. -/
instance apply_module : module (module.End R M) M :=
{ smul := ($),
  smul_zero := linear_map.map_zero,
  smul_add := linear_map.map_add,
  add_smul := linear_map.add_apply,
  zero_smul := (linear_map.zero_apply : ∀ m, (0 : M →ₗ[R] M) m = 0),
  one_smul := λ _, rfl,
  mul_smul := λ _ _ _, rfl }

@[simp] protected lemma smul_def (f : M →ₗ[R] M) (a : M) : f • a = f a := rfl

/-- `linear_map.apply_module` is faithful. -/
instance apply_has_faithful_scalar : has_faithful_scalar (module.End R M) M :=
⟨λ _ _, linear_map.ext⟩

instance apply_smul_comm_class : smul_comm_class R (module.End R M) M :=
{ smul_comm := λ r e m, (e.map_smul r m).symm }

instance apply_smul_comm_class' : smul_comm_class (module.End R M) R M :=
{ smul_comm := linear_map.map_smul }

end linear_map
