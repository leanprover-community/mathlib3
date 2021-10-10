/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
import algebra.group.hom
import algebra.module.basic
import algebra.module.pi
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

We then provide `linear_map` with the following instances:

* `linear_map.add_comm_monoid` and `linear_map.add_comm_group`: the elementwise addition structures
  corresponding to addition in the codomain
* `linear_map.distrib_mul_action` and `linear_map.module`: the elementwise scalar action structures
  corresponding to applying the action in the codomain.
* `module.End.semiring` and `module.End.ring`: the (semi)ring of endomorphisms formed by taking the
  additive structure above with composition as multiplication.

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
variables {k : Type*} {S : Type*} {T : Type*}
variables {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variables {N₁ : Type*} {N₂ : Type*} {N₃ : Type*} {ι : Type*}

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

namespace linear_map

/-! ### Arithmetic on the codomain -/
section arithmetic

variables [semiring R₁] [semiring R₂] [semiring R₃]
variables [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃]
variables [add_comm_group N₁] [add_comm_group N₂] [add_comm_group N₃]
variables [module R₁ M] [module R₂ M₂] [module R₃ M₃]
variables [module R₁ N₁] [module R₂ N₂] [module R₃ N₃]
variables {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃} [ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃]

/-- The constant 0 map is linear. -/
instance : has_zero (M →ₛₗ[σ₁₂] M₂) :=
⟨{ to_fun := 0, map_add' := by simp, map_smul' := by simp }⟩

@[simp] lemma zero_apply (x : M) : (0 : M →ₛₗ[σ₁₂] M₂) x = 0 := rfl

@[simp] theorem comp_zero (g : M₂ →ₛₗ[σ₂₃] M₃) : (g.comp (0 : M →ₛₗ[σ₁₂] M₂) : M →ₛₗ[σ₁₃] M₃) = 0 :=
ext $ assume c, by rw [comp_apply, zero_apply, zero_apply, g.map_zero]

@[simp] theorem zero_comp (f : M →ₛₗ[σ₁₂] M₂) : ((0 : M₂ →ₛₗ[σ₂₃] M₃).comp f : M →ₛₗ[σ₁₃] M₃) = 0 :=
rfl

instance : inhabited (M →ₛₗ[σ₁₂] M₂) := ⟨0⟩

@[simp] lemma default_def : default (M →ₛₗ[σ₁₂] M₂) = 0 := rfl

/-- The sum of two linear maps is linear. -/
instance : has_add (M →ₛₗ[σ₁₂] M₂) :=
⟨λ f g, { to_fun := f + g,
          map_add' := by simp [add_comm, add_left_comm], map_smul' := by simp [smul_add] }⟩

@[simp] lemma add_apply (f g : M →ₛₗ[σ₁₂] M₂) (x : M) : (f + g) x = f x + g x := rfl

lemma add_comp (f : M →ₛₗ[σ₁₂] M₂) (g h : M₂ →ₛₗ[σ₂₃] M₃) :
  ((h + g).comp f : M →ₛₗ[σ₁₃] M₃) = h.comp f + g.comp f := rfl

lemma comp_add (f g : M →ₛₗ[σ₁₂] M₂) (h : M₂ →ₛₗ[σ₂₃] M₃) :
  (h.comp (f + g) : M →ₛₗ[σ₁₃] M₃) = h.comp f + h.comp g :=
ext $ λ _, h.map_add _ _

/-- The type of linear maps is an additive monoid. -/
instance : add_comm_monoid (M →ₛₗ[σ₁₂] M₂) :=
{ zero := 0,
  add := (+),
  add_assoc := λ f g h, linear_map.ext $ λ x, add_assoc _ _ _,
  zero_add := λ f, linear_map.ext $ λ x, zero_add _,
  add_zero := λ f, linear_map.ext $ λ x, add_zero _,
  add_comm := λ f g, linear_map.ext $ λ x, add_comm _ _,
  nsmul := λ n f,
  { to_fun := λ x, n • (f x),
    map_add' := λ x y, by rw [f.map_add, smul_add],
    map_smul' := λ c x,
    begin
      rw [f.map_smulₛₗ],
      simp [smul_comm n (σ₁₂ c) (f x)],
    end },
  nsmul_zero' := λ f, linear_map.ext $ λ x, add_comm_monoid.nsmul_zero' _,
  nsmul_succ' := λ n f, linear_map.ext $ λ x, add_comm_monoid.nsmul_succ' _ _ }

/-- The negation of a linear map is linear. -/
instance : has_neg (M →ₛₗ[σ₁₂] N₂) :=
⟨λ f, { to_fun := -f, map_add' := by simp [add_comm], map_smul' := by simp }⟩

@[simp] lemma neg_apply (f : M →ₛₗ[σ₁₂] N₂) (x : M) : (- f) x = - f x := rfl

include σ₁₃
@[simp] lemma neg_comp (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] N₃) : (- g).comp f = - g.comp f := rfl

@[simp] lemma comp_neg (f : M →ₛₗ[σ₁₂] N₂) (g : N₂ →ₛₗ[σ₂₃] N₃) : g.comp (- f) = - g.comp f :=
ext $ λ _, g.map_neg _
omit σ₁₃

/-- The negation of a linear map is linear. -/
instance : has_sub (M →ₛₗ[σ₁₂] N₂) :=
⟨λ f g, { to_fun := f - g,
          map_add' := λ x y, by simp only [pi.sub_apply, map_add, add_sub_comm],
          map_smul' := λ r x, by simp [pi.sub_apply, map_smul, smul_sub] }⟩

@[simp] lemma sub_apply (f g : M →ₛₗ[σ₁₂] N₂) (x : M) : (f - g) x = f x - g x := rfl

include σ₁₃
lemma sub_comp (f : M →ₛₗ[σ₁₂] M₂) (g h : M₂ →ₛₗ[σ₂₃] N₃) :
  (g - h).comp f = g.comp f - h.comp f := rfl

lemma comp_sub (f g : M →ₛₗ[σ₁₂] N₂) (h : N₂ →ₛₗ[σ₂₃] N₃) :
  h.comp (g - f) = h.comp g - h.comp f :=
ext $ λ _, h.map_sub _ _
omit σ₁₃

/-- The type of linear maps is an additive group. -/
instance : add_comm_group (M →ₛₗ[σ₁₂] N₂) :=
{ zero := 0,
  add := (+),
  neg := has_neg.neg,
  sub := has_sub.sub,
  sub_eq_add_neg := λ f g, linear_map.ext $ λ m, sub_eq_add_neg _ _,
  add_left_neg := λ f, linear_map.ext $ λ m, add_left_neg _,
  nsmul := λ n f, {
    to_fun := λ x, n • (f x),
    map_add' := λ x y, by rw [f.map_add, smul_add],
    map_smul' := λ c x, by rw [f.map_smulₛₗ, smul_comm n (σ₁₂ c) (f x)] },
  gsmul := λ n f, {
    to_fun := λ x, n • (f x),
    map_add' := λ x y, by rw [f.map_add, smul_add],
    map_smul' := λ c x, by rw [f.map_smulₛₗ, smul_comm n (σ₁₂ c) (f x)] },
  gsmul_zero' := λ a, linear_map.ext $ λ m, zero_smul _ _,
  gsmul_succ' := λ n a, linear_map.ext $ λ m, add_comm_group.gsmul_succ' n _,
  gsmul_neg' := λ n a, linear_map.ext $ λ m, add_comm_group.gsmul_neg' n _,
  .. linear_map.add_comm_monoid }

end arithmetic

-- TODO: generalize this section to semilinear maps where possible
section actions

variables [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃]
variables [module R M] [module R M₂] [module R M₃]

section has_scalar
variables [monoid S] [distrib_mul_action S M₂] [smul_comm_class R S M₂]
variables [monoid T] [distrib_mul_action T M₂] [smul_comm_class R T M₂]

instance : has_scalar S (M →ₗ[R] M₂) :=
⟨λ a f, { to_fun := a • f,
          map_add' := λ x y, by simp only [pi.smul_apply, f.map_add, smul_add],
          map_smul' := λ c x, by simp [pi.smul_apply, f.map_smul, smul_comm c] }⟩

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

end actions

/-!
### Monoid structure of endomorphisms

Lemmas about `pow` such as `linear_map.pow_apply` appear in later files.
-/
section endomorphisms

variables [semiring R] [add_comm_monoid M] [add_comm_group N₁] [module R M] [module R N₁]

instance : has_one (module.End R M) := ⟨linear_map.id⟩
instance : has_mul (module.End R M) := ⟨linear_map.comp⟩

lemma one_eq_id : (1 : module.End R M) = id := rfl
lemma mul_eq_comp (f g : module.End R M) : f * g = f.comp g := rfl

@[simp] lemma one_apply (x : M) : (1 : module.End R M) x = x := rfl
@[simp] lemma mul_apply (f g : module.End R M) (x : M) : (f * g) x = f (g x) := rfl

lemma coe_one : ⇑(1 : module.End R M) = _root_.id := rfl
lemma coe_mul (f g : module.End R M) : ⇑(f * g) = f ∘ g := rfl

instance _root_.module.End.monoid : monoid (module.End R M) :=
{ mul := (*),
  one := (1 : M →ₗ[R] M),
  mul_assoc := λ f g h, linear_map.ext $ λ x, rfl,
  mul_one := comp_id,
  one_mul := id_comp }

instance _root_.module.End.semiring : semiring (module.End R M) :=
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

instance _root_.module.End.ring : ring (module.End R N₁) :=
{ ..module.End.semiring, ..linear_map.add_comm_group }

section
variables [monoid S] [distrib_mul_action S M] [smul_comm_class R S M]

instance _root_.module.End.is_scalar_tower :
  is_scalar_tower S (module.End R M) (module.End R M) := ⟨smul_comp⟩

instance _root_.module.End.smul_comm_class [has_scalar S R] [is_scalar_tower S R M] :
  smul_comm_class S (module.End R M) (module.End R M) :=
⟨λ s _ _, (comp_smul _ s _).symm⟩

instance _root_.module.End.smul_comm_class' [has_scalar S R] [is_scalar_tower S R M] :
  smul_comm_class (module.End R M) S (module.End R M) :=
smul_comm_class.symm _ _ _

end

/-! ### Action by a module endomorphism. -/

/-- The tautological action by `module.End R M` (aka `M →ₗ[R] M`) on `M`.

This generalizes `function.End.apply_mul_action`. -/
instance apply_module : module (module.End R M) M :=
{ smul := ($),
  smul_zero := linear_map.map_zero,
  smul_add := linear_map.map_add,
  add_smul := linear_map.add_apply,
  zero_smul := (linear_map.zero_apply : ∀ m, (0 : M →ₗ[R] M) m = 0),
  one_smul := λ _, rfl,
  mul_smul := λ _ _ _, rfl }

@[simp] protected lemma smul_def (f : module.End R M) (a : M) : f • a = f a := rfl

/-- `linear_map.apply_module` is faithful. -/
instance apply_has_faithful_scalar : has_faithful_scalar (module.End R M) M :=
⟨λ _ _, linear_map.ext⟩

instance apply_smul_comm_class : smul_comm_class R (module.End R M) M :=
{ smul_comm := λ r e m, (e.map_smul r m).symm }

instance apply_smul_comm_class' : smul_comm_class (module.End R M) R M :=
{ smul_comm := linear_map.map_smul }

end endomorphisms

end linear_map
