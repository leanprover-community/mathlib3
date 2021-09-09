/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen
-/
import algebra.group.hom
import algebra.module.basic
import algebra.group_action_hom

/-!
# (Semi)linear maps and (semi)linear equivalences

In this file we define

* `linear_map σ M M₂`, `M →ₛₗ[σ] M₂` : a semilinear map between two `module`s. Here,
  `σ` is a `ring_hom` from `R` to `R₂` and an `f : M →ₛₗ[σ] M₂` satisfies
  `f (c • x) = (σ c) • (f x)`. We recover plain linear maps by choosing `σ` to be `ring_hom.id R`.
  This is denoted by `M →ₗ[R] M₂`.

* `is_linear_map R f` : predicate saying that `f : M → M₂` is a linear map. (Note that this
  was not generalized to semilinear maps.)

* `linear_equiv σ M ₂`, `M ≃ₛₗ[σ] M₂`: an invertible semilinear map. The plain linear version,
  with `σ` being `ring_hom.id R`, is denoted by `M ≃ₗ[R] M₂`.

## Implementation notes

To ensure that composition works smoothly for semilinear maps, we use the following typeclasses
  for `ring_hom`s defined in `algebra/ring/basic`:
* `ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃`, which states that `σ₁₃ = σ₂₃.comp σ₁₂`.
* `ring_hom_inv_pair σ σ'`, which state that `σ` and `σ'` are inverses of each other.
* `ring_hom_surjective σ`, which states that `σ` is surjective.
These typeclasses ensure that objects such as `σ₂₃.comp σ₁₂` never end up in the type of a
semilinear map; instead, the typeclass system directly finds the appropriate `ring_hom` to use.

## Tags

linear map, linear equiv, linear equivalences, linear isomorphism, linear isomorphic
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
`σ = ring_hom.id R`, the notation `M →ₗ[R] M₂` is available. An unbundled version of plain linear
maps is available with the predicate `is_linear_map`, but it should be avoided most of the time. -/
structure linear_map {R : Type*} {S : Type*} [semiring R] [semiring S]  (σ : R →+* S)
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

/-- The `mul_action_hom` underlying a `linear_map`. -/
def to_mul_action_hom (f : M →ₗ[R] M₂) : mul_action_hom R M M₂ := {..f}

/-- The `distrib_mul_action_hom` underlying a `linear_map`. -/
def to_distrib_mul_action_hom (f : M →ₗ[R] M₂) : distrib_mul_action_hom R M M₂ :=
{ map_zero' := zero_smul R (0 : M) ▸ zero_smul R (f.to_fun 0) ▸ f.map_smul' 0 0, ..f }

instance {σ : R →+* S} : has_coe_to_fun (M →ₛₗ[σ] M₃) := ⟨_, to_fun⟩

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

/-- If two `R`-linear maps from `R` are equal on `1`, then they are equal. -/
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

/-! ### Linear equivalences -/
section
set_option old_structure_cmd true

/-- A linear equivalence is an invertible linear map. -/
@[nolint has_inhabited_instance]
structure linear_equiv {R : Type*} {S : Type*} [semiring R] [semiring S] (σ : R →+* S)
  {σ' : S →+* R} [ring_hom_inv_pair σ σ'] [ring_hom_inv_pair σ' σ]
  (M : Type*) (M₂ : Type*)
  [add_comm_monoid M] [add_comm_monoid M₂] [module R M] [module S M₂]
  extends linear_map σ M M₂, M ≃+ M₂
end

attribute [nolint doc_blame] linear_equiv.to_linear_map
attribute [nolint doc_blame] linear_equiv.to_add_equiv

notation M ` ≃ₛₗ[`:50 σ `] ` M₂ := linear_equiv σ M M₂
notation M ` ≃ₗ[`:50 R `] ` M₂ := linear_equiv (ring_hom.id R) M M₂

namespace linear_equiv

section add_comm_monoid

variables {M₄ : Type*}
variables [semiring R] [semiring S]

section
variables [add_comm_monoid M] [add_comm_monoid M₁] [add_comm_monoid M₂]
variables [module R M] [module S M₂] {σ : R →+* S} {σ' : S →+* R}
variables [ring_hom_inv_pair σ σ'] [ring_hom_inv_pair σ' σ]

include R

include σ'
instance : has_coe (M ≃ₛₗ[σ] M₂) (M →ₛₗ[σ] M₂) := ⟨to_linear_map⟩
-- see Note [function coercion]
instance : has_coe_to_fun (M ≃ₛₗ[σ] M₂) := ⟨_, λ f, f.to_fun⟩

@[simp] lemma coe_mk {to_fun inv_fun map_add map_smul left_inv right_inv } :
  ⇑(⟨to_fun, map_add, map_smul, inv_fun, left_inv, right_inv⟩ : M ≃ₛₗ[σ] M₂) = to_fun :=
rfl

-- This exists for compatibility, previously `≃ₗ[R]` extended `≃` instead of `≃+`.
@[nolint doc_blame]
def to_equiv : (M ≃ₛₗ[σ] M₂) → M ≃ M₂ := λ f, f.to_add_equiv.to_equiv

lemma to_equiv_injective : function.injective (to_equiv : (M ≃ₛₗ[σ] M₂) → M ≃ M₂) :=
λ ⟨_, _, _, _, _, _⟩ ⟨_, _, _, _, _, _⟩ h, linear_equiv.mk.inj_eq.mpr (equiv.mk.inj h)

@[simp] lemma to_equiv_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : e₁.to_equiv = e₂.to_equiv ↔ e₁ = e₂ :=
to_equiv_injective.eq_iff

lemma to_linear_map_injective :
  function.injective (coe : (M ≃ₛₗ[σ] M₂) → (M →ₛₗ[σ] M₂)) :=
λ e₁ e₂ H, to_equiv_injective $ equiv.ext $ linear_map.congr_fun H

@[simp, norm_cast] lemma to_linear_map_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} :
  (e₁ : M →ₛₗ[σ] M₂) = e₂ ↔ e₁ = e₂ :=
to_linear_map_injective.eq_iff

end

section
variables [semiring R₁] [semiring R₂] [semiring R₃]
variables [add_comm_monoid M] [add_comm_monoid M₁] [add_comm_monoid M₂]
variables [add_comm_monoid M₃] [add_comm_monoid M₄]
variables [add_comm_monoid N₁] [add_comm_monoid N₂]
variables {module_M : module R M} {module_S_M₂ : module S M₂} {σ : R →+* S} {σ' : S →+* R}
variables {re₁ : ring_hom_inv_pair σ σ'} {re₂ : ring_hom_inv_pair σ' σ}
variables (e e' : M ≃ₛₗ[σ] M₂)

lemma to_linear_map_eq_coe : e.to_linear_map = (e : M →ₛₗ[σ] M₂) := rfl

@[simp, norm_cast] theorem coe_coe : ⇑(e : M →ₛₗ[σ] M₂) = e := rfl

@[simp] lemma coe_to_equiv : ⇑e.to_equiv = e := rfl

@[simp] lemma coe_to_linear_map : ⇑e.to_linear_map = e := rfl

@[simp] lemma to_fun_eq_coe : e.to_fun = e := rfl

section
variables {e e'}
@[ext] lemma ext (h : ∀ x, e x = e' x) : e = e' :=
to_equiv_injective (equiv.ext h)

protected lemma congr_arg : Π {x x' : M}, x = x' → e x = e x'
| _ _ rfl := rfl

protected lemma congr_fun (h : e = e') (x : M) : e x = e' x := h ▸ rfl

lemma ext_iff : e = e' ↔ ∀ x, e x = e' x :=
⟨λ h x, h ▸ rfl, ext⟩

end

section
variables (M R)

/-- The identity map is a linear equivalence. -/
@[refl]
def refl [module R M] : M ≃ₗ[R] M := { .. linear_map.id, .. equiv.refl M }

end

@[simp] lemma refl_apply [module R M] (x : M) : refl R M x = x := rfl

include module_M module_S_M₂ re₁ re₂
/-- Linear equivalences are symmetric. -/
@[symm]
def symm (e : M ≃ₛₗ[σ] M₂) : M₂ ≃ₛₗ[σ'] M :=
{ to_fun := e.to_linear_map.inverse e.inv_fun e.left_inv e.right_inv,
  inv_fun := e.to_equiv.symm.inv_fun,
  map_smul' := λ r x, by simp,
  .. e.to_linear_map.inverse e.inv_fun e.left_inv e.right_inv,
  .. e.to_equiv.symm }
omit module_M module_S_M₂ re₁ re₂

/-- See Note [custom simps projection] -/
def simps.symm_apply {R : Type*} {S : Type*} [semiring R] [semiring S] {σ : R →+* S}
  {σ' : S →+* R} [ring_hom_inv_pair σ σ'] [ring_hom_inv_pair σ' σ]
  {M : Type*} {M₂ : Type*} [add_comm_monoid M] [add_comm_monoid M₂] [module R M] [module S M₂]
  (e : M ≃ₛₗ[σ] M₂) : M₂ → M := e.symm

initialize_simps_projections linear_equiv (to_fun → apply, inv_fun → symm_apply)

include σ'
@[simp] lemma inv_fun_eq_symm : e.inv_fun = e.symm := rfl
omit σ'

variables {module_M₁ : module R₁ M₁} {module_M₂ : module R₂ M₂} {module_M₃ : module R₃ M₃}
variables {module_N₁ : module R₁ N₁} {module_N₂ : module R₁ N₂}
variables {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}
variables {σ₂₁ : R₂ →+* R₁} {σ₃₂ : R₃ →+* R₂} {σ₃₁ : R₃ →+* R₁}
variables [ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃]
variables [ring_hom_comp_triple σ₃₂ σ₂₁ σ₃₁]
variables {re₁₂ : ring_hom_inv_pair σ₁₂ σ₂₁} {re₂₃ : ring_hom_inv_pair σ₂₃ σ₃₂}
variables {re₁₃ : ring_hom_inv_pair σ₁₃ σ₃₁} {re₂₁ : ring_hom_inv_pair σ₂₁ σ₁₂}
variables {re₃₂ : ring_hom_inv_pair σ₃₂ σ₂₃} {re₃₁ : ring_hom_inv_pair σ₃₁ σ₁₃}
variables (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃)

include σ₃₁ re₁₃ re₃₁
/-- Linear equivalences are transitive. The linter thinks the `ring_hom_comp_triple` argument
is doubled -- it is not. -/
@[trans, nolint unused_arguments]
def trans : M₁ ≃ₛₗ[σ₁₃] M₃ :=
{ .. e₂₃.to_linear_map.comp e₁₂.to_linear_map,
  .. e₁₂.to_equiv.trans e₂₃.to_equiv }
omit σ₃₁ re₁₃ re₃₁

infixl ` ≪≫ₗ `:80 := @linear_equiv.trans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (ring_hom.id _) (ring_hom.id _) (ring_hom.id _)
  (ring_hom.id _) (ring_hom.id _) (ring_hom.id _)
  ring_hom_comp_triple.ids ring_hom_comp_triple.ids
  ring_hom_inv_pair.ids ring_hom_inv_pair.ids ring_hom_inv_pair.ids
  ring_hom_inv_pair.ids ring_hom_inv_pair.ids ring_hom_inv_pair.ids

variables {e₁₂} {e₂₃}

@[simp] lemma coe_to_add_equiv : ⇑(e.to_add_equiv) = e := rfl

/-- The two paths coercion can take to an `add_monoid_hom` are equivalent -/
lemma to_add_monoid_hom_commutes :
  e.to_linear_map.to_add_monoid_hom = e.to_add_equiv.to_add_monoid_hom :=
rfl

include σ₃₁ re₁₃ re₃₁
@[simp] theorem trans_apply (c : M₁) :
  (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃) c = e₂₃ (e₁₂ c) := rfl
omit σ₃₁ re₁₃ re₃₁

include σ'
@[simp] theorem apply_symm_apply (c : M₂) : e (e.symm c) = c := e.right_inv c
@[simp] theorem symm_apply_apply (b : M) : e.symm (e b) = b := e.left_inv b
omit σ'

include σ₃₁ σ₂₁ σ₃₂ re₁₃ re₃₁
@[simp] lemma symm_trans_apply
  (c : M₃) : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃).symm c = e₁₂.symm (e₂₃.symm c) := rfl
omit σ₃₁ σ₂₁ σ₃₂ re₁₃ re₃₁

@[simp] lemma trans_refl : e.trans (refl S M₂) = e := to_equiv_injective e.to_equiv.trans_refl
@[simp] lemma refl_trans : (refl R M).trans e = e := to_equiv_injective e.to_equiv.refl_trans

include σ'
lemma symm_apply_eq {x y} : e.symm x = y ↔ x = e y := e.to_equiv.symm_apply_eq

lemma eq_symm_apply {x y} : y = e.symm x ↔ e y = x := e.to_equiv.eq_symm_apply
omit σ'

@[simp] lemma refl_symm [module R M] : (refl R M).symm = linear_equiv.refl R M := rfl

@[simp] lemma trans_symm [module R M] [module R M₂] (f : M ≃ₗ[R] M₂) :
  f.trans f.symm = linear_equiv.refl R M :=
by { ext x, simp }

@[simp] lemma symm_trans [module R M] [module R M₂] (f : M ≃ₗ[R] M₂) :
  f.symm.trans f = linear_equiv.refl R M₂ :=
by { ext x, simp }

@[simp, norm_cast] lemma refl_to_linear_map [module R M] :
  (linear_equiv.refl R M : M →ₗ[R] M) = linear_map.id :=
rfl

instance : ring_hom_inv_pair (ring_hom.id R) (ring_hom.id R) := by apply_instance

@[simp, norm_cast]
lemma comp_coe [module R M] [module R M₂] [module R M₃] (f :  M ≃ₗ[R] M₂)
  (f' :  M₂ ≃ₗ[R] M₃) : (f' : M₂ →ₗ[R] M₃).comp (f : M →ₗ[R] M₂) = (f.trans f' : M ≃ₗ[R] M₃) :=
rfl

@[simp] lemma mk_coe (h₁ h₂ f h₃ h₄) :
  (linear_equiv.mk e h₁ h₂ f h₃ h₄ : M ≃ₛₗ[σ] M₂) = e := ext $ λ _, rfl

@[simp] theorem map_add (a b : M) : e (a + b) = e a + e b := e.map_add' a b
@[simp] theorem map_zero : e 0 = 0 := e.to_linear_map.map_zero
@[simp] theorem map_smulₛₗ (c : R) (x : M) : e (c • x) = (σ c) • e x := e.map_smul' c x

include module_N₁ module_N₂
theorem map_smul (e : N₁ ≃ₗ[R₁] N₂) (c : R₁) (x : N₁) :
  e (c • x) = c • e x := map_smulₛₗ _ _ _
omit module_N₁ module_N₂

@[simp] lemma map_sum {s : finset ι} (u : ι → M) : e (∑ i in s, u i) = ∑ i in s, e (u i) :=
e.to_linear_map.map_sum

@[simp] theorem map_eq_zero_iff {x : M} : e x = 0 ↔ x = 0 :=
e.to_add_equiv.map_eq_zero_iff
theorem map_ne_zero_iff {x : M} : e x ≠ 0 ↔ x ≠ 0 :=
e.to_add_equiv.map_ne_zero_iff

include module_M module_S_M₂ re₁ re₂
@[simp] theorem symm_symm (e : M ≃ₛₗ[σ] M₂): e.symm.symm = e :=
by { cases e, refl }
omit module_M module_S_M₂ re₁ re₂

lemma symm_bijective [module R M] [module S M₂] [ring_hom_inv_pair σ' σ]
  [ring_hom_inv_pair σ σ'] : function.bijective (symm : (M ≃ₛₗ[σ] M₂) → (M₂ ≃ₛₗ[σ'] M)) :=
equiv.bijective ⟨(symm : (M ≃ₛₗ[σ] M₂) →
  (M₂ ≃ₛₗ[σ'] M)), (symm : (M₂ ≃ₛₗ[σ'] M) → (M ≃ₛₗ[σ] M₂)), symm_symm, symm_symm⟩

@[simp] lemma mk_coe' (f h₁ h₂ h₃ h₄) : (linear_equiv.mk f h₁ h₂ ⇑e h₃ h₄ :
  M₂ ≃ₛₗ[σ'] M) = e.symm :=
symm_bijective.injective $ ext $ λ x, rfl

include σ'
@[simp] theorem symm_mk (f h₁ h₂ h₃ h₄) :
  (⟨e, h₁, h₂, f, h₃, h₄⟩ : M ≃ₛₗ[σ] M₂).symm =
  { to_fun := f, inv_fun := e,
    ..(⟨e, h₁, h₂, f, h₃, h₄⟩ : M ≃ₛₗ[σ] M₂).symm } := rfl
omit σ'

@[simp] lemma coe_symm_mk [module R M] [module R M₂]
  {to_fun inv_fun map_add map_smul left_inv right_inv} :
  ⇑((⟨to_fun, map_add, map_smul, inv_fun, left_inv, right_inv⟩ : M ≃ₗ[R] M₂).symm) = inv_fun :=
rfl

protected lemma bijective : function.bijective e := e.to_equiv.bijective
protected lemma injective : function.injective e := e.to_equiv.injective
protected lemma surjective : function.surjective e := e.to_equiv.surjective

include σ'
protected lemma image_eq_preimage (s : set M) : e '' s = e.symm ⁻¹' s :=
e.to_equiv.image_eq_preimage s
omit σ'

end

variables [semiring R₁] [semiring R₂] [semiring R₃]
variables [add_comm_monoid M] [add_comm_monoid M₁] [add_comm_monoid M₂]

/-- An involutive linear map is a linear equivalence. -/
def of_involutive {σ σ' : R →+* R} [ring_hom_inv_pair σ σ'] [ring_hom_inv_pair σ' σ]
  {module_M : module R M} (f : M →ₛₗ[σ] M) (hf : involutive f) :
  M ≃ₛₗ[σ] M :=
{ .. f, .. hf.to_equiv f }

@[simp] lemma coe_of_involutive {σ σ' : R →+* R} [ring_hom_inv_pair σ σ']
  [ring_hom_inv_pair σ' σ] {module_M : module R M} (f : M →ₛₗ[σ] M) (hf : involutive f) :
  ⇑(of_involutive f hf) = f :=
rfl

section restrict_scalars

variables (R) [module R M] [module R M₂] [module S M] [module S M₂]
  [linear_map.compatible_smul M M₂ R S]

/-- If `M` and `M₂` are both `R`-semimodules and `S`-semimodules and `R`-semimodule structures
are defined by an action of `R` on `S` (formally, we have two scalar towers), then any `S`-linear
equivalence from `M` to `M₂` is also an `R`-linear equivalence.

See also `linear_map.restrict_scalars`. -/
@[simps]
def restrict_scalars (f : M ≃ₗ[S] M₂) : M ≃ₗ[R] M₂ :=
{ to_fun := f,
  inv_fun := f.symm,
  left_inv := f.left_inv,
  right_inv := f.right_inv,
  .. f.to_linear_map.restrict_scalars R }

lemma restrict_scalars_injective :
  function.injective (restrict_scalars R : (M ≃ₗ[S] M₂) → (M ≃ₗ[R] M₂)) :=
λ f g h, ext (linear_equiv.congr_fun h : _)

@[simp]
lemma restrict_scalars_inj (f g : M ≃ₗ[S] M₂) :
  f.restrict_scalars R = g.restrict_scalars R ↔ f = g :=
(restrict_scalars_injective R).eq_iff

end restrict_scalars

end add_comm_monoid

end linear_equiv

namespace module

/-- `g : R ≃+* S` is `R`-linear when the module structure on `S` is `module.comp_hom S g` . -/
@[simps]
def comp_hom.to_linear_equiv {R S : Type*} [semiring R] [semiring S] (g : R ≃+* S) :
  (by haveI := comp_hom S (↑g : R →+* S); exact (R ≃ₗ[R] S)) :=
by exact {
  to_fun := (g : R → S),
  inv_fun := (g.symm : S → R),
  map_smul' := g.map_mul,
  ..g }

end module

namespace distrib_mul_action

variables (R M) [semiring R] [add_comm_monoid M] [module R M]

section
variables [monoid S] [distrib_mul_action S M] [smul_comm_class S R M]

/-- Each element of the monoid defines a linear map.

This is a stronger version of `distrib_mul_action.to_add_monoid_hom`. -/
@[simps]
def to_linear_map (s : S) : M →ₗ[R] M :=
{ to_fun := has_scalar.smul s,
  map_add' := smul_add s,
  map_smul' := λ a b, smul_comm _ _ _ }

end

section
variables [group S] [distrib_mul_action S M] [smul_comm_class S R M]

/-- Each element of the group defines a linear equivalence.

This is a stronger version of `distrib_mul_action.to_add_equiv`. -/
@[simps]
def to_linear_equiv (s : S) : M ≃ₗ[R] M :=
{ ..to_add_equiv _ _ s,
  ..to_linear_map R M s }

end

end distrib_mul_action
