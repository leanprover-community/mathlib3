/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo

-/

import topology.algebra.ring linear_algebra.basic ring_theory.algebra

/-!
# Theory of topological modules and continuous linear maps.

We define classes `topological_semimodule`, `topological_module` and `topological_vector_spaces`,
as extensions of the corresponding algebraic classes where the algebraic operations are continuous.

We also define continuous linear maps, as linear maps between topological modules which are
continuous. The set of continuous linear maps between the topological `R`-modules `M` and `M₂` is
denoted by `M →L[R] M₂`.

Continuous linear equivalences are denoted by `M ≃L[R] M₂`.

## Implementation notes

Topological vector spaces are defined as an `abbreviation` for topological modules,
if the base ring is a field. This has as advantage that topological vector spaces are completely
transparent for type class inference, which means that all instances for topological modules
are immediately picked up for vector spaces as well.
A cosmetic disadvantage is that one can not extend topological vector spaces.
The solution is to extend `topological_module` instead.
-/

open topological_space

universes u v w u'

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A topological semimodule, over a semiring which is also a topological space, is a
semimodule in which scalar multiplication is continuous. In applications, R will be a topological
semiring and M a topological additive semigroup, but this is not needed for the definition -/
class topological_semimodule (R : Type u) (M : Type v)
  [semiring R] [topological_space R]
  [topological_space M] [add_comm_monoid M]
  [semimodule R M] : Prop :=
(continuous_smul : continuous (λp : R × M, p.1 • p.2))
end prio

section

variables {R : Type u} {M : Type v}
[semiring R] [topological_space R]
[topological_space M] [add_comm_monoid M]
[semimodule R M] [topological_semimodule R M]

lemma continuous_smul : continuous (λp:R×M, p.1 • p.2) :=
topological_semimodule.continuous_smul R M

lemma continuous.smul {M₂ : Type*} [topological_space M₂] {f : M₂ → R} {g : M₂ → M}
  (hf : continuous f) (hg : continuous g) : continuous (λp, f p • g p) :=
continuous_smul.comp (hf.prod_mk hg)

end

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A topological module, over a ring which is also a topological space, is a module in which
scalar multiplication is continuous. In applications, `R` will be a topological ring and `M` a
topological additive group, but this is not needed for the definition -/
class topological_module (R : Type u) (M : Type v)
  [ring R] [topological_space R]
  [topological_space M] [add_comm_group M]
  [module R M]
  extends topological_semimodule R M : Prop

/-- A topological vector space is a topological module over a field. -/
abbreviation topological_vector_space (R : Type u) (M : Type v)
  [discrete_field R] [topological_space R]
  [topological_space M] [add_comm_group M] [module R M] :=
topological_module R M
end prio

section

variables {R : Type*} {M : Type*}
[ring R] [topological_space R]
[topological_space M] [add_comm_group M]
[module R M] [topological_module R M]

/-- Scalar multiplication by a unit is a homeomorphism from a
topological module onto itself. -/
protected def homeomorph.smul_of_unit (a : units R) : M ≃ₜ M :=
{ to_fun    := λ x, (a : R) • x,
  inv_fun   := λ x, ((a⁻¹ : units R) : R) • x,
  right_inv := λ x, calc (a : R) • ((a⁻¹ : units R) : R) • x = x :
                 by rw [smul_smul, units.mul_inv, one_smul],
  left_inv  := λ x, calc ((a⁻¹ : units R) : R) • (a : R) • x = x :
                 by rw [smul_smul, units.inv_mul, one_smul],
  continuous_to_fun  := continuous_const.smul continuous_id,
  continuous_inv_fun := continuous_const.smul continuous_id }

lemma is_open_map_smul_of_unit (a : units R) : is_open_map (λ (x : M), (a : R) • x) :=
(homeomorph.smul_of_unit a).is_open_map

lemma is_closed_map_smul_of_unit (a : units R) : is_closed_map (λ (x : M), (a : R) • x) :=
(homeomorph.smul_of_unit a).is_closed_map

end

section

variables {R : Type*} {M : Type*} {a : R}
[discrete_field R] [topological_space R]
[topological_space M] [add_comm_group M]
[vector_space R M] [topological_vector_space R M]

set_option class.instance_max_depth 36

/-- Scalar multiplication by a non-zero field element is a
homeomorphism from a topological vector space onto itself. -/
protected def homeomorph.smul_of_ne_zero (ha : a ≠ 0) : M ≃ₜ M :=
{.. homeomorph.smul_of_unit ((equiv.units_equiv_ne_zero _).inv_fun ⟨_, ha⟩)}

lemma is_open_map_smul_of_ne_zero (ha : a ≠ 0) : is_open_map (λ (x : M), a • x) :=
(homeomorph.smul_of_ne_zero ha).is_open_map

lemma is_closed_map_smul_of_ne_zero (ha : a ≠ 0) : is_closed_map (λ (x : M), a • x) :=
(homeomorph.smul_of_ne_zero ha).is_closed_map

end

/-- Continuous linear maps between modules. We only put the type classes that are necessary for the
definition, although in applications `M` and `M₂` will be topological modules over the topological
ring `R`. -/
structure continuous_linear_map
  (R : Type*) [ring R]
  (M : Type*) [topological_space M] [add_comm_group M]
  (M₂ : Type*) [topological_space M₂] [add_comm_group M₂]
  [module R M] [module R M₂]
  extends linear_map R M M₂ :=
(cont : continuous to_fun)

notation M ` →L[`:25 R `] ` M₂ := continuous_linear_map R M M₂

/-- Continuous linear equivalences between modules. We only put the type classes that are necessary
for the definition, although in applications `M` and `M₂` will be topological modules over the
topological ring `R`. -/
structure continuous_linear_equiv
  (R : Type*) [ring R]
  (M : Type*) [topological_space M] [add_comm_group M]
  (M₂ : Type*) [topological_space M₂] [add_comm_group M₂]
  [module R M] [module R M₂]
  extends linear_equiv R M M₂ :=
(continuous_to_fun  : continuous to_fun)
(continuous_inv_fun : continuous inv_fun)

notation M ` ≃L[`:50 R `] ` M₂ := continuous_linear_equiv R M M₂

namespace continuous_linear_map

section general_ring
/- Properties that hold for non-necessarily commutative rings. -/

variables
{R : Type*} [ring R]
{M : Type*} [topological_space M] [add_comm_group M]
{M₂ : Type*} [topological_space M₂] [add_comm_group M₂]
{M₃ : Type*} [topological_space M₃] [add_comm_group M₃]
{M₄ : Type*} [topological_space M₄] [add_comm_group M₄]
[module R M] [module R M₂] [module R M₃] [module R M₄]

/-- Coerce continuous linear maps to linear maps. -/
instance : has_coe (M →L[R] M₂) (M →ₗ[R] M₂) := ⟨to_linear_map⟩

protected lemma continuous (f : M →L[R] M₂) : continuous f := f.2

/-- Coerce continuous linear maps to functions. -/
instance to_fun : has_coe_to_fun $ M →L[R] M₂ := ⟨_, λ f, f.to_fun⟩

@[ext] theorem ext {f g : M →L[R] M₂} (h : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr' 1; ext x; apply h

theorem ext_iff {f g : M →L[R] M₂} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, by rw h, by ext⟩

variables (c : R) (f g : M →L[R] M₂) (h : M₂ →L[R] M₃) (x y z : M)

-- make some straightforward lemmas available to `simp`.
@[simp] lemma map_zero : f (0 : M) = 0 := (to_linear_map _).map_zero
@[simp] lemma map_add  : f (x + y) = f x + f y := (to_linear_map _).map_add _ _
@[simp] lemma map_sub  : f (x - y) = f x - f y := (to_linear_map _).map_sub _ _
@[simp] lemma map_smul : f (c • x) = c • f x := (to_linear_map _).map_smul _ _
@[simp] lemma map_neg  : f (-x) = - (f x) := (to_linear_map _).map_neg _

@[simp, squash_cast] lemma coe_coe : ((f : M →ₗ[R] M₂) : (M → M₂)) = (f : M → M₂) := rfl

/-- The continuous map that is constantly zero. -/
def zero : M →L[R] M₂ :=
⟨0, by exact continuous_const⟩

instance: has_zero (M →L[R] M₂) := ⟨zero⟩
instance : inhabited (M →L[R] M₂) := ⟨0⟩

@[simp] lemma zero_apply : (0 : M →L[R] M₂) x = 0 := rfl
@[simp, elim_cast] lemma coe_zero : ((0 : M →L[R] M₂) : M →ₗ[R] M₂) = 0 := rfl
/- no simp attribute on the next line as simp does not always simplify `0 x` to `0`
when `0` is the zero function, while it does for the zero continuous linear map,
and this is the most important property we care about. -/
@[elim_cast] lemma coe_zero' : ((0 : M →L[R] M₂) : M → M₂) = 0 := rfl

/-- the identity map as a continuous linear map. -/
def id : M →L[R] M :=
⟨linear_map.id, continuous_id⟩

instance : has_one (M →L[R] M) := ⟨id⟩

@[simp] lemma id_apply : (id : M →L[R] M) x = x := rfl
@[simp, elim_cast] lemma coe_id : ((id : M →L[R] M) : M →ₗ[R] M) = linear_map.id := rfl
@[simp, elim_cast] lemma coe_id' : ((id : M →L[R] M) : M → M) = _root_.id := rfl

@[simp] lemma one_apply : (1 : M →L[R] M) x = x := rfl

section add
variables [topological_add_group M₂]

instance : has_add (M →L[R] M₂) :=
⟨λ f g, ⟨f + g, f.2.add g.2⟩⟩

@[simp] lemma add_apply : (f + g) x = f x + g x := rfl
@[simp, move_cast] lemma coe_add : (((f + g) : M →L[R] M₂) : M →ₗ[R] M₂) = (f : M →ₗ[R] M₂) + g := rfl
@[move_cast] lemma coe_add' : (((f + g) : M →L[R] M₂) : M → M₂) = (f : M → M₂) + g := rfl

instance : has_neg (M →L[R] M₂) := ⟨λ f, ⟨-f, f.2.neg⟩⟩

@[simp] lemma neg_apply : (-f) x = - (f x) := rfl

@[simp, move_cast] lemma coe_neg : (((-f) : M →L[R] M₂) : M →ₗ[R] M₂) = -(f : M →ₗ[R] M₂) := rfl
@[move_cast] lemma coe_neg' : (((-f) : M →L[R] M₂) : M → M₂) = -(f : M → M₂) := rfl

instance : add_comm_group (M →L[R] M₂) :=
by refine {zero := 0, add := (+), neg := has_neg.neg, ..};
   intros; ext; simp

@[simp] lemma sub_apply (x : M) : (f - g) x = f x - g x := rfl
@[simp, move_cast] lemma coe_sub : (((f - g) : M →L[R] M₂) : M →ₗ[R] M₂) = (f : M →ₗ[R] M₂) - g := rfl
@[simp, move_cast] lemma coe_sub' : (((f - g) : M →L[R] M₂) : M → M₂) = (f : M → M₂) - g := rfl

end add

/-- Composition of bounded linear maps. -/
def comp (g : M₂ →L[R] M₃) (f : M →L[R] M₂) : M →L[R] M₃ :=
⟨linear_map.comp g.to_linear_map f.to_linear_map, g.2.comp f.2⟩

@[simp, move_cast] lemma coe_comp : ((h.comp f) : (M →ₗ[R] M₃)) = (h : M₂ →ₗ[R] M₃).comp f := rfl
@[simp, move_cast] lemma coe_comp' : ((h.comp f) : (M → M₃)) = (h : M₂ → M₃) ∘ f := rfl

@[simp] theorem comp_id : f.comp id = f :=
ext $ λ x, rfl

@[simp] theorem id_comp : id.comp f = f :=
ext $ λ x, rfl

@[simp] theorem comp_zero : f.comp (0 : M₃ →L[R] M) = 0 :=
by { ext, simp }

@[simp] theorem zero_comp : (0 : M₂ →L[R] M₃).comp f = 0 :=
by { ext, simp }

@[simp] lemma comp_add [topological_add_group M₂] [topological_add_group M₃]
  (g : M₂ →L[R] M₃) (f₁ f₂ : M →L[R] M₂) :
  g.comp (f₁ + f₂) = g.comp f₁ + g.comp f₂ :=
by { ext, simp }

@[simp] lemma add_comp [topological_add_group M₃]
  (g₁ g₂ : M₂ →L[R] M₃) (f : M →L[R] M₂) :
  (g₁ + g₂).comp f = g₁.comp f + g₂.comp f :=
by { ext, simp }

theorem comp_assoc (h : M₃ →L[R] M₄) (g : M₂ →L[R] M₃) (f : M →L[R] M₂) :
  (h.comp g).comp f = h.comp (g.comp f) :=
rfl

instance : has_mul (M →L[R] M) := ⟨comp⟩

instance [topological_add_group M] : ring (M →L[R] M) :=
{ mul := (*),
  one := 1,
  mul_one := λ _, ext $ λ _, rfl,
  one_mul := λ _, ext $ λ _, rfl,
  mul_assoc := λ _ _ _, ext $ λ _, rfl,
  left_distrib := λ _ _ _, ext $ λ _, map_add _ _ _,
  right_distrib := λ _ _ _, ext $ λ _, linear_map.add_apply _ _ _,
  ..continuous_linear_map.add_comm_group }

/-- The cartesian product of two bounded linear maps, as a bounded linear map. -/
def prod (f₁ : M →L[R] M₂) (f₂ : M →L[R] M₃) : M →L[R] (M₂ × M₃) :=
{ cont := f₁.2.prod_mk f₂.2,
  ..f₁.to_linear_map.prod f₂.to_linear_map }

end general_ring

section comm_ring

variables
{R : Type*} [comm_ring R] [topological_space R]
{M : Type*} [topological_space M] [add_comm_group M]
{M₂ : Type*} [topological_space M₂] [add_comm_group M₂]
{M₃ : Type*} [topological_space M₃] [add_comm_group M₃]
[module R M] [module R M₂] [module R M₃] [topological_module R M₃]

instance : has_scalar R (M →L[R] M₃) :=
⟨λ c f, ⟨c • f, continuous_const.smul f.2⟩⟩

variables (c : R) (h : M₂ →L[R] M₃) (f g : M →L[R] M₂) (x y z : M)

@[simp] lemma smul_comp : (c • h).comp f = c • (h.comp f) := rfl

variable [topological_module R M₂]

@[simp] lemma smul_apply : (c • f) x = c • (f x) := rfl
@[simp, move_cast] lemma coe_apply : (((c • f) : M →L[R] M₂) : M →ₗ[R] M₂) = c • (f : M →ₗ[R] M₂) := rfl
@[move_cast] lemma coe_apply' : (((c • f) : M →L[R] M₂) : M → M₂) = c • (f : M → M₂) := rfl

@[simp] lemma comp_smul : h.comp (c • f) = c • (h.comp f) := by { ext, simp }

/-- The linear map `λ x, c x • f`.  Associates to a scalar-valued linear map and an element of
`M₂` the `M₂`-valued linear map obtained by multiplying the two (a.k.a. tensoring by `M₂`) -/
def smul_right (c : M →L[R] R) (f : M₂) : M →L[R] M₂ :=
{ cont := c.2.smul continuous_const,
  ..c.to_linear_map.smul_right f }

@[simp]
lemma smul_right_apply {c : M →L[R] R} {f : M₂} {x : M} :
  (smul_right c f : M → M₂) x = (c : M → R) x • f :=
rfl

@[simp]
lemma smul_right_one_one (c : R →L[R] M₂) : smul_right 1 ((c : R → M₂) 1) = c :=
by ext; simp [-continuous_linear_map.map_smul, (continuous_linear_map.map_smul _ _ _).symm]

@[simp]
lemma smul_right_one_eq_iff {f f' : M₂} :
  smul_right (1 : R →L[R] R) f = smul_right 1 f' ↔ f = f' :=
⟨λ h, have (smul_right (1 : R →L[R] R) f : R → M₂) 1 = (smul_right (1 : R →L[R] R) f' : R → M₂) 1,
        by rw h,
      by simp at this; assumption,
  by cc⟩

variable [topological_add_group M₂]

instance : module R (M →L[R] M₂) :=
{ smul_zero := λ _, ext $ λ _, smul_zero _,
  zero_smul := λ _, ext $ λ _, zero_smul _ _,
  one_smul  := λ _, ext $ λ _, one_smul _ _,
  mul_smul  := λ _ _ _, ext $ λ _, mul_smul _ _ _,
  add_smul  := λ _ _ _, ext $ λ _, add_smul _ _ _,
  smul_add  := λ _ _ _, ext $ λ _, smul_add _ _ _ }

set_option class.instance_max_depth 55

instance : is_ring_hom (λ c : R, c • (1 : M₂ →L[R] M₂)) :=
{ map_one := one_smul _ _,
  map_add := λ _ _, ext $ λ _, add_smul _ _ _,
  map_mul := λ _ _, ext $ λ _, mul_smul _ _ _ }

instance : algebra R (M₂ →L[R] M₂) :=
{ to_fun    := λ c, c • 1,
  smul_def' := λ _ _, rfl,
  commutes' := λ _ _, ext $ λ _, map_smul _ _ _ }

end comm_ring

end continuous_linear_map

namespace continuous_linear_equiv
variables {R : Type*} [ring R]
{M : Type*} [topological_space M] [add_comm_group M]
{M₂ : Type*} [topological_space M₂] [add_comm_group M₂]
{M₃ : Type*} [topological_space M₃] [add_comm_group M₃]
[module R M] [module R M₂] [module R M₃]

/-- A continuous linear equivalence induces a continuous linear map. -/
def to_continuous_linear_map (e : M ≃L[R] M₂) : M →L[R] M₂ :=
{ cont := e.continuous_to_fun,
  ..e.to_linear_equiv.to_linear_map }

/-- Coerce continuous linear equivs to continuous linear maps. -/
instance : has_coe (M ≃L[R] M₂) (M →L[R] M₂) := ⟨to_continuous_linear_map⟩

/-- Coerce continuous linear equivs to maps. -/
instance : has_coe_to_fun (M ≃L[R] M₂) := ⟨_, λ f, ((f : M →L[R] M₂) : M → M₂)⟩

@[simp] theorem coe_apply (e : M ≃L[R] M₂) (b : M) : (e : M →L[R] M₂) b = e b := rfl

@[squash_cast] lemma coe_coe (e : M ≃L[R] M₂) : ((e : M →L[R] M₂) : M → M₂) = e := rfl

@[ext] lemma ext {f g : M ≃L[R] M₂} (h : (f : M → M₂) = g) : f = g :=
begin
  cases f; cases g,
  simp only [],
  ext x,
  simp only [coe_fn_coe_base] at h,
  induction h,
  refl
end

/-- A continuous linear equivalence induces a homeomorphism. -/
def to_homeomorph (e : M ≃L[R] M₂) : M ≃ₜ M₂ := { ..e }

-- Make some straightforward lemmas available to `simp`.
@[simp] lemma map_zero (e : M ≃L[R] M₂) : e (0 : M) = 0 := (e : M →L[R] M₂).map_zero
@[simp] lemma map_add (e : M ≃L[R] M₂) (x y : M) : e (x + y) = e x + e y :=
(e : M →L[R] M₂).map_add x y
@[simp] lemma map_sub (e : M ≃L[R] M₂) (x y : M) : e (x - y) = e x - e y :=
(e : M →L[R] M₂).map_sub x y
@[simp] lemma map_smul (e : M ≃L[R] M₂) (c : R) (x : M) : e (c • x) = c • (e x) :=
(e : M →L[R] M₂).map_smul c x
@[simp] lemma map_neg (e : M ≃L[R] M₂) (x : M) : e (-x) = -e x := (e : M →L[R] M₂).map_neg x
@[simp] lemma map_eq_zero_iff (e : M ≃L[R] M₂) {x : M} : e x = 0 ↔ x = 0 :=
e.to_linear_equiv.map_eq_zero_iff

protected lemma continuous (e : M ≃L[R] M₂) : continuous (e : M → M₂) :=
e.continuous_to_fun

protected lemma continuous_on (e : M ≃L[R] M₂) {s : set M} : continuous_on (e : M → M₂) s :=
e.continuous.continuous_on

protected lemma continuous_at (e : M ≃L[R] M₂) {x : M} : continuous_at (e : M → M₂) x :=
e.continuous.continuous_at

protected lemma continuous_within_at (e : M ≃L[R] M₂) {s : set M} {x : M} :
  continuous_within_at (e : M → M₂) s x :=
e.continuous.continuous_within_at

lemma comp_continuous_on_iff
  {α : Type*} [topological_space α] (e : M ≃L[R] M₂) (f : α → M) (s : set α) :
  continuous_on (e ∘ f) s ↔ continuous_on f s :=
e.to_homeomorph.comp_continuous_on_iff _ _

lemma comp_continuous_iff
  {α : Type*} [topological_space α] (e : M ≃L[R] M₂) (f : α → M) :
  continuous (e ∘ f) ↔ continuous f :=
e.to_homeomorph.comp_continuous_iff _

section
variable (M)

/-- The identity map as a continuous linear equivalence. -/
@[refl] protected def refl : M ≃L[R] M :=
{ continuous_to_fun := continuous_id,
  continuous_inv_fun := continuous_id,
  .. linear_equiv.refl M }
end

/-- The inverse of a continuous linear equivalence as a continuous linear equivalence-/
@[symm] protected def symm (e : M ≃L[R] M₂) : M₂ ≃L[R] M :=
{ continuous_to_fun := e.continuous_inv_fun,
  continuous_inv_fun := e.continuous_to_fun,
  .. e.to_linear_equiv.symm }

@[simp] lemma symm_to_linear_equiv (e : M ≃L[R] M₂) :
  e.symm.to_linear_equiv = e.to_linear_equiv.symm :=
by { ext, refl }

/-- The composition of two continuous linear equivalences as a continuous linear equivalence. -/
@[trans] protected def trans (e₁ : M ≃L[R] M₂) (e₂ : M₂ ≃L[R] M₃) : M ≃L[R] M₃ :=
{ continuous_to_fun := e₂.continuous_to_fun.comp e₁.continuous_to_fun,
  continuous_inv_fun := e₁.continuous_inv_fun.comp e₂.continuous_inv_fun,
  .. e₁.to_linear_equiv.trans e₂.to_linear_equiv }

@[simp] lemma trans_to_linear_equiv (e₁ : M ≃L[R] M₂) (e₂ : M₂ ≃L[R] M₃) :
  (e₁.trans e₂).to_linear_equiv = e₁.to_linear_equiv.trans e₂.to_linear_equiv :=
by { ext, refl }

@[simp] theorem apply_symm_apply (e : M ≃L[R] M₂) (c : M₂) : e (e.symm c) = c := e.1.6 c
@[simp] theorem symm_apply_apply (e : M ≃L[R] M₂) (b : M) : e.symm (e b) = b := e.1.5 b

@[simp] theorem coe_comp_coe_symm (e : M ≃L[R] M₂) :
  (e : M →L[R] M₂).comp (e.symm : M₂ →L[R] M) = continuous_linear_map.id :=
continuous_linear_map.ext e.apply_symm_apply

@[simp] theorem coe_symm_comp_coe (e : M ≃L[R] M₂) :
  (e.symm : M₂ →L[R] M).comp (e : M →L[R] M₂) = continuous_linear_map.id :=
continuous_linear_map.ext e.symm_apply_apply

@[simp] lemma symm_comp_self (e : M ≃L[R] M₂) :
  (e.symm : M₂ → M) ∘ (e : M → M₂) = id :=
by{ ext x, exact symm_apply_apply e x }

@[simp] lemma self_comp_symm (e : M ≃L[R] M₂) :
  (e : M → M₂) ∘ (e.symm : M₂ → M) = id :=
by{ ext x, exact apply_symm_apply e x }

@[simp] theorem symm_symm (e : M ≃L[R] M₂) : e.symm.symm = e :=
by { ext x, refl }

@[simp] theorem symm_symm_apply (e : M ≃L[R] M₂) (x : M) : e.symm.symm x = e x :=
rfl

end continuous_linear_equiv
