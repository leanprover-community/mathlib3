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
continuous. The set of continuous linear maps between the topological `α`-modules `β` and `γ` is
denoted by `β →L[α] γ`.

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
semimodule in which scalar multiplication is continuous. In applications, α will be a topological
semiring and β a topological additive semigroup, but this is not needed for the definition -/
class topological_semimodule (α : Type u) (β : Type v)
  [semiring α] [topological_space α]
  [topological_space β] [add_comm_monoid β]
  [semimodule α β] : Prop :=
(continuous_smul : continuous (λp : α × β, p.1 • p.2))
end prio

section

variables {α : Type u} {β : Type v}
[semiring α] [topological_space α]
[topological_space β] [add_comm_monoid β]
[semimodule α β] [topological_semimodule α β]

lemma continuous_smul : continuous (λp:α×β, p.1 • p.2) :=
topological_semimodule.continuous_smul α β

lemma continuous.smul {γ : Type*} [topological_space γ] {f : γ → α} {g : γ → β}
  (hf : continuous f) (hg : continuous g) : continuous (λp, f p • g p) :=
continuous_smul.comp (hf.prod_mk hg)

end

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A topological module, over a ring which is also a topological space, is a module in which
scalar multiplication is continuous. In applications, α will be a topological ring and β a
topological additive group, but this is not needed for the definition -/
class topological_module (α : Type u) (β : Type v)
  [ring α] [topological_space α]
  [topological_space β] [add_comm_group β]
  [module α β]
  extends topological_semimodule α β : Prop

/-- A topological vector space is a topological module over a field. -/
abbreviation topological_vector_space (α : Type u) (β : Type v)
  [discrete_field α] [topological_space α]
  [topological_space β] [add_comm_group β] [module α β] :=
topological_module α β
end prio

section

variables {α : Type*} {β : Type*}
[ring α] [topological_space α]
[topological_space β] [add_comm_group β]
[module α β] [topological_module α β]

/-- Scalar multiplication by a unit is a homeomorphism from a
topological module onto itself. -/
protected def homeomorph.smul_of_unit (a : units α) : β ≃ₜ β :=
{ to_fun    := λ x, (a : α) • x,
  inv_fun   := λ x, ((a⁻¹ : units α) : α) • x,
  right_inv := λ x, calc (a : α) • ((a⁻¹ : units α) : α) • x = x :
                 by rw [smul_smul, units.mul_inv, one_smul],
  left_inv  := λ x, calc ((a⁻¹ : units α) : α) • (a : α) • x = x :
                 by rw [smul_smul, units.inv_mul, one_smul],
  continuous_to_fun  := continuous_const.smul continuous_id,
  continuous_inv_fun := continuous_const.smul continuous_id }

lemma is_open_map_smul_of_unit (a : units α) : is_open_map (λ (x : β), (a : α) • x) :=
(homeomorph.smul_of_unit a).is_open_map

lemma is_closed_map_smul_of_unit (a : units α) : is_closed_map (λ (x : β), (a : α) • x) :=
(homeomorph.smul_of_unit a).is_closed_map

end

section

variables {α : Type*} {β : Type*} {a : α}
[discrete_field α] [topological_space α]
[topological_space β] [add_comm_group β]
[vector_space α β] [topological_vector_space α β]

set_option class.instance_max_depth 36

/-- Scalar multiplication by a non-zero field element is a
homeomorphism from a topological vector space onto itself. -/
protected def homeomorph.smul_of_ne_zero (ha : a ≠ 0) : β ≃ₜ β :=
{.. homeomorph.smul_of_unit ((equiv.units_equiv_ne_zero _).inv_fun ⟨_, ha⟩)}

lemma is_open_map_smul_of_ne_zero (ha : a ≠ 0) : is_open_map (λ (x : β), a • x) :=
(homeomorph.smul_of_ne_zero ha).is_open_map

lemma is_closed_map_smul_of_ne_zero (ha : a ≠ 0) : is_closed_map (λ (x : β), a • x) :=
(homeomorph.smul_of_ne_zero ha).is_closed_map

end

/-- Continuous linear maps between modules. We only put the type classes that are necessary for the
definition, although in applications β and γ will be topological modules over the topological
ring α -/
structure continuous_linear_map
  (α : Type*) [ring α]
  (β : Type*) [topological_space β] [add_comm_group β]
  (γ : Type*) [topological_space γ] [add_comm_group γ]
  [module α β] [module α γ]
  extends linear_map α β γ :=
(cont : continuous to_fun)

notation β ` →L[`:25 α `] ` γ := continuous_linear_map α β γ

namespace continuous_linear_map

section general_ring
/- Properties that hold for non-necessarily commutative rings. -/

variables
{α : Type*} [ring α]
{β : Type*} [topological_space β] [add_comm_group β]
{γ : Type*} [topological_space γ] [add_comm_group γ]
{δ : Type*} [topological_space δ] [add_comm_group δ]
[module α β] [module α γ] [module α δ]

/-- Coerce continuous linear maps to linear maps. -/
instance : has_coe (β →L[α] γ) (β →ₗ[α] γ) := ⟨to_linear_map⟩

protected lemma continuous (f : β →L[α] γ) : continuous f := f.2

/-- Coerce continuous linear maps to functions. -/
instance to_fun : has_coe_to_fun $ β →L[α] γ := ⟨_, λ f, f.to_fun⟩

@[ext] theorem ext {f g : β →L[α] γ} (h : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr' 1; ext x; apply h

theorem ext_iff {f g : β →L[α] γ} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, by rw h, by ext⟩

variables (c : α) (f g : β →L[α] γ) (h : γ →L[α] δ) (x y z : β)

-- make some straightforward lemmas available to `simp`.
@[simp] lemma map_zero : f (0 : β) = 0 := (to_linear_map _).map_zero
@[simp] lemma map_add  : f (x + y) = f x + f y := (to_linear_map _).map_add _ _
@[simp] lemma map_sub  : f (x - y) = f x - f y := (to_linear_map _).map_sub _ _
@[simp] lemma map_smul : f (c • x) = c • f x := (to_linear_map _).map_smul _ _
@[simp] lemma map_neg  : f (-x) = - (f x) := (to_linear_map _).map_neg _

@[simp, squash_cast] lemma coe_coe : ((f : β →ₗ[α] γ) : (β → γ)) = (f : β → γ) := rfl

/-- The continuous map that is constantly zero. -/
def zero : β →L[α] γ :=
⟨0, by exact continuous_const⟩

instance: has_zero (β →L[α] γ) := ⟨zero⟩

@[simp] lemma zero_apply : (0 : β →L[α] γ) x = 0 := rfl
@[simp, elim_cast] lemma coe_zero : ((0 : β →L[α] γ) : β →ₗ[α] γ) = 0 := rfl
/- no simp attribute on the next line as simp does not always simplify 0 x to x
when 0 is the zero function, while it does for the zero continuous linear map,
and this is the most important property we care about. -/
@[elim_cast] lemma coe_zero' : ((0 : β →L[α] γ) : β → γ) = 0 := rfl

/-- the identity map as a continuous linear map. -/
def id : β →L[α] β :=
⟨linear_map.id, continuous_id⟩

instance : has_one (β →L[α] β) := ⟨id⟩

@[simp] lemma id_apply : (id : β →L[α] β) x = x := rfl
@[simp, elim_cast] lemma coe_id : ((id : β →L[α] β) : β →ₗ[α] β) = linear_map.id := rfl
@[simp, elim_cast] lemma coe_id' : ((id : β →L[α] β) : β → β) = _root_.id := rfl

@[simp] lemma one_apply : (1 : β →L[α] β) x = x := rfl

section add
variables [topological_add_group γ]

instance : has_add (β →L[α] γ) :=
⟨λ f g, ⟨f + g, f.2.add g.2⟩⟩

@[simp] lemma add_apply : (f + g) x = f x + g x := rfl
@[simp, move_cast] lemma coe_add : (((f + g) : β →L[α] γ) : β →ₗ[α] γ) = (f : β →ₗ[α] γ) + g := rfl
@[move_cast] lemma coe_add' : (((f + g) : β →L[α] γ) : β → γ) = (f : β → γ) + g := rfl

instance : has_neg (β →L[α] γ) := ⟨λ f, ⟨-f, f.2.neg⟩⟩

@[simp] lemma neg_apply : (-f) x = - (f x) := rfl

@[simp, move_cast] lemma coe_neg : (((-f) : β →L[α] γ) : β →ₗ[α] γ) = -(f : β →ₗ[α] γ) := rfl
@[move_cast] lemma coe_neg' : (((-f) : β →L[α] γ) : β → γ) = -(f : β → γ) := rfl

instance : add_comm_group (β →L[α] γ) :=
by refine {zero := 0, add := (+), neg := has_neg.neg, ..};
   intros; ext; simp

@[simp] lemma sub_apply (x : β) : (f - g) x = f x - g x := rfl
@[simp, move_cast] lemma coe_sub : (((f - g) : β →L[α] γ) : β →ₗ[α] γ) = (f : β →ₗ[α] γ) - g := rfl
@[simp, move_cast] lemma coe_sub' : (((f - g) : β →L[α] γ) : β → γ) = (f : β → γ) - g := rfl

end add

/-- Composition of bounded linear maps. -/
def comp (g : γ →L[α] δ) (f : β →L[α] γ) : β →L[α] δ :=
⟨linear_map.comp g.to_linear_map f.to_linear_map, g.2.comp f.2⟩

@[simp, move_cast] lemma coe_comp : ((h.comp f) : (β →ₗ[α] δ)) = (h : γ →ₗ[α] δ).comp f := rfl
@[simp, move_cast] lemma coe_comp' : ((h.comp f) : (β → δ)) = (h : γ → δ) ∘ f := rfl

@[simp] theorem comp_id : f.comp id = f :=
ext $ λ x, rfl

@[simp] theorem id_comp : id.comp f = f :=
ext $ λ x, rfl

@[simp] theorem comp_zero : f.comp (0 : δ →L[α] β) = 0 :=
by { ext, simp }

@[simp] theorem zero_comp : (0 : γ →L[α] δ).comp f = 0 :=
by { ext, simp }

@[simp] lemma comp_add [topological_add_group γ] [topological_add_group δ]
  (g : γ →L[α] δ) (f₁ f₂ : β →L[α] γ) :
  g.comp (f₁ + f₂) = g.comp f₁ + g.comp f₂ :=
by { ext, simp }

@[simp] lemma add_comp [topological_add_group δ]
  (g₁ g₂ : γ →L[α] δ) (f : β →L[α] γ) :
  (g₁ + g₂).comp f = g₁.comp f + g₂.comp f :=
by { ext, simp }

instance : has_mul (β →L[α] β) := ⟨comp⟩

instance [topological_add_group β] : ring (β →L[α] β) :=
{ mul := (*),
  one := 1,
  mul_one := λ _, ext $ λ _, rfl,
  one_mul := λ _, ext $ λ _, rfl,
  mul_assoc := λ _ _ _, ext $ λ _, rfl,
  left_distrib := λ _ _ _, ext $ λ _, map_add _ _ _,
  right_distrib := λ _ _ _, ext $ λ _, linear_map.add_apply _ _ _,
  ..continuous_linear_map.add_comm_group }

/-- The cartesian product of two bounded linear maps, as a bounded linear map. -/
def prod (f₁ : β →L[α] γ) (f₂ : β →L[α] δ) : β →L[α] (γ × δ) :=
{ cont := f₁.2.prod_mk f₂.2,
  ..f₁.to_linear_map.prod f₂.to_linear_map }

end general_ring

section comm_ring

variables
{α : Type*} [comm_ring α] [topological_space α]
{β : Type*} [topological_space β] [add_comm_group β]
{γ : Type*} [topological_space γ] [add_comm_group γ]
{δ : Type*} [topological_space δ] [add_comm_group δ]
[module α β] [module α γ] [module α δ] [topological_module α δ]

instance : has_scalar α (β →L[α] δ) :=
⟨λ c f, ⟨c • f, continuous_const.smul f.2⟩⟩

variables (c : α) (h : γ →L[α] δ) (f g : β →L[α] γ) (x y z : β)

@[simp] lemma smul_comp : (c • h).comp f = c • (h.comp f) := rfl

variable [topological_module α γ]

@[simp] lemma smul_apply : (c • f) x = c • (f x) := rfl
@[simp, move_cast] lemma coe_apply : (((c • f) : β →L[α] γ) : β →ₗ[α] γ) = c • (f : β →ₗ[α] γ) := rfl
@[move_cast] lemma coe_apply' : (((c • f) : β →L[α] γ) : β → γ) = c • (f : β → γ) := rfl

@[simp] lemma comp_smul : h.comp (c • f) = c • (h.comp f) := by { ext, simp }

/-- The linear map `λ x, c x • f`.  Associates to a scalar-valued linear map and an element of
`γ` the `γ`-valued linear map obtained by multiplying the two (a.k.a. tensoring by `γ`) -/
def smul_right (c : β →L[α] α) (f : γ) : β →L[α] γ :=
{ cont := c.2.smul continuous_const,
  ..c.to_linear_map.smul_right f }

@[simp]
lemma smul_right_apply {c : β →L[α] α} {f : γ} {x : β} :
  (smul_right c f : β → γ) x = (c : β → α) x • f :=
rfl

@[simp]
lemma smul_right_one_one (c : α →L[α] γ) : smul_right 1 ((c : α → γ) 1) = c :=
by ext; simp [-continuous_linear_map.map_smul, (continuous_linear_map.map_smul _ _ _).symm]

@[simp]
lemma smul_right_one_eq_iff {f f' : γ} :
  smul_right (1 : α →L[α] α) f = smul_right 1 f' ↔ f = f' :=
⟨λ h, have (smul_right (1 : α →L[α] α) f : α → γ) 1 = (smul_right (1 : α →L[α] α) f' : α → γ) 1,
        by rw h,
      by simp at this; assumption,
  by cc⟩

variable [topological_add_group γ]

instance : module α (β →L[α] γ) :=
{ smul_zero := λ _, ext $ λ _, smul_zero _,
  zero_smul := λ _, ext $ λ _, zero_smul _ _,
  one_smul  := λ _, ext $ λ _, one_smul _ _,
  mul_smul  := λ _ _ _, ext $ λ _, mul_smul _ _ _,
  add_smul  := λ _ _ _, ext $ λ _, add_smul _ _ _,
  smul_add  := λ _ _ _, ext $ λ _, smul_add _ _ _ }

set_option class.instance_max_depth 55

instance : is_ring_hom (λ c : α, c • (1 : γ →L[α] γ)) :=
{ map_one := one_smul _ _,
  map_add := λ _ _, ext $ λ _, add_smul _ _ _,
  map_mul := λ _ _, ext $ λ _, mul_smul _ _ _ }

instance : algebra α (γ →L[α] γ) :=
{ to_fun    := λ c, c • 1,
  smul_def' := λ _ _, rfl,
  commutes' := λ _ _, ext $ λ _, map_smul _ _ _ }

end comm_ring

end continuous_linear_map
