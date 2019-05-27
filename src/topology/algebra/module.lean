/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo

Theory of topological modules and continuous linear maps.
-/

import topology.algebra.ring linear_algebra.basic ring_theory.algebra

open topological_space

universes u v w u'

/-- A topological semimodule, over a semiring which is also a topological space, is a
semimodule in which scalar multiplication is continuous. In applications, α will be a topological
semiring and β a topological additive semigroup, but this is not needed for the definition -/
class topological_semimodule (α : Type u) (β : Type v)
  [semiring α] [topological_space α]
  [topological_space β] [add_comm_monoid β]
  [semimodule α β] : Prop :=
(continuous_smul : continuous (λp : α × β, p.1 • p.2))

section

variables {α : Type u} {β : Type v}
[semiring α] [topological_space α]
[topological_space β] [add_comm_monoid β]
[semimodule α β] [topological_semimodule α β]

lemma continuous_smul' : continuous (λp:α×β, p.1 • p.2) :=
topological_semimodule.continuous_smul α β

lemma continuous_smul {γ : Type*} [topological_space γ] {f : γ → α} {g : γ → β}
  (hf : continuous f) (hg : continuous g) : continuous (λp, f p • g p) :=
continuous_smul'.comp (hf.prod_mk hg)

end

/-- A topological module, over a ring which is also a topological space, is a module in which
scalar multiplication is continuous. In applications, α will be a topological ring and β a
topological additive group, but this is not needed for the definition -/
class topological_module (α : Type u) (β : Type v)
  [ring α] [topological_space α]
  [topological_space β] [add_comm_group β]
  [module α β]
  extends topological_semimodule α β : Prop

class topological_vector_space (α : Type u) (β : Type v)
  [discrete_field α] [topological_space α]
  [topological_space β] [add_comm_group β] [vector_space α β]
  extends topological_module α β

/- Continuous linear maps between modules. Only put the type classes that are necessary for the
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
{α : Type*} [ring α] [topological_space α]
{β : Type*} [topological_space β] [add_comm_group β]
{γ : Type*} [topological_space γ] [add_comm_group γ]
{δ : Type*} [topological_space δ] [add_comm_group δ]
[module α β] [module α γ] [module α δ]

/-- Coerce continuous linear maps to linear maps. -/
instance : has_coe (β →L[α] γ) (β →ₗ[α] γ) := ⟨to_linear_map⟩

protected lemma continuous (f : β →L[α] γ) : continuous f := f.2

/-- Coerce continuous linear maps to functions. -/
instance to_fun : has_coe_to_fun $ β →L[α] γ := ⟨_, λ f, f.to_fun⟩

@[extensionality] theorem ext {f g : β →L[α] γ} (h : ∀ x, f x = g x) : f = g :=
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

@[simp] lemma coe_coe : ((f : β →ₗ[α] γ) : (β → γ)) = (f : β → γ) := rfl

/-- The continuous map that is constantly zero. -/
def zero : β →L[α] γ :=
⟨0, by exact continuous_const⟩

instance: has_zero (β →L[α] γ) := ⟨zero⟩

@[simp] lemma zero_apply : (0 : β →L[α] γ) x = 0 := rfl
@[simp] lemma coe_zero : ((0 : β →L[α] γ) : β →ₗ[α] γ) = 0 := rfl
/- no simp attribute on the next line as simp does not always simplify 0 x to x
when 0 is the zero function, while it does for the zero continuous linear map,
and this is the most important property we care about. -/
lemma coe_zero' : ((0 : β →L[α] γ) : β → γ) = 0 := rfl

/-- the identity map as a continuous linear map. -/
def id : β →L[α] β :=
⟨linear_map.id, continuous_id⟩

instance : has_one (β →L[α] β) := ⟨id⟩

@[simp] lemma id_apply : (id : β →L[α] β) x = x := rfl
@[simp] lemma coe_id : ((id : β →L[α] β) : β →ₗ[α] β) = linear_map.id := rfl
@[simp] lemma coe_id' : ((id : β →L[α] β) : β → β) = _root_.id := rfl

section add
variables [topological_add_group γ]

instance : has_add (β →L[α] γ) :=
⟨λ f g, ⟨f + g, continuous_add f.2 g.2⟩⟩

@[simp] lemma add_apply : (f + g) x = f x + g x := rfl
@[simp] lemma coe_add : ((f + g) : β →ₗ[α] γ) = (f : β →ₗ[α] γ) + g := rfl
@[simp] lemma coe_add' : ((f + g) : β → γ) = (f : β → γ) + g := rfl

set_option class.instance_max_depth 60

instance : has_neg (β →L[α] γ) := ⟨λ f, ⟨-f, continuous_neg f.2⟩⟩

@[simp] lemma neg_apply : (-f) x = - (f x) := rfl

@[simp] lemma coe_neg : ((-f) : β →ₗ[α] γ) = -(f : β →ₗ[α] γ) := rfl
@[simp] lemma coe_neg' : ((-f) : β → γ) = -(f : β → γ) := rfl

instance : add_comm_group (β →L[α] γ) :=
by refine {zero := 0, add := (+), neg := has_neg.neg, ..};
   intros; ext; simp

@[simp] lemma sub_apply (x : β) : (f - g) x = f x - g x := rfl
@[simp] lemma coe_sub : ((f - g) : β →ₗ[α] γ) = (f : β →ₗ[α] γ) - g := rfl
@[simp] lemma coe_sub' : ((f - g) : β → γ) = (f : β → γ) - g := rfl

end add

/-- Composition of bounded linear maps. -/
def comp (g : γ →L[α] δ) (f : β →L[α] γ) : β →L[α] δ :=
⟨linear_map.comp g.to_linear_map f.to_linear_map, g.2.comp f.2⟩

@[simp] lemma coe_comp : ((h.comp f) : (β →ₗ[α] δ)) = (h : γ →ₗ[α] δ).comp f := rfl
@[simp] lemma coe_comp' : ((h.comp f) : (β → δ)) = (h : γ → δ) ∘ f := rfl

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
{ cont := continuous.prod_mk f₁.2 f₂.2,
  ..f₁.to_linear_map.prod f₂.to_linear_map }

end general_ring

section comm_ring

variables
{α : Type*} [comm_ring α] [topological_space α]
{β : Type*} [topological_space β] [add_comm_group β]
{γ : Type*} [topological_space γ] [add_comm_group γ] [topological_add_group γ]
[module α β] [module α γ] [topological_module α γ]

instance : has_scalar α (β →L[α] γ) :=
⟨λ c f, ⟨c • f, continuous_smul continuous_const f.2⟩⟩

variables (c : α) (f g : β →L[α] γ) (x y z : β)

@[simp] lemma smul_apply : (c • f) x = c • (f x) := rfl
@[simp] lemma coe_apply : ((c • f) : β →ₗ[α] γ) = c • (f : β →ₗ[α] γ) := rfl
@[simp] lemma coe_apply' : ((c • f) : β → γ) = c • (f : β → γ) := rfl

instance : module α (β →L[α] γ) :=
{ smul_zero := λ _, ext $ λ _, smul_zero _,
  zero_smul := λ _, ext $ λ _, zero_smul _ _,
  one_smul  := λ _, ext $ λ _, one_smul _ _,
  mul_smul  := λ _ _ _, ext $ λ _, mul_smul _ _ _,
  add_smul  := λ _ _ _, ext $ λ _, add_smul _ _ _,
  smul_add  := λ _ _ _, ext $ λ _, smul_add _ _ _ }

set_option class.instance_max_depth 60

instance : is_ring_hom (λ c : α, c • (1 : γ →L[α] γ)) :=
{ map_one := one_smul _ _,
  map_add := λ _ _, ext $ λ _, add_smul _ _ _,
  map_mul := λ _ _, ext $ λ _, mul_smul _ _ _ }

instance : algebra α (γ →L[α] γ) :=
{ to_fun    := λ c, c • 1,
  smul_def' := λ _ _, rfl,
  commutes' := λ _ _, ext $ λ _, map_smul _ _ _ }

/-- Associating to a scalar-valued linear map and an element of `γ` the
`γ`-valued linear map obtained by multiplying the two (a.k.a. tensoring by `γ`) -/
def scalar_prod_space_iso (c : β →L[α] α) (f : γ) : β →L[α] γ :=
{ cont := continuous_smul c.2 continuous_const,
  ..c.to_linear_map.scalar_prod_space_iso f }

end comm_ring

section field

variables
{α : Type*} [discrete_field α] [topological_space α]
{β : Type*} [topological_space β] [add_comm_group β]
{γ : Type*} [topological_space γ] [add_comm_group γ] [topological_add_group γ]
[vector_space α β] [vector_space α γ] [topological_vector_space α γ]

instance : vector_space α (β →L[α] γ) := { ..continuous_linear_map.module }

end field

end continuous_linear_map
