/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.algebra.module
import geometry.manifold.smooth_map

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{H : Type*} [topological_space H]
{H' : Type*} [topological_space H']
{I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'}
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

namespace continuous_map

@[to_additive]
instance has_mul [has_continuous_mul β] : has_mul C(α, β) :=
⟨λ f g, ⟨f * g, continuous_mul.comp (f.continuous.prod_mk g.continuous)⟩⟩

@[to_additive]
instance {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [has_one β] : has_one C(α, β) := ⟨const (1 : β)⟩

end continuous_map

section group_structure

/-!
### Group stucture

In this section we show that continuous functions valued in a topological group inherit
a structure of group.
-/

section subtype

@[to_additive continuous_add_submonoid]
instance continuous_submonoid (α : Type u) (β : Type v) [topological_space α] [topological_space β]
  [monoid β] [topological_monoid β] : is_submonoid { f : α → β | continuous f } :=
{ one_mem := @continuous_const _ _ _ _ 1,
  mul_mem := λ f g fc gc, continuous.comp
  has_continuous_mul.continuous_mul (continuous.prod_mk fc gc) }.

@[to_additive continuous_add_subgroup]
instance continuous_subgroup (α : Type u) (β : Type v) [topological_space α] [topological_space β]
  [group β] [topological_group β] : is_subgroup { f : α → β | continuous f } :=
{ inv_mem := λ f fc, continuous.comp topological_group.continuous_inv fc,
  ..continuous_submonoid α β, }.

@[to_additive continuous_add_monoid]
instance continuous_monoid {α : Type u} {β : Type v} [topological_space α] [topological_space β]
  [monoid β] [topological_monoid β] : monoid { f : α → β | continuous f } :=
subtype.monoid

@[to_additive continuous_add_group]
instance continuous_group {α : Type u} {β : Type v} [topological_space α] [topological_space β]
  [group β] [topological_group β] : group { f : α → β | continuous f } :=
subtype.group

@[to_additive continuous_add_comm_group]
instance continuous_comm_group {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [comm_group β] [topological_group β] : comm_group { f : α → β | continuous f } :=
@subtype.comm_group _ _ _ (continuous_subgroup α β) -- infer_instance doesn't work?!

end subtype

section continuous_map

@[to_additive continuous_map_add_semigroup]
instance continuous_map_semigroup {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [semigroup β] [has_continuous_mul β] : semigroup C(α, β) :=
{ mul_assoc := λ a b c, by ext; exact mul_assoc _ _ _,
  ..continuous_map.has_mul}

@[to_additive continuous_map_add_monoid]
instance continuous_map_monoid {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [monoid β] [has_continuous_mul β] : monoid C(α, β) :=
{ one_mul := λ a, by ext; exact one_mul _,
  mul_one := λ a, by ext; exact mul_one _,
  ..continuous_map_semigroup,
  ..continuous_map.has_one }

@[to_additive continuous_map_add_comm_monoid]
instance continuous_map_comm_monoid {α : Type*} {β : Type*} [topological_space α]
[topological_space β] [comm_monoid β] [has_continuous_mul β] : comm_monoid C(α, β) :=
{ one_mul := λ a, by ext; exact one_mul _,
  mul_one := λ a, by ext; exact mul_one _,
  mul_comm := λ a b, by ext; exact mul_comm _ _,
  ..continuous_map_semigroup,
  ..continuous_map.has_one }

@[to_additive continuous_map_add_group]
instance continuous_map_group {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [group β] [topological_group β] : group C(α, β) :=
{ inv := λ f, ⟨λ x, (f x)⁻¹, continuous_inv.comp f.continuous⟩,
  mul_left_inv := λ a, by ext; exact mul_left_inv _,
  ..continuous_map_monoid }

@[to_additive continuous_map_add_comm_group]
instance continuous_map_comm_group {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [comm_group β] [topological_group β] : comm_group C(α, β) :=
{ ..continuous_map_group,
  ..continuous_map_comm_monoid }

end continuous_map

end group_structure

section ring_structure

/-!
### Ring stucture

In this section we show that continuous functions valued in a topological ring `R` inherit
a structure of ring.
-/

section subtype

instance continuous_subring (α : Type u) (R : Type v) [topological_space α] [topological_space R]
  [ring R] [topological_ring R] : is_subring { f : α → R | continuous f } :=
{ ..continuous_add_subgroup α R,
  ..continuous_submonoid α R }.

instance continuous_ring {α : Type u} {R : Type v} [topological_space α] [topological_space R]
  [ring R] [topological_ring R] : ring { f : α → R | continuous f } :=
@subtype.ring _ _ _ (continuous_subring α R) -- infer_instance doesn't work?!

instance continuous_comm_ring {α : Type u} {R : Type v} [topological_space α] [topological_space R]
  [comm_ring R] [topological_ring R] : comm_ring { f : α → R | continuous f } :=
@subtype.comm_ring _ _ _ (continuous_subring α R) -- infer_instance doesn't work?!

end subtype

section continuous_map

instance continuous_map_semiring {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [semiring β] [topological_semiring β] : semiring C(α, β) :=
{ left_distrib := λ a b c, by ext; exact left_distrib _ _ _,
  right_distrib := λ a b c, by ext; exact right_distrib _ _ _,
  zero_mul := λ a, by ext; exact zero_mul _,
  mul_zero := λ a, by ext; exact mul_zero _,
  ..continuous_map_add_comm_monoid,
  ..continuous_map_monoid }

instance continuous_map_ring {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [ring β] [topological_ring β] : ring C(α, β) :=
{ ..continuous_map_semiring,
  ..continuous_map_add_comm_group, }

instance continuous_map_comm_ring {α : Type*} {β : Type*} [topological_space α]
[topological_space β] [comm_ring β] [topological_ring β] : comm_ring C(α, β) :=
{ ..continuous_map_semiring,
  ..continuous_map_add_comm_group,
  ..continuous_map_comm_monoid,}

end continuous_map

end ring_structure

local attribute [ext] subtype.eq

section semimodule_structure

/-!
### Semiodule stucture

In this section we show that continuous functions valued in a topological semimodule `M` over a
topological semiring `R` inherit a structure of semimodule.
-/

section subtype

instance coninuous_has_scalar {α : Type*} [topological_space α]
  (R : Type*) [semiring R] [topological_space R]
  (M : Type*) [topological_space M] [add_comm_group M]
  [semimodule R M] [topological_semimodule R M] :
  has_scalar R { f : α → M | continuous f } :=
⟨λ r f, ⟨r • f, continuous_const.smul f.property⟩⟩

instance continuous_semimodule {α : Type*} [topological_space α]
{R : Type*} [semiring R] [topological_space R]
{M : Type*} [topological_space M] [add_comm_group M] [topological_add_group M]
[semimodule R M] [topological_semimodule R M] :
  semimodule R { f : α → M | continuous f } :=
  semimodule.of_core $
{ smul     := (•),
  smul_add := λ c f g, by ext x; exact smul_add c (f x) (g x),
  add_smul := λ c₁ c₂ f, by ext x; exact add_smul c₁ c₂ (f x),
  mul_smul := λ c₁ c₂ f, by ext x; exact mul_smul c₁ c₂ (f x),
  one_smul := λ f, by ext x; exact one_smul R (f x) }

end subtype

section continuous_map

instance continuous_map_has_scalar {α : Type*} [topological_space α]
  (R : Type*) [semiring R] [topological_space R]
  (M : Type*) [topological_space M] [add_comm_monoid M]
  [semimodule R M] [topological_semimodule R M] :
  has_scalar R C(α, M) :=
⟨λ r f, ⟨r • f, continuous_const.smul f.continuous⟩⟩

instance continuous_map_semimodule {α : Type*} [topological_space α]
{R : Type*} [semiring R] [topological_space R]
{M : Type*} [topological_space M] [add_comm_group M] [topological_add_group M]
[semimodule R M] [topological_semimodule R M] :
  semimodule R C(α, M) :=
  semimodule.of_core $
{ smul     := (•),
  smul_add := λ c f g, by ext x; exact smul_add c (f x) (g x),
  add_smul := λ c₁ c₂ f, by ext x; exact add_smul c₁ c₂ (f x),
  mul_smul := λ c₁ c₂ f, by ext x; exact mul_smul c₁ c₂ (f x),
  one_smul := λ f, by ext x; exact one_smul R (f x) }

end continuous_map

end semimodule_structure

section algebra_structure

/-!
### Algebra structure

In this section we show that continuous functions valued in a topological algebra `A` over a ring
`R` inherit a structure of algebra. Note that the hypothesis that `A` is a topologial algebra is
obtained by requiring that `A` be both a `topological_semimodule` and a `topological_semiring`
(by now we require `topological_ring`: see TODO below).-/

section subtype

variables {α : Type*} [topological_space α]
{R : Type*} [comm_semiring R]
{A : Type*} [topological_space A] [ring A]
[algebra R A] [topological_ring A]

/-- Continuous constant functions as a `ring_hom`. -/
def continuous.C : R →+* { f : α → A | continuous f } :=
{ to_fun    := λ c : R, ⟨λ x: α, ((algebra_map R A) c), continuous_const⟩,
  map_one'  := by ext x; exact (algebra_map R A).map_one,
  map_mul'  := λ c₁ c₂, by ext x; exact (algebra_map R A).map_mul _ _,
  map_zero' := by ext x; exact (algebra_map R A).map_zero,
  map_add'  := λ c₁ c₂, by ext x; exact (algebra_map R A).map_add _ _ }

variables [topological_space R] [topological_semimodule R A]

instance : algebra R { f : α → A | continuous f } :=
{ to_ring_hom := continuous.C,
  commutes' := λ c f, by ext x; exact algebra.commutes' _ _,
  smul_def' := λ c f, by ext x; exact algebra.smul_def' _ _,
  ..continuous_semimodule,
  ..continuous_ring }

/- TODO: We are assuming `A` to be a ring and not a semiring just because there is not yet an
instance of semiring. In turn, we do not want to define yet an instance of semiring because there is
no `is_subsemiring` but only `subsemiring`, and it will make sense to change this when the whole
file will have no more `is_subobject`s but only `subobject`s. It does not make sense to change
it yet in this direction as `subring` does not exist yet, so everything is being blocked by
`subring`: afterwards everything will need to be updated to the new conventions of Mathlib.
Then the instance of `topological_ring` can also be removed, as it is below for `continuous_map`. -/

end subtype

section continuous_map

variables {α : Type*} [topological_space α]
{R : Type*} [comm_semiring R]
{A : Type*} [topological_space A] [semiring A]
[algebra R A] [topological_semiring A]

/-- Continuous constant functions as a `ring_hom`. -/
def continuous_map.C : R →+* C(α, A) :=
{ to_fun    := λ c : R, ⟨λ x: α, ((algebra_map R A) c), continuous_const⟩,
  map_one'  := by ext x; exact (algebra_map R A).map_one,
  map_mul'  := λ c₁ c₂, by ext x; exact (algebra_map R A).map_mul _ _,
  map_zero' := by ext x; exact (algebra_map R A).map_zero,
  map_add'  := λ c₁ c₂, by ext x; exact (algebra_map R A).map_add _ _ }

variables [topological_space R] [topological_semimodule R A]

instance : algebra R C(α, A) :=
{ to_ring_hom := continuous_map.C,
  commutes' := λ c f, by ext x; exact algebra.commutes' _ _,
  smul_def' := λ c f, by ext x; exact algebra.smul_def' _ _,
  ..continuous_map_semiring }

end continuous_map

end algebra_structure

section module_over_continuous_functions

/-!
### Structure as module over scalar functions

If `M` is a module over `R`, then we show that the space of continuous functions from `α` to `M`
is naturally a module over the algebra of continuous functions from `α` to `M`. -/

section subtype

instance continuous_has_scalar' {α : Type*} [topological_space α]
  {R : Type*} [semiring R] [topological_space R]
  {M : Type*} [topological_space M] [add_comm_group M]
  [semimodule R M] [topological_semimodule R M] :
  has_scalar { f : α → R | continuous f } { f : α → M | continuous f } :=
⟨λ f g, ⟨λ x, (f x) • (g x), (continuous.smul f.2 g.2)⟩⟩

instance continuous_module' {α : Type*} [topological_space α]
  (R : Type*) [ring R] [topological_space R] [topological_ring R]
  (M : Type*) [topological_space M] [add_comm_group M] [topological_add_group M]
  [module R M] [topological_module R M]
  : module { f : α → R | continuous f } { f : α → M | continuous f } :=
  semimodule.of_core $
{ smul     := (•),
  smul_add := λ c f g, by ext x; exact smul_add (c x) (f x) (g x),
  add_smul := λ c₁ c₂ f, by ext x; exact add_smul (c₁ x) (c₂ x) (f x),
  mul_smul := λ c₁ c₂ f, by ext x; exact mul_smul (c₁ x) (c₂ x) (f x),
  one_smul := λ f, by ext x; exact one_smul R (f x) }

end subtype

section continuous_map

instance continuous_map_has_scalar' {α : Type*} [topological_space α]
  {R : Type*} [semiring R] [topological_space R]
  {M : Type*} [topological_space M] [add_comm_group M]
  [semimodule R M] [topological_semimodule R M] :
  has_scalar C(α, R) C(α, M) :=
⟨λ f g, ⟨λ x, (f x) • (g x), (continuous.smul f.2 g.2)⟩⟩

instance continuous_map_module' {α : Type*} [topological_space α]
  (R : Type*) [ring R] [topological_space R] [topological_ring R]
  (M : Type*) [topological_space M] [add_comm_group M] [topological_add_group M]
  [module R M] [topological_module R M]
  : module C(α, R) C(α, M) :=
  semimodule.of_core $
{ smul     := (•),
  smul_add := λ c f g, by ext x; exact smul_add (c x) (f x) (g x),
  add_smul := λ c₁ c₂ f, by ext x; exact add_smul (c₁ x) (c₂ x) (f x),
  mul_smul := λ c₁ c₂ f, by ext x; exact mul_smul (c₁ x) (c₂ x) (f x),
  one_smul := λ f, by ext x; exact one_smul R (f x) }

end continuous_map

end module_over_continuous_functions
