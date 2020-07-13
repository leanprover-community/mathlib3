/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.algebra.module

/- TODO: change subtype of continuous functions into continuous bundled functions. -/

universes u v

local attribute [elab_simple] continuous.comp

namespace continuous_functions

variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]
variables {f g : {f : α → β | continuous f }}

instance : has_coe_to_fun {f : α → β | continuous f } :=  ⟨_, subtype.val⟩

@[ext] lemma ext (H : ∀x, f x = g x) : f = g :=
subtype.eq $ funext H

end continuous_functions

section group_structure

/-!
### Group stucture

In this section we show that continuous functions valued in a topological group inherit
a structure of topological group.
-/

@[to_additive continuous_add_submonoid]
instance continuous_submonoid (α : Type u) (β : Type v) [topological_space α] [topological_space β]
  [monoid β] [topological_monoid β] : is_submonoid { f : α → β | continuous f } :=
{ one_mem := @continuous_const _ _ _ _ 1,
  mul_mem :=
  λ f g fc gc, continuous.comp topological_monoid.continuous_mul (continuous.prod_mk fc gc) }.

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

end group_structure

section ring_structure

/-!
### Ring stucture

In this section we show that continuous functions valued in a topological ring `R` inherit
a structure of topological ring.
-/

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

end ring_structure

section semimodule_structure

/-!
### Semiodule stucture

In this section we show that continuous functions valued in a topological semimodule `M` over a
topological semiring `R` inherit a structure of topological semimodule.
-/

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
  smul_add := λ c f g, continuous_functions.ext $ λ x, smul_add c (f x) (g x),
  add_smul := λ c₁ c₂ f, continuous_functions.ext $ λ x, add_smul c₁ c₂ (f x),
  mul_smul := λ c₁ c₂ f, continuous_functions.ext $ λ x, mul_smul c₁ c₂ (f x),
  one_smul := λ f, continuous_functions.ext $ λ x, one_smul R (f x) }

end semimodule_structure

section algebra_structure

/-!
### Algebra structure

In this section we show that continuous functions valued in a topological algebra `A` over a
topological ring `R` inherit a structure of topological algebra. -/

variables {α : Type*} [topological_space α]
{R : Type*} [comm_semiring R] [topological_space R] [topological_semiring R]
{A : Type*} [topological_space A] [ring A]
[algebra R A] [topological_algebra R A] [topological_ring A]

/-- Continuous constant functions as a `ring_hom`. -/
def C : R →+* { f : α → A | continuous f } :=
{ to_fun    := λ c : R, ⟨λ x: α, ((algebra_map R A) c), continuous_const⟩,
  map_one'  := continuous_functions.ext $ λ x, (algebra_map R A).map_one,
  map_mul'  := λ c₁ c₂, continuous_functions.ext $ λ x, (algebra_map R A).map_mul _ _,
  map_zero' := continuous_functions.ext $ λ x, (algebra_map R A).map_zero,
  map_add'  := λ c₁ c₂, continuous_functions.ext $ λ x, (algebra_map R A).map_add _ _ }

instance : algebra R { f : α → A | continuous f } :=
{ to_ring_hom := C,
  commutes' := λ c f, continuous_functions.ext $ λ x, algebra.commutes' _ _,
  smul_def' := λ c f, continuous_functions.ext $ λ x, algebra.smul_def' _ _,
  ..continuous_semimodule,
  ..continuous_ring }

/- TODO: We are assuming `A` to be a ring and not a semiring just because there is not yet an
instance of semiring. In turn, we do not want to define yet an instance of semiring because there is
no `is_subsemiring` but only `subsemiring`, and it will make sense to change this when the whole
file will have no more `is_subobject`s but only `subobject`s. It does not make sense to change
it yet in this direction as `subring` does not exist yet, so everything is being blocked by
`subring`: afterwards everything will need to be updated to the new conventions of Mathlib.
Then the instance of `topological_ring` can also be removed. -/

end algebra_structure

section module_over_continuous_functions

/-!
### Structure as module over scalar functions

If `M` is a module over `R`, then we show that the space of continuous functions from `α` to `M`
is naturally a module over the algebra of continuous functions from `α` to `M`. -/

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
  smul_add := λ c f g, continuous_functions.ext $ λ x, smul_add (c x) (f x) (g x),
  add_smul := λ c₁ c₂ f, continuous_functions.ext $ λ x, add_smul (c₁ x) (c₂ x) (f x),
  mul_smul := λ c₁ c₂ f, continuous_functions.ext $ λ x, mul_smul (c₁ x) (c₂ x) (f x),
  one_smul := λ f, continuous_functions.ext $ λ x, one_smul R (f x) }

end module_over_continuous_functions
