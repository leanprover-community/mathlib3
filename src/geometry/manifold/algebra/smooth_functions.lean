/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/

import geometry.manifold.algebra.structures
import geometry.manifold.smooth_map

/-!
# Algebraic structures over smooth functions

In this file we define instances of algebraic sturctures over smooth functions.
-/

noncomputable theory

open_locale manifold

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{E'' : Type*} [normed_group E''] [normed_space 𝕜 E'']
{H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{N : Type*} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N]

namespace smooth_map

@[to_additive]
instance has_mul {G : Type*} [has_mul G] [topological_space G] [has_continuous_mul G]
  [charted_space H' G] [smooth_manifold_with_corners I' G] [has_smooth_mul I' G] :
  has_mul C∞(I, N; I', G) :=
⟨λ f g, ⟨f * g, smooth_mul.comp (f.smooth.prod_mk g.smooth)⟩⟩

@[to_additive]
instance {G : Type*} [monoid G] [topological_space G]
  [charted_space H' G] [smooth_manifold_with_corners I' G] :
  has_one C∞(I, N; I', G) :=
⟨const (1 : G)⟩

end smooth_map

section group_structure

/-!
### Group stucture

In this section we show that smooth functions valued in a Lie group inherit a structure of group.
-/

@[to_additive]
instance smooth_map_semigroup {G : Type*} [semigroup G] [topological_space G] [has_continuous_mul G]
  [charted_space H' G] [smooth_manifold_with_corners I' G] [has_smooth_mul I' G]
 : semigroup C∞(I, N; I', G) :=
{ mul_assoc := λ a b c, by ext; exact mul_assoc _ _ _,
  ..smooth_map.has_mul}

@[to_additive]
instance smooth_map_monoid {G : Type*} [monoid G] [topological_space G] [has_continuous_mul G]
  [charted_space H' G] [smooth_manifold_with_corners I' G] [has_smooth_mul I' G] :
  monoid C∞(I, N; I', G) :=
{ one_mul := λ a, by ext; exact one_mul _,
  mul_one := λ a, by ext; exact mul_one _,
  ..smooth_map_semigroup,
  ..smooth_map.has_one }

@[to_additive]
instance smooth_map_comm_monoid {G : Type*} [comm_monoid G] [topological_space G]
  [has_continuous_mul G] [charted_space H' G]
  [smooth_manifold_with_corners I' G] [has_smooth_mul I' G] :
  comm_monoid C∞(I, N; I', G) :=
{ one_mul := λ a, by ext; exact one_mul _,
  mul_one := λ a, by ext; exact mul_one _,
  mul_comm := λ a b, by ext; exact mul_comm _ _,
  ..smooth_map_semigroup,
  ..smooth_map.has_one }

@[to_additive]
instance smooth_map_group {G : Type*} [group G] [topological_space G] [topological_group G]
  [charted_space H' G] [smooth_manifold_with_corners I' G] [lie_group I' G] :
  group C∞(I, N; I', G) :=
{ inv := λ f, ⟨λ x, (f x)⁻¹, smooth_inv.comp f.smooth⟩,
  mul_left_inv := λ a, by ext; exact mul_left_inv _,
  ..smooth_map_monoid }

@[to_additive]
instance smooth_map_comm_group {G : Type*} [comm_group G] [topological_space G]
  [topological_group G] [charted_space H' G] [smooth_manifold_with_corners I' G] [lie_group I' G] :
  comm_group C∞(I, N; I', G) :=
{ ..smooth_map_group,
  ..smooth_map_comm_monoid }

end group_structure

section ring_structure

/-!
### Ring stucture

In this section we show that smooth functions valued in a smooth ring `R` inherit a structure of
ring.
-/

instance smooth_map_semiring {R : Type*} [semiring R] [topological_space R] [topological_semiring R]
  [charted_space H' R] [smooth_manifold_with_corners I' R] [smooth_semiring I' R] :
  semiring C∞(I, N; I', R) :=
{ left_distrib := λ a b c, by ext; exact left_distrib _ _ _,
  right_distrib := λ a b c, by ext; exact right_distrib _ _ _,
  zero_mul := λ a, by ext; exact zero_mul _,
  mul_zero := λ a, by ext; exact mul_zero _,
  ..smooth_map_add_comm_monoid,
  ..smooth_map_monoid }

instance smooth_map_ring {R : Type*} [ring R] [topological_space R] [topological_ring R]
  [charted_space H' R] [smooth_manifold_with_corners I' R] [smooth_ring I' R] :
  ring C∞(I, N; I', R) :=
{ ..smooth_map_semiring,
  ..smooth_map_add_comm_group, }

instance smooth_map_comm_ring {R : Type*} [comm_ring R] [topological_space R] [topological_ring R]
  [charted_space H' R] [smooth_manifold_with_corners I' R] [smooth_ring I' R] :
  comm_ring C∞(I, N; I', R) :=
{ ..smooth_map_semiring,
  ..smooth_map_add_comm_group,
  ..smooth_map_comm_monoid,}

end ring_structure

section semimodule_structure

/-!
### Semiodule stucture

In this section we show that smooth functions valued in a smooth vector space `M` over a normed
field `R` that is a normed space over `𝕜` inherit a structure of vector space.

From now on, whenever a scalar multiplication is involved, we cannot consider `R` to be a generic
semiring with a manifold structure, because of dangerous instances problems (the model with corners
on which `R` is a manifold gets forgotten). Hence we do everything in the case of `R` being a field
which is a normed space over `𝕜`, which is slightly more general that the case `𝕜 = R` as it takes
into account the case `𝕜 = ℝ`, `R = ℂ`.
-/

instance smooth_map_has_scalar
  {R : Type*} [normed_field R] [normed_space 𝕜 R]
  {M : Type*} [topological_space M] [add_comm_group M]
  [vector_space R M] [topological_vector_space R M]
  [charted_space H'' M] [smooth_manifold_with_corners I'' M] [smooth_vector_space I'' R M] :
  has_scalar R C∞(I, N; I'', M) :=
⟨λ r f, ⟨r • f, (@smooth_const _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Isf(𝕜, R) _ _ _ _).smul f.smooth⟩⟩

instance smooth_map_semimodule
  {R : Type*} [normed_field R] [normed_space 𝕜 R]
  {M : Type*} [topological_space M] [add_comm_group M] [topological_add_group M]
  [vector_space R M] [topological_vector_space R M]
  [charted_space H'' M] [smooth_manifold_with_corners I'' M] [lie_add_group I'' M]
  [smooth_vector_space I'' R M] :
  vector_space R C∞(I, N; I'', M) :=
semimodule.of_core $
{ smul     := (•),
  smul_add := λ c f g, by ext x; exact smul_add c (f x) (g x),
  add_smul := λ c₁ c₂ f, by ext x; exact add_smul c₁ c₂ (f x),
  mul_smul := λ c₁ c₂ f, by ext x; exact mul_smul c₁ c₂ (f x),
  one_smul := λ f, by ext x; exact one_smul R (f x), }

end semimodule_structure

section algebra_structure

/-!
### Algebra structure

In this section we show that smooth functions valued in a smooth algebra `A` over a normed field
`R` that is a normed space over `𝕜` inherit a structure of algebra. Note that the hypothesis that
`A` is a smooth algebra is obtained by requiring that `A` be both a `smooth_vector_space` and a
`smooth_ring`.

To see why `R` cannot be a generic semiring with a manifold structure see the note of "Semiodule
stucture".
-/

variables {R : Type*} [normed_field R]
{A : Type*} [topological_space A] [ring A] [algebra R A] [topological_ring A]
[charted_space H'' A] [smooth_manifold_with_corners I'' A] [smooth_ring I'' A]

/-- Smooth constant functions as a `ring_hom`. -/
def smooth_map.C : R →+* C∞(I, N; I'', A) :=
{ to_fun    := λ c : R, ⟨λ x, ((algebra_map R A) c), smooth_const⟩,
  map_one'  := by ext x; exact (algebra_map R A).map_one,
  map_mul'  := λ c₁ c₂, by ext x; exact (algebra_map R A).map_mul _ _,
  map_zero' := by ext x; exact (algebra_map R A).map_zero,
  map_add'  := λ c₁ c₂, by ext x; exact (algebra_map R A).map_add _ _ }

variables [normed_space 𝕜 R]
[topological_vector_space R A] [smooth_vector_space I'' R A]

instance : algebra R C∞(I, N; I'', A) :=
{ smul := λ r f,
  ⟨r • f, (@smooth_const _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Isf(𝕜, R) _ _ _ _).smul f.smooth⟩,
  to_ring_hom := smooth_map.C,
  commutes' := λ c f, by ext x; exact algebra.commutes' _ _,
  smul_def' := λ c f, by ext x; exact algebra.smul_def' _ _,
  ..smooth_map_semiring }

end algebra_structure

section module_over_continuous_functions

/-!
### Structure as module over scalar functions

If `M` is a module over `R`, then we show that the space of smooth functions from `α` to `M`
is naturally a module over the ring of smooth functions from `α` to `M`. -/

instance smooth_map_has_scalar'
  {R : Type*} [semiring R] [topological_space R]
  [charted_space H' R] [smooth_manifold_with_corners I' R]
  {M : Type*} [topological_space M] [add_comm_monoid M]
  [semimodule R M] [topological_semimodule R M]
  [charted_space H'' M] [smooth_manifold_with_corners I'' M] [smooth_semimodule I' I'' R M] :
  has_scalar C∞(I, N; I', R) C∞(I, N; I'', M) :=
⟨λ f g, ⟨λ x, (f x) • (g x), (smooth.smul f.2 g.2)⟩⟩

instance smooth_map_module'
  {R : Type*} [semiring R] [topological_space R] [topological_semiring R]
  [charted_space H' R] [smooth_manifold_with_corners I' R] [smooth_semiring I' R]
  {M : Type*} [topological_space M] [add_comm_monoid M] [has_continuous_add M]
  [semimodule R M] [topological_semimodule R M]
  [charted_space H'' M] [smooth_manifold_with_corners I'' M]
  [has_smooth_add I'' M] [smooth_semimodule I' I'' R M]
  : semimodule C∞(I, N; I', R) C∞(I, N; I'', M) :=
{ smul     := (•),
  smul_add := λ c f g, by ext x; exact smul_add (c x) (f x) (g x),
  add_smul := λ c₁ c₂ f, by ext x; exact add_smul (c₁ x) (c₂ x) (f x),
  mul_smul := λ c₁ c₂ f, by ext x; exact mul_smul (c₁ x) (c₂ x) (f x),
  one_smul := λ f, by ext x; exact one_smul R (f x),
  zero_smul := λ f, by ext x; exact zero_smul _ _,
  smul_zero := λ r, by ext x; exact smul_zero _, }

end module_over_continuous_functions

instance field_valued_smooth_maps_ring : ring C∞(I, N; 𝕜) := by apply_instance

instance field_valued_smooth_maps_algebra : algebra 𝕜 C∞(I, N; 𝕜) := by apply_instance
