/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import topology.algebra.module.basic

/-!
# Weak dual topology

This file defines the weak-* topology on duals of suitable topological modules `E` over suitable
topological semirings `𝕜`. The (weak) dual consists of continuous linear functionals `E →L[𝕜] 𝕜`
from `E` to scalars `𝕜`. The weak-* topology is the coarsest topology on this dual
`weak_dual 𝕜 E := (E →L[𝕜] 𝕜)` w.r.t. which the evaluation maps at all `z : E` are continuous.

The weak dual is a module over `𝕜` if the semiring `𝕜` is commutative.

## Main definitions

The main definitions are the type `weak_dual 𝕜 E` and a topology instance on it.

* `weak_dual 𝕜 E` is a type synonym for `dual 𝕜 E` (when the latter is defined): both are equal to
  the type `E →L[𝕜] 𝕜` of continuous linear maps from a module `E` over `𝕜` to the ring `𝕜`.
* The instance `weak_dual.topological_space` is the weak-* topology on `weak_dual 𝕜 E`, i.e., the
  coarsest topology making the evaluation maps at all `z : E` continuous.

## Main results

We establish that `weak_dual 𝕜 E` has the following structure:
* `weak_dual.has_continuous_add`: The addition in `weak_dual 𝕜 E` is continuous.
* `weak_dual.module`: If the scalars `𝕜` are a commutative semiring, then `weak_dual 𝕜 E` is a
  module over `𝕜`.
* `weak_dual.has_continuous_smul`: If the scalars `𝕜` are a commutative semiring, then the scalar
  multiplication by `𝕜` in `weak_dual 𝕜 E` is continuous.

We prove the following results characterizing the weak-* topology:
* `weak_dual.eval_continuous`: For any `z : E`, the evaluation mapping `weak_dual 𝕜 E → 𝕜` taking
  `x'`to `x' z` is continuous.
* `weak_dual.continuous_of_continuous_eval`: For a mapping to `weak_dual 𝕜 E` to be continuous,
  it suffices that its compositions with evaluations at all points `z : E` are continuous.
* `weak_dual.tendsto_iff_forall_eval_tendsto`: Convergence in `weak_dual 𝕜 E` can be characterized
  in terms of convergence of the evaluations at all points `z : E`.

## Notations

No new notation is introduced.

## Implementation notes

The weak-* topology is defined as the induced topology under the mapping that associates to a dual
element `x'` the functional `E → 𝕜`, when the space `E → 𝕜` of functionals is equipped with the
topology of pointwise convergence (product topology).

Typically one might assume that `𝕜` is a topological semiring in the sense of the typeclasses
`topological_space 𝕜`, `semiring 𝕜`, `has_continuous_add 𝕜`, `has_continuous_mul 𝕜`,
and that the space `E` is a topological module over `𝕜` in the sense of the typeclasses
`topological_space E`, `add_comm_monoid E`, `has_continuous_add E`, `module 𝕜 E`,
`has_continuous_smul 𝕜 E`. The definitions and results are, however, given with weaker assumptions
when possible.

## References

* https://en.wikipedia.org/wiki/Weak_topology#Weak-*_topology

## Tags

weak-star, weak dual

-/

noncomputable theory
open filter
open_locale topological_space

universes u v

section weak_star_topology
/-!
### Weak star topology on duals of topological modules
-/

variables (𝕜 : Type*) [topological_space 𝕜] [semiring 𝕜]
variables (E : Type*) [topological_space E] [add_comm_monoid E] [module 𝕜 E]

/-- The weak dual of a topological module `E` over a topological semiring `𝕜` consists of
continuous linear functionals from `E` to scalars `𝕜`. It is a type synonym with the usual dual
(when the latter is defined), but will be equipped with a different topology. -/
@[derive [inhabited, λ α, has_coe_to_fun α (λ _, E → 𝕜), λ α, add_monoid_hom_class α E 𝕜]]
def weak_dual := E →L[𝕜] 𝕜

instance [has_continuous_add 𝕜] : add_comm_monoid (weak_dual 𝕜 E) :=
continuous_linear_map.add_comm_monoid

namespace weak_dual

/-- The weak-* topology instance `weak_dual.topological_space` on the dual of a topological module
`E` over a topological semiring `𝕜` is defined as the induced topology under the mapping that
associates to a dual element `x' : weak_dual 𝕜 E` the functional `E → 𝕜`, when the space `E → 𝕜`
of functionals is equipped with the topology of pointwise convergence (product topology). -/
instance : topological_space (weak_dual 𝕜 E) :=
topological_space.induced (λ x' : weak_dual 𝕜 E, λ z : E, x' z) Pi.topological_space

/-- The coercion `coe_fn : weak_dual 𝕜 E → (E → 𝕜)` is an embedding. -/
lemma coe_fn_embedding :
  embedding (coe_fn : weak_dual 𝕜 E → (E → 𝕜)) :=
by convert continuous_linear_map.coe_fn_injective.embedding_induced

lemma coe_fn_continuous :
  continuous (λ (x' : (weak_dual 𝕜 E)), (λ (z : E), x' z)) :=
continuous_induced_dom

lemma eval_continuous (z : E) : continuous (λ (x' : weak_dual 𝕜 E), x' z) :=
(continuous_pi_iff.mp (coe_fn_continuous 𝕜 E)) z

lemma continuous_of_continuous_eval {α : Type u} [topological_space α]
  {g : α → weak_dual 𝕜 E} (h : ∀ z, continuous (λ a, g a z)) : continuous g :=
continuous_induced_rng (continuous_pi_iff.mpr h)

theorem tendsto_iff_forall_eval_tendsto {γ : Type u} {F : filter γ}
  {ψs : γ → weak_dual 𝕜 E} {ψ : weak_dual 𝕜 E} :
  tendsto ψs F (𝓝 ψ) ↔ ∀ z : E, tendsto (λ i, ψs i z) F (𝓝 (ψ z)) :=
by rw [← tendsto_pi_nhds, (coe_fn_embedding 𝕜 E).tendsto_nhds_iff]

/-- Addition in `weak_dual 𝕜 E` is continuous. -/
instance [has_continuous_add 𝕜] : has_continuous_add (weak_dual 𝕜 E) :=
⟨continuous_induced_rng $ ((coe_fn_continuous 𝕜 E).comp continuous_fst).add
  ((coe_fn_continuous 𝕜 E).comp continuous_snd)⟩

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it acts on `weak_dual 𝕜 E`. -/
instance (M : Type*) [monoid M] [distrib_mul_action M 𝕜] [smul_comm_class 𝕜 M 𝕜]
  [has_continuous_const_smul M 𝕜] :
  mul_action M (weak_dual 𝕜 E) :=
continuous_linear_map.mul_action

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it acts distributively on `weak_dual 𝕜 E`. -/
instance (M : Type*) [monoid M] [distrib_mul_action M 𝕜] [smul_comm_class 𝕜 M 𝕜]
  [has_continuous_const_smul M 𝕜] [has_continuous_add 𝕜] :
  distrib_mul_action M (weak_dual 𝕜 E) :=
continuous_linear_map.distrib_mul_action

/-- If `𝕜` is a topological module over a semiring `R` and scalar multiplication commutes with the
multiplication on `𝕜`, then `weak_dual 𝕜 E` is a module over `R`. -/
instance (R : Type*) [semiring R] [module R 𝕜] [smul_comm_class 𝕜 R 𝕜]
  [has_continuous_const_smul R 𝕜] [has_continuous_add 𝕜] :
  module R (weak_dual 𝕜 E) :=
continuous_linear_map.module

instance (M : Type*) [monoid M] [distrib_mul_action M 𝕜] [smul_comm_class 𝕜 M 𝕜]
  [has_continuous_const_smul M 𝕜] : has_continuous_const_smul M (weak_dual 𝕜 E) :=
⟨λ m, continuous_induced_rng $ (coe_fn_continuous 𝕜 E).const_smul m⟩

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it continuously acts on `weak_dual 𝕜 E`. -/
instance (M : Type*) [monoid M] [distrib_mul_action M 𝕜] [smul_comm_class 𝕜 M 𝕜]
  [topological_space M] [has_continuous_smul M 𝕜] :
  has_continuous_smul M (weak_dual 𝕜 E) :=
⟨continuous_induced_rng $ continuous_fst.smul ((coe_fn_continuous 𝕜 E).comp continuous_snd)⟩

end weak_dual

end weak_star_topology

section algebra

variables {𝕜 : Type*} {A : Type*}
  [comm_semiring 𝕜] [topological_space 𝕜]
  [semiring A] [topological_space A] [algebra 𝕜 A]

variables (𝕜) (A)

/-- The Gelfand space of a topological algebra is the subset of elements of the weak dual that
are also algebra homomorphisms. -/
def gelfand_space :=
  {φ : weak_dual 𝕜 A | (φ 1 = 1) ∧ (∀ (x y : A), φ (x * y) = (φ x) * (φ y))}

variables {𝕜} {A}

namespace gelfand_space

-- TODO: upgrade this to `alg_hom_class` when it gets defined.
instance : ring_hom_class (gelfand_space 𝕜 A) A 𝕜 :=
{ map_one := λ φ, φ.prop.1,
  map_mul := λ φ, φ.prop.2,
  ..subtype.add_monoid_hom_class (weak_dual 𝕜 A) A 𝕜 _ }

/-- An element of the Gelfand space, as an algebra homomorphism. -/
def to_alg_hom (φ : gelfand_space 𝕜 A) : A →ₐ[𝕜] 𝕜 :=
{ to_fun := (φ : A → 𝕜),
  map_one' := ring_hom_class.map_one _,
  map_mul' := ring_hom_class.map_mul _,
  map_zero' := ring_hom_class.map_zero _,
  map_add' := ring_hom_class.map_add _,
  commutes' := λ r, by rw [algebra.algebra_map_eq_smul_one, algebra.id.map_eq_id,
        ring_hom.id_apply, @coe_fn_coe_base' _ (weak_dual 𝕜 A), continuous_linear_map.map_smul,
        algebra.id.smul_eq_mul, ←@coe_fn_coe_base', map_one, mul_one] }

end gelfand_space

end algebra
