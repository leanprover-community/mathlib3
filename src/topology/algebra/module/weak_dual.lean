/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Moritz Doll
-/
import topology.algebra.module.basic

/-!
# Weak dual topology

This file defines the weak topology given two vector spaces `E` and `F` over a commutative semiring
`𝕜` and a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`. The weak topology on `E` is the coarsest topology
such that for all `y : F` every map `λ x, B x y` is continuous.

In the case that `F = E →L[𝕜] 𝕜` and `B` being the canonical pairing, we obtain the weak-* topology,
`weak_dual 𝕜 E := (E →L[𝕜] 𝕜)`. Interchanging the arguments in the bilinear form yields the
weak topology `weak_space 𝕜 E := E`.

## Main definitions

The main definitions are the types `weak_bilin B` for the general case and the two special cases
`weak_dual 𝕜 E` and `weak_space 𝕜 E` with the respective topology instances on it.

* Given `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`, the type `weak_bilin B` is a type synonym for `E`.
* The instance `weak_bilin.topological_space` is the weak topology induced by the bilinear form `B`.
* `weak_dual 𝕜 E` is a type synonym for `dual 𝕜 E` (when the latter is defined): both are equal to
  the type `E →L[𝕜] 𝕜` of continuous linear maps from a module `E` over `𝕜` to the ring `𝕜`.
* The instance `weak_dual.topological_space` is the weak-* topology on `weak_dual 𝕜 E`, i.e., the
  coarsest topology making the evaluation maps at all `z : E` continuous.
* `weak_space 𝕜 E` is a type synonym for `E` (when the latter is defined).
* The instance `weak_dual.topological_space` is the weak topology on `E`, i.e., the
  coarsest topology such that all `v : dual 𝕜 E` remain continuous.

## Main results

We establish that `weak_bilin B` has the following structure:
* `weak_bilin.has_continuous_add`: The addition in `weak_bilin B` is continuous.
* `weak_bilin.has_continuous_smul`: The scalar multiplication in `weak_bilin B` is continuous.

We prove the following results characterizing the weak topology:
* `eval_continuous`: For any `y : F`, the evaluation mapping `λ x, B x y` is continuous.
* `continuous_of_continuous_eval`: For a mapping to `weak_bilin B` to be continuous,
  it suffices that its compositions with pairing with `B` at all points `y : F` is continuous.
* `tendsto_iff_forall_eval_tendsto`: Convergence in `weak_bilin B` can be characterized
  in terms of convergence of the evaluations at all points `y : F`.

## Notations

No new notation is introduced.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

weak-star, weak dual, duality

-/

noncomputable theory
open filter
open_locale topological_space

variables {α 𝕜 𝕝 R E F M : Type*}

section weak_topology

/-- The space `E` equipped with the weak topology induced by the bilinear form `B`. -/
@[derive [add_comm_monoid, module 𝕜],
nolint has_inhabited_instance unused_arguments]
def weak_bilin [comm_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E] [add_comm_monoid F]
  [module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) := E

namespace weak_bilin

instance [comm_semiring 𝕜] [a : add_comm_group E] [module 𝕜 E] [add_comm_monoid F]
  [module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : add_comm_group (weak_bilin B) := a

@[priority 100]
instance module' [comm_semiring 𝕜] [comm_semiring 𝕝] [add_comm_group E] [module 𝕜 E]
  [add_comm_group F] [module 𝕜 F] [m : module 𝕝 E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
  module 𝕝 (weak_bilin B) := m

instance [comm_semiring 𝕜] [comm_semiring 𝕝] [add_comm_group E] [module 𝕜 E]
  [add_comm_group F] [module 𝕜 F] [has_scalar 𝕝 𝕜] [module 𝕝 E] [s : is_scalar_tower 𝕝 𝕜 E]
  (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : is_scalar_tower 𝕝 𝕜 (weak_bilin B) := s

section semiring

variables [topological_space 𝕜] [comm_semiring 𝕜]
variables [add_comm_monoid E] [module 𝕜 E]
variables [add_comm_monoid F] [module 𝕜 F]
variables (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

instance : topological_space (weak_bilin B) :=
topological_space.induced (λ x y, B x y) Pi.topological_space

lemma coe_fn_continuous : continuous (λ (x : weak_bilin B) y, B x y) :=
continuous_induced_dom

lemma eval_continuous (y : F) : continuous (λ x : weak_bilin B, B x y) :=
( continuous_pi_iff.mp (coe_fn_continuous B)) y

lemma continuous_of_continuous_eval [topological_space α] {g : α → weak_bilin B}
  (h : ∀ y, continuous (λ a, B (g a) y)) : continuous g :=
continuous_induced_rng (continuous_pi_iff.mpr h)

/-- The coercion `(λ x y, B x y) : E → (F → 𝕜)` is an embedding. -/
lemma embedding {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (hB : function.injective B) :
  embedding (λ (x : weak_bilin B)  y, B x y) :=
function.injective.embedding_induced $ linear_map.coe_injective.comp hB

theorem tendsto_iff_forall_eval_tendsto {l : filter α} {f : α → (weak_bilin B)} {x : weak_bilin B}
  (hB : function.injective B) : tendsto f l (𝓝 x) ↔ ∀ y, tendsto (λ i, B (f i) y) l (𝓝 (B x y)) :=
by rw [← tendsto_pi_nhds, embedding.tendsto_nhds_iff (embedding hB)]

/-- Addition in `weak_space B` is continuous. -/
instance [has_continuous_add 𝕜] : has_continuous_add (weak_bilin B) :=
begin
  refine ⟨continuous_induced_rng _⟩,
  refine cast (congr_arg _ _) (((coe_fn_continuous B).comp continuous_fst).add
    ((coe_fn_continuous B).comp continuous_snd)),
  ext,
  simp only [function.comp_app, pi.add_apply, map_add, linear_map.add_apply],
end

/-- Scalar multiplication by `𝕜` on `weak_bilin B` is continuous. -/
instance [has_continuous_smul 𝕜 𝕜] : has_continuous_smul 𝕜 (weak_bilin B) :=
begin
  refine ⟨continuous_induced_rng _⟩,
  refine cast (congr_arg _ _) (continuous_fst.smul ((coe_fn_continuous B).comp continuous_snd)),
  ext,
  simp only [function.comp_app, pi.smul_apply, linear_map.map_smulₛₗ, ring_hom.id_apply,
    linear_map.smul_apply],
end

end semiring

section ring

variables [topological_space 𝕜] [comm_ring 𝕜]
variables [add_comm_group E] [module 𝕜 E]
variables [add_comm_group F] [module 𝕜 F]
variables (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

/-- `weak_space B` is a `topological_add_group`, meaning that addition and negation are
continuous. -/
instance [has_continuous_add 𝕜] : topological_add_group (weak_bilin B) :=
{ to_has_continuous_add := by apply_instance,
  continuous_neg := begin
    refine continuous_induced_rng (continuous_pi_iff.mpr (λ y, _)),
    refine cast (congr_arg _ _) (eval_continuous B (-y)),
    ext,
    simp only [map_neg, function.comp_app, linear_map.neg_apply],
  end }

end ring

end weak_bilin

end weak_topology

section weak_star_topology

/-- The canonical pairing of a vector space and its topological dual. -/
def top_dual_pairing (𝕜 E) [comm_semiring 𝕜] [topological_space 𝕜] [has_continuous_add 𝕜]
  [add_comm_monoid E] [module 𝕜 E] [topological_space E]
  [has_continuous_const_smul 𝕜 𝕜] :
  (E →L[𝕜] 𝕜) →ₗ[𝕜] E →ₗ[𝕜] 𝕜 := continuous_linear_map.coe_lm 𝕜

variables [comm_semiring 𝕜] [topological_space 𝕜] [has_continuous_add 𝕜]
variables [has_continuous_const_smul 𝕜 𝕜]
variables [add_comm_monoid E] [module 𝕜 E] [topological_space E]

lemma dual_pairing_apply (v : (E →L[𝕜] 𝕜)) (x : E) : top_dual_pairing 𝕜 E v x = v x := rfl

/-- The weak star topology is the topology coarsest topology on `E →L[𝕜] 𝕜` such that all
functionals `λ v, top_dual_pairing 𝕜 E v x` are continuous. -/
@[derive [add_comm_monoid, module 𝕜, topological_space, has_continuous_add]]
def weak_dual (𝕜 E) [comm_semiring 𝕜] [topological_space 𝕜] [has_continuous_add 𝕜]
  [has_continuous_const_smul 𝕜 𝕜] [add_comm_monoid E] [module 𝕜 E] [topological_space E] :=
weak_bilin (top_dual_pairing 𝕜 E)

namespace weak_dual

instance : inhabited (weak_dual 𝕜 E) := continuous_linear_map.inhabited

instance weak_dual.add_monoid_hom_class : add_monoid_hom_class (weak_dual 𝕜 E) E 𝕜 :=
continuous_linear_map.add_monoid_hom_class

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (weak_dual 𝕜 E) (λ _, E → 𝕜) := fun_like.has_coe_to_fun

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it acts on `weak_dual 𝕜 E`. -/
instance (M) [monoid M] [distrib_mul_action M 𝕜] [smul_comm_class 𝕜 M 𝕜]
  [has_continuous_const_smul M 𝕜] :
  mul_action M (weak_dual 𝕜 E) :=
continuous_linear_map.mul_action

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it acts distributively on `weak_dual 𝕜 E`. -/
instance (M) [monoid M] [distrib_mul_action M 𝕜] [smul_comm_class 𝕜 M 𝕜]
  [has_continuous_const_smul M 𝕜] :
  distrib_mul_action M (weak_dual 𝕜 E) :=
continuous_linear_map.distrib_mul_action

/-- If `𝕜` is a topological module over a semiring `R` and scalar multiplication commutes with the
multiplication on `𝕜`, then `weak_dual 𝕜 E` is a module over `R`. -/
instance module' (R) [semiring R] [module R 𝕜] [smul_comm_class 𝕜 R 𝕜]
  [has_continuous_const_smul R 𝕜] :
  module R (weak_dual 𝕜 E) :=
continuous_linear_map.module

instance (M) [monoid M] [distrib_mul_action M 𝕜] [smul_comm_class 𝕜 M 𝕜]
  [has_continuous_const_smul M 𝕜] : has_continuous_const_smul M (weak_dual 𝕜 E) :=
⟨λ m, continuous_induced_rng $ (weak_bilin.coe_fn_continuous (top_dual_pairing 𝕜 E)).const_smul m⟩

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it continuously acts on `weak_dual 𝕜 E`. -/
instance (M) [monoid M] [distrib_mul_action M 𝕜] [smul_comm_class 𝕜 M 𝕜]
  [topological_space M] [has_continuous_smul M 𝕜] :
  has_continuous_smul M (weak_dual 𝕜 E) :=
⟨continuous_induced_rng $ continuous_fst.smul ((weak_bilin.coe_fn_continuous
                          (top_dual_pairing 𝕜 E)).comp continuous_snd)⟩

lemma coe_fn_continuous : continuous (λ (x : weak_dual 𝕜 E) y, x y) :=
continuous_induced_dom

lemma eval_continuous (y : E) : continuous (λ x : weak_dual 𝕜 E, x y) :=
continuous_pi_iff.mp coe_fn_continuous y

lemma continuous_of_continuous_eval [topological_space α] {g : α → weak_dual 𝕜 E}
  (h : ∀ y, continuous (λ a, (g a) y)) : continuous g :=
continuous_induced_rng (continuous_pi_iff.mpr h)

end weak_dual

/-- The weak topology is the topology coarsest topology on `E` such that all
functionals `λ x, top_dual_pairing 𝕜 E v x` are continuous. -/
@[derive [add_comm_monoid, module 𝕜, topological_space, has_continuous_add],
nolint has_inhabited_instance]
def weak_space (𝕜 E) [comm_semiring 𝕜] [topological_space 𝕜] [has_continuous_add 𝕜]
  [has_continuous_const_smul 𝕜 𝕜] [add_comm_monoid E] [module 𝕜 E] [topological_space E] :=
weak_bilin (top_dual_pairing 𝕜 E).flip

theorem tendsto_iff_forall_eval_tendsto_top_dual_pairing
  {l : filter α} {f : α → weak_dual 𝕜 E} {x : weak_dual 𝕜 E} :
  tendsto f l (𝓝 x) ↔
    ∀ y, tendsto (λ i, top_dual_pairing 𝕜 E (f i) y) l (𝓝 (top_dual_pairing 𝕜 E x y)) :=
weak_bilin.tendsto_iff_forall_eval_tendsto _ continuous_linear_map.coe_injective

end weak_star_topology
