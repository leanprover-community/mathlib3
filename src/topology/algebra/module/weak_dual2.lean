/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Moritz Doll
-/
import topology.algebra.module.basic
import linear_algebra.bilinear_map

noncomputable theory
open filter
open_locale topological_space

variables {α 𝕜 E F : Type*}

section weak_topology

@[derive [add_comm_monoid, module 𝕜]]
def weak_space [comm_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E] [add_comm_monoid F] [module 𝕜 F]
  (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) := E

section semiring

variables [topological_space 𝕜] [comm_semiring 𝕜]
variables [add_comm_monoid E] [module 𝕜 E]
variables [add_comm_monoid F] [module 𝕜 F]
variables (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

instance : topological_space (weak_space B) :=
topological_space.induced (λ x y, B x y) Pi.topological_space

lemma coe_fn_continuous : continuous (λ (x : weak_space B) y, B x y) :=
continuous_induced_dom

lemma eval_continuous (y : F) : continuous (λ x : weak_space B, B x y) :=
( continuous_pi_iff.mp (coe_fn_continuous B)) y

lemma continuous_of_continuous_eval [topological_space α] {g : α → weak_space B}
  (h : ∀ y, continuous (λ a, B (g a) y)) : continuous g :=
continuous_induced_rng (continuous_pi_iff.mpr h)

/-- The coercion `(λ x y, B x y) : E → (F → 𝕜)` is an embedding. -/
lemma bilin_embedding {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (hB : function.injective B) :
  embedding (λ (x : weak_space B)  y, B x y) :=
function.injective.embedding_induced $ linear_map.coe_injective.comp hB

theorem tendsto_iff_forall_eval_tendsto {l : filter α} {f : α → (weak_space B)} {x : weak_space B}
  (hB : function.injective B) : tendsto f l (𝓝 x) ↔ ∀ y, tendsto (λ i, B (f i) y) l (𝓝 (B x y)) :=
by rw [← tendsto_pi_nhds, embedding.tendsto_nhds_iff (bilin_embedding hB)]

/-- Addition in `weak_space B` is continuous. -/
instance [has_continuous_add 𝕜] : has_continuous_add (weak_space B) :=
begin
  refine ⟨continuous_induced_rng _⟩,
  refine cast (congr_arg _ _) (((coe_fn_continuous B).comp continuous_fst).add
    ((coe_fn_continuous B).comp continuous_snd)),
  ext,
  simp only [function.comp_app, pi.add_apply, map_add, linear_map.add_apply],
end

end semiring

end weak_topology

section weak_star_topology

/-- The canonical pairing of a vector space and its topological dual. -/
def top_dual_pairing (𝕜 E) [comm_semiring 𝕜] [topological_space 𝕜] [has_continuous_add 𝕜]
  [add_comm_monoid E] [module 𝕜 E] [topological_space E] [has_continuous_add E]
  [has_continuous_const_smul 𝕜 𝕜] :
  (E →L[𝕜] 𝕜) →ₗ[𝕜] E →ₗ[𝕜] 𝕜 := continuous_linear_map.coe_lm 𝕜

variables [comm_semiring 𝕜] [topological_space 𝕜] [has_continuous_add 𝕜]
variables [has_continuous_const_smul 𝕜 𝕜]
variables [add_comm_monoid E] [module 𝕜 E] [topological_space E] [has_continuous_add E]

lemma dual_pairing_apply (v : (E →L[𝕜] 𝕜)) (x : E) : top_dual_pairing 𝕜 E v x = v x := rfl

/-- The weak star topology is the topology coarsest topology on `E →L[𝕜] 𝕜` such that all
functionals `λ v, top_dual_pairing 𝕜 E v x` are continuous. -/
@[derive [add_comm_monoid, module 𝕜, topological_space, has_continuous_add]]
def weak_star_dual (𝕜 E) [comm_semiring 𝕜] [topological_space 𝕜] [has_continuous_add 𝕜]
  [has_continuous_const_smul 𝕜 𝕜]
  [add_comm_monoid E] [module 𝕜 E] [topological_space E] [has_continuous_add E] :=
weak_space (top_dual_pairing 𝕜 E)

instance fun_like_weak_dual : fun_like (weak_star_dual 𝕜 E) E (λ _, 𝕜) :=
by {dunfold weak_star_dual, dunfold weak_space, apply_instance}

/-- The weak star topology is the topology coarsest topology on `E` such that all
functionals `λ x, top_dual_pairing 𝕜 E v x` are continuous. -/
@[derive [add_comm_monoid, module 𝕜, topological_space, has_continuous_add]]
def weak_dual (𝕜 E) [comm_semiring 𝕜] [topological_space 𝕜] [has_continuous_add 𝕜]
  [has_continuous_const_smul 𝕜 𝕜]
  [add_comm_monoid E] [module 𝕜 E] [topological_space E] [has_continuous_add E] :=
weak_space (top_dual_pairing 𝕜 E).flip

end weak_star_topology
