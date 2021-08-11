/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä and Heather Macbeth
-/
import topology.algebra.module

noncomputable theory
open filter
open_locale topological_space

section weak_star_topology

/-!
### Weak star topology on duals of topological modules
In this section, we define the weak-* topology on duals of suitable topological modules `E` over
suitable topological semirings `𝕜`. The (weak) dual consists of continuous linear functionals
`E →L[𝕜] 𝕜` from `E` to scalars `𝕜`. The weak-* topology is the coarsest topology on this dual
`weak_dual 𝕜 E := (E →L[𝕜] 𝕜)` w.r.t. which the evaluation maps at all `z : E` are continuous.

The weak dual is a module over `𝕜` if the semiring `𝕜` is commutative.
-/

variables (𝕜 : Type*) [topological_space 𝕜] [semiring 𝕜]
variables [has_continuous_add 𝕜] [has_continuous_mul 𝕜]
variables (E : Type*) [topological_space E] [add_comm_monoid E] [has_continuous_add E]
variables [module 𝕜 E] [has_continuous_smul 𝕜 E]

/-- The (weak) dual of a topological module `E` over a topological semiring `𝕜` consists of
continuous linear functionals from `E` to scalars `𝕜`. It is a type synonym with the original
dual, but will be equipped with a different topology. -/
@[derive [inhabited, has_coe_to_fun, add_comm_monoid]]
def weak_dual := E →L[𝕜] 𝕜

namespace weak_dual

instance weak_dual_topology :
  topological_space (weak_dual 𝕜 E) :=
topological_space.induced (λ x' : weak_dual 𝕜 E, λ z : E, x' z) Pi.topological_space

lemma eval_continuous' :
  continuous (λ (x' : (weak_dual 𝕜 E)), (λ (z : E), x' z)) :=
continuous_induced_dom

lemma eval_continuous (z : E) : continuous (λ (x' : weak_dual 𝕜 E), x' z) :=
(continuous_pi_iff.mp (weak_dual.eval_continuous' 𝕜 E)) z

lemma continuous_of_continuous_eval {α : Type*} [topological_space α]
  {g : α → weak_dual 𝕜 E} (h : ∀ z, continuous (λ a, g a z)) : continuous g :=
continuous_induced_rng (continuous_pi_iff.mpr h)

theorem tendsto_iff_forall_eval_tendsto {γ : Type*} {F : filter γ}
  {ψs : γ → weak_dual 𝕜 E} {ψ : weak_dual 𝕜 E} :
  tendsto ψs F (𝓝 ψ) ↔ ∀ z : E, tendsto (λ i, ψs i z) F (𝓝 (ψ z)) :=
begin
  rw ←tendsto_pi,
  split,
  { intros weak_star_conv,
    exact tendsto.comp (continuous.tendsto (weak_dual.eval_continuous' 𝕜 E) ψ) weak_star_conv, },
  { intro h_lim_forall,
    rwa [nhds_induced, tendsto_comap_iff], },
end

/-- If the scalars `𝕜` are a commutative semiring, then `weak_dual 𝕜 E` is (an additive
    commutative monoid and moreover) a module over `𝕜`. -/
instance weak_dual_module (𝕜 : Type*) [topological_space 𝕜] [comm_semiring 𝕜]
  [has_continuous_add 𝕜] [has_continuous_mul 𝕜]
  (E : Type*) [topological_space E] [add_comm_group E] [has_continuous_add E]
  [module 𝕜 E] [has_continuous_smul 𝕜 E] :
  module 𝕜 (weak_dual 𝕜 E) :=
continuous_linear_map.module

end weak_dual

end weak_star_topology
