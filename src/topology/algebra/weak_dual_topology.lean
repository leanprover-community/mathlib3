/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä and Heather Macbeth
-/
import tactic
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
@[derive [inhabited, has_coe_to_fun]] def weak_dual := E →L[𝕜] 𝕜

instance [inhabited 𝕜] : inhabited (weak_dual 𝕜 E) :=
{ default := { to_fun := (λ (x : E) , 0),
               map_add' := by simp only [add_zero, forall_const],
               map_smul' := by simp only [forall_const, smul_zero],
               cont := continuous_const, }, }

instance weak_dual.has_coe_to_fun :
  has_coe_to_fun (weak_dual 𝕜 E) := ⟨_, (λ (x' : weak_dual 𝕜 E), (λ (x : E), x'.to_fun x)) ⟩

instance weak_dual.topology :
  topological_space (weak_dual 𝕜 E) :=
topological_space.induced (λ x' : weak_dual 𝕜 E, λ z : E, x' z) Pi.topological_space

lemma weak_dual.test_continuous' :
  continuous (λ (x' : (weak_dual 𝕜 E)), (λ (z : E), x' z)) :=
continuous_induced_dom

lemma weak_dual.test_continuous (z : E) : continuous (λ (x' : weak_dual 𝕜 E), x' z) :=
(continuous_pi_iff.mp (weak_dual.test_continuous' 𝕜 E)) z

theorem weak_dual.tendsto_iff_forall_test_tendsto {γ : Type*} {F : filter γ}
  {ψs : γ → weak_dual 𝕜 E} {ψ : weak_dual 𝕜 E} :
  tendsto ψs F (𝓝 ψ) ↔ ∀ (z : E), tendsto (λ i, (ψs(i)) z) F (𝓝 (ψ z)) :=
begin
  split,
  { intros weak_star_conv,
    exact tendsto_pi.mp
      (tendsto.comp (continuous.tendsto (weak_dual.test_continuous' 𝕜 E) ψ) weak_star_conv), },
  { intro h_lim_forall,
    have h_lim := tendsto_pi.mpr h_lim_forall,
    rwa [nhds_induced, tendsto_comap_iff], },
end

/-- If the scalars `𝕜` are a commutative semiring, then `weak_dual 𝕜 E` is an additive commutative
    monoid (and in fact moreover a module over `𝕜`). -/
instance weak_dual.add_comm_monoid (𝕜 : Type*) [topological_space 𝕜] [comm_semiring 𝕜]
  [has_continuous_add 𝕜] [has_continuous_mul 𝕜]
  (E : Type*) [topological_space E] [add_comm_group E] [has_continuous_add E]
  [module 𝕜 E] [has_continuous_smul 𝕜 E] :
  add_comm_monoid (weak_dual 𝕜 E) :=
restrict_scalars.add_comm_monoid 𝕜 𝕜 (E →L[𝕜] 𝕜)

/-- If the scalars `𝕜` are a commutative semiring, then `weak_dual 𝕜 E` is (an additive
    commutative monoid and moreover) a module over `𝕜`. -/
instance weak_dual.module (𝕜 : Type*) [topological_space 𝕜] [comm_semiring 𝕜]
  [has_continuous_add 𝕜] [has_continuous_mul 𝕜]
  (E : Type*) [topological_space E] [add_comm_group E] [has_continuous_add E]
  [module 𝕜 E] [has_continuous_smul 𝕜 E] :
  module 𝕜 (weak_dual 𝕜 E) :=
restrict_scalars.module 𝕜 𝕜 (E →L[𝕜] 𝕜)

end weak_star_topology
