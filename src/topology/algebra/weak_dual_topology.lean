/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Heather Macbeth
-/
import topology.algebra.module

/-!
# Weak dual topology

This file defines the weak-* topology on duals of suitable topological modules `E` over suitable
topological semirings `𝕜`. The (weak) dual consists of continuous linear functionals `E →L[𝕜] 𝕜`
from `E` to scalars `𝕜`. The weak-* topology is the coarsest topology on this dual
`weak_dual 𝕜 E := (E →L[𝕜] 𝕜)` w.r.t. which the evaluation maps at all `z : E` are continuous.

The weak dual is a module over `𝕜` if the semiring `𝕜` is commutative.

## Main definitions

The main definitions are the type `weak_dual 𝕜 E` and a topology instance on it.

* `weak_dual 𝕜 E` is a type synonym for `dual 𝕜 E` (when the latter is defined), both are equal to
  the type `E →L[𝕜] 𝕜` of continuous linear maps from a module `E` over `𝕜` to the ring `𝕜`.
* `weak_dual_topology` is the topology instance on `weak_dual 𝕜 E`, the weak-* topology, i.e.,
  the coarsest topology making the evaluation maps at all `z : E` are continuous.

## Main results

The results in this file primarily concern the characterization of the weak-* topology.

## Notations

No new notation is introduced.

## Implementation notes

The weak-* topology is defined as the induced topology under the mapping that associates to a dual
element `x'` the functional `E → 𝕜`, when the space `E → 𝕜` of functionals is equipped with the
topology of pointwise convergence (product topology).

The general definition assumes that `𝕜` is a topological semiring in the sense of the typeclasses
 `topological_space 𝕜`, `semiring 𝕜`, `has_continuous_add 𝕜`, `has_continuous_mul 𝕜`,
and that the space `E` is a topological module over `𝕜` in the sense of the typeclasses
`topological_space E`, `add_comm_monoid E`, `has_continuous_add E`, `module 𝕜 E`,
`has_continuous_smul 𝕜 E`.

## References

* https://en.wikipedia.org/wiki/Weak_topology#Weak-*_topology

## Tags

weak-star, weak dual

-/

noncomputable theory
open filter
open_locale topological_space

section weak_star_topology
/-!
### Weak star topology on duals of topological modules
In this section, we define the weak-* topology on duals of suitable topological modules `E` over
suitable topological semirings `𝕜`. The (weak) dual `weak_dual 𝕜 E` consists of continuous linear
functionals `E →L[𝕜] 𝕜` from `E` to scalars `𝕜`. The weak-* topology is the coarsest topology on
this dual `weak_dual 𝕜 E := (E →L[𝕜] 𝕜)` w.r.t. which the evaluation maps at all `z : E` are
continuous.

The weak dual is a module over `𝕜` if the semiring `𝕜` is commutative.
-/

variables (𝕜 : Type*) [topological_space 𝕜] [semiring 𝕜]
variables (E : Type*) [topological_space E] [add_comm_monoid E] [module 𝕜 E]

/-- The (weak) dual of a topological module `E` over a topological semiring `𝕜` consists of
continuous linear functionals from `E` to scalars `𝕜`. It is a type synonym with the original
dual, but will be equipped with a different topology. -/
@[derive [inhabited, has_coe_to_fun]]
def weak_dual := E →L[𝕜] 𝕜

instance [has_continuous_add 𝕜] : add_comm_monoid (weak_dual 𝕜 E) := continuous_linear_map.add_comm_monoid

namespace weak_dual

variables [has_continuous_add 𝕜] [has_continuous_mul 𝕜]
variables [has_continuous_add E] [has_continuous_smul 𝕜 E]

/-- The weak-* topology instance `weak_dual_topology` on the dual of a topological module `E` over
a topological semiring `𝕜` is defined as the induced topology under the mapping that associates to
a dual element `x' : weak_dual 𝕜 E` the functional `E → 𝕜`, when the space `E → 𝕜` of functionals
is equipped with the topology of pointwise convergence (product topology). -/
instance : topological_space (weak_dual 𝕜 E) :=
topological_space.induced (λ x' : weak_dual 𝕜 E, λ z : E, x' z) Pi.topological_space

lemma eval_continuous' :
  continuous (λ (x' : (weak_dual 𝕜 E)), (λ (z : E), x' z)) :=
continuous_induced_dom

lemma eval_continuous (z : E) : continuous (λ (x' : weak_dual 𝕜 E), x' z) :=
(continuous_pi_iff.mp (eval_continuous' 𝕜 E)) z

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

instance : has_continuous_add (weak_dual 𝕜 E) :=
{ continuous_add := begin
    apply continuous_of_continuous_eval,
    intros z,
    rw continuous_def,
    intros V V_open,
    have W_open := continuous_def.mp (‹has_continuous_add 𝕜›.continuous_add) _ V_open,
    set W := ((λ (p : 𝕜 × 𝕜), p.fst + p.snd) ⁻¹' V) with h_W,
    --simp at whee,

    --rw continuous_iff_continuous_at,
    --intros p,

    --rw continuous_iff_ultrafilter,
    --intros p F h_F,
    --have whee := tendsto.prod_mk_nhds,

    --rw tendsto.prod_mk_nhds,
    --have whee := continuous_at.tendsto,
    --have whee := continuous_pi_iff,
    --rw continuous_iff_tends
    --have key := continuous.prod_map,
    sorry,
  end, }

--instance : has_continuous_smul 𝕜 (weak_dual 𝕜 E) := sorry

/-- If the scalars `𝕜` are a commutative semiring, then `weak_dual 𝕜 E` is a module over `𝕜`. -/
instance (𝕜 : Type*) [topological_space 𝕜] [comm_semiring 𝕜]
  [has_continuous_add 𝕜] [has_continuous_mul 𝕜]
  (E : Type*) [topological_space E] [add_comm_group E] [has_continuous_add E]
  [module 𝕜 E] [has_continuous_smul 𝕜 E] :
  module 𝕜 (weak_dual 𝕜 E) :=
continuous_linear_map.module

end weak_dual

end weak_star_topology
