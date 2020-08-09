/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/

/-|
# Smooth structures

In this file we define smooth structures that build on Lie groups. We prefer using the term smooth
instead of Lie mainly because Lie ring has currently another use in mathematics.
-/

import geometry.manifold.algebra.lie_group

open_locale manifold

section smooth_ring
variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{H : Type*} [topological_space H]
{E : Type*} [normed_group E] [normed_space 𝕜 E]

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A smooth semiring is a semiring where addition and multiplication are smooth. -/
class smooth_semiring (I : model_with_corners 𝕜 E H)
  (R : Type*) [semiring R] [topological_space R] [topological_semiring R] [charted_space H R]
  [smooth_manifold_with_corners I R]
  extends has_smooth_add I R, has_smooth_mul I R : Prop
end prio

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A smooth ring is a ring where the ring operations are smooth. -/
class smooth_ring (I : model_with_corners 𝕜 E H)
  (R : Type*) [ring R] [topological_space R] [topological_ring R] [charted_space H R]
  [smooth_manifold_with_corners I R]
  extends lie_add_group I R, has_smooth_mul I R : Prop
end prio

@[priority 100] -- see Note [lower instance priority]
instance smooth_ring.to_smooth_semiring {I : model_with_corners 𝕜 E H}
  {R : Type*} [ring R] [topological_space R] [topological_ring R] [charted_space H R]
  [smooth_manifold_with_corners I R] [t : smooth_ring I R] :
  smooth_semiring I R := { ..t }

end smooth_ring

instance field_smooth_ring {𝕜 : Type*} [nondiscrete_normed_field 𝕜] :
  smooth_ring (model_with_corners_self 𝕜 𝕜) 𝕜 :=
{ smooth_mul :=
  begin
    rw smooth_iff,
    refine ⟨continuous_mul, λ x y, _⟩,
    simp only [prod.mk.eta] with mfld_simps,
    rw times_cont_diff_on_univ,
    exact times_cont_diff_mul,
  end,
  ..field_lie_group }

lemma {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] normed_space_smooth_smul :
  smooth (Isf(𝕜).prod Isf(𝕜, E)) Isf(𝕜, E) (λp : 𝕜 × E, p.1 • p.2) :=
  begin
    rw smooth_iff,
    refine ⟨continuous_smul, λ x y, _⟩,
    simp only [prod.mk.eta] with mfld_simps,
    rw times_cont_diff_on_univ,
    exact times_cont_diff_smul,
  end
