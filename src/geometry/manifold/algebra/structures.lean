/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import geometry.manifold.algebra.lie_group

/-!
# Smooth structures

In this file we define smooth structures that build on Lie groups. We prefer using the term smooth
instead of Lie mainly because Lie ring has currently another use in mathematics.
-/

open_locale manifold

section smooth_ring
variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{H : Type*} [topological_space H]
{E : Type*} [normed_group E] [normed_space 𝕜 E]

set_option default_priority 100 -- see Note [default priority]

/-- A smooth (semi)ring is a (semi)ring `R` where addition and multiplication are smooth.
If `R` is a ring, then negation is automatically smooth, as it is multiplication with `-1`. -/
-- See note [Design choices about smooth algebraic structures]
class smooth_ring (I : model_with_corners 𝕜 E H)
  (R : Type*) [semiring R] [topological_space R] [charted_space H R]
  extends has_smooth_add I R : Prop :=
(smooth_mul : smooth (I.prod I) I (λ p : R×R, p.1 * p.2))

instance smooth_ring.to_has_smooth_mul (I : model_with_corners 𝕜 E H)
  (R : Type*) [semiring R] [topological_space R] [charted_space H R] [h : smooth_ring I R] :
  has_smooth_mul I R := { ..h }

instance smooth_ring.to_lie_add_group (I : model_with_corners 𝕜 E H)
  (R : Type*) [ring R] [topological_space R] [charted_space H R] [smooth_ring I R] :
  lie_add_group I R :=
{ compatible := λ e e', has_groupoid.compatible (times_cont_diff_groupoid ⊤ I),
  smooth_add := smooth_add I,
  smooth_neg := by simpa only [neg_one_mul] using @smooth_mul_left 𝕜 _ H _ E _ _ I R _ _ _ _ (-1) }

end smooth_ring

instance field_smooth_ring {𝕜 : Type*} [nondiscrete_normed_field 𝕜] :
  smooth_ring 𝓘(𝕜) 𝕜 :=
{ smooth_mul :=
  begin
    rw smooth_iff,
    refine ⟨continuous_mul, λ x y, _⟩,
    simp only [prod.mk.eta] with mfld_simps,
    rw times_cont_diff_on_univ,
    exact times_cont_diff_mul,
  end,
  ..normed_space_lie_add_group }

variables {𝕜 R E H : Type*} [topological_space R] [topological_space H]
  [nondiscrete_normed_field 𝕜] [normed_group E] [normed_space 𝕜 E]
  [charted_space H R] (I : model_with_corners 𝕜 E H)

/-- A smooth (semi)ring is a topological (semi)ring. This is not an instance for technical reasons,
see note [Design choices about smooth algebraic structures]. -/
lemma topological_ring_of_smooth [semiring R] [smooth_ring I R] :
  topological_ring R :=
{ .. has_continuous_mul_of_smooth I, .. has_continuous_add_of_smooth I }
