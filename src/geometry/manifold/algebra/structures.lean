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

section smooth_module

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{H : Type*} [topological_space H]
{E : Type*} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H)
{H' : Type*} [topological_space H']
{E' : Type*} [normed_group E'] [normed_space 𝕜 E'] (I' : model_with_corners 𝕜 E' H')
{H'' : Type*} [topological_space H'']
{E'' : Type*} [normed_group E''] [normed_space 𝕜 E''] (I'' : model_with_corners 𝕜 E'' H'')

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A smooth semimodule, over a semiring which is also a smooth manifold, is a
semimodule in which scalar multiplication is smooth. In applications, R will be a smooth
semiring and M a smooth additive semigroup, but this is not needed for the definition -/
class smooth_semimodule (R : Type*) (M : Type*)
  [semiring R] [topological_space R] [charted_space H R] [smooth_manifold_with_corners I R]
  [topological_space M] [add_comm_monoid M] [semimodule R M] [topological_semimodule R M]
  [charted_space H' M] [smooth_manifold_with_corners I' M] : Prop :=
(smooth_smul : smooth (I.prod I') I' (λp : R × M, p.1 • p.2))
end prio

section

variables {I I' I''} {R : Type*} {M : Type*}
[semiring R] [topological_space R] [charted_space H R] [smooth_manifold_with_corners I R]
[topological_space M] [add_comm_monoid M] [semimodule R M] [charted_space H' M]
[smooth_manifold_with_corners I' M] [topological_semimodule R M] [smooth_semimodule I I' R M]

lemma smooth_smul : smooth (I.prod I') I' (λ p : R × M, p.1 • p.2) :=
smooth_semimodule.smooth_smul

lemma smooth.smul {N : Type*} [topological_space N] [charted_space H'' N]
  [smooth_manifold_with_corners I'' N] {f : N → R} {g : N → M}
  (hf : smooth I'' I f) (hg : smooth I'' I' g) : smooth I'' I' (λ p, f p • g p) :=
smooth_smul.comp (hf.prod_mk hg)

end

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A smooth module, over a ring which is also a smooth manifold, is a module in which
scalar multiplication is smooth. In applications, `R` will be a smooth ring and `M` a
smooth additive group, but this is not needed for the definition -/
class smooth_module (R : Type*) (M : Type*)
  [ring R] [topological_space R] [charted_space H R] [smooth_manifold_with_corners I R]
  [topological_space M] [add_comm_group M] [module R M] [topological_module R M]
  [charted_space H' M] [smooth_manifold_with_corners I' M]
  extends smooth_semimodule I I' R M : Prop

/-- A smooth vector space is a smooth module over a field. -/
abbreviation smooth_vector_space (R : Type*) (M : Type*)
  [normed_field R] [normed_space 𝕜 R]
  [topological_space M] [add_comm_group M] [vector_space R M] [topological_vector_space R M]
  [charted_space H' M] [smooth_manifold_with_corners I' M] :=
smooth_module Isf(𝕜, R) I' R M
end prio

end smooth_module

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

instance normed_group_smooth_module {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] :
  smooth_vector_space Isf(𝕜, E) 𝕜 E :=
{ smooth_smul :=
  begin
    rw smooth_iff,
    refine ⟨continuous_smul, λ x y, _⟩,
    simp only [prod.mk.eta] with mfld_simps,
    rw times_cont_diff_on_univ,
    exact times_cont_diff_smul,
  end,
  ..normed_space_lie_group }
