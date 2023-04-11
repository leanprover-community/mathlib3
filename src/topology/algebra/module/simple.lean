/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import ring_theory.simple_module
import topology.algebra.module.basic

/-!
# The kernel of a linear function is closed or dense

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove (`linear_map.is_closed_or_dense_ker`) that the kernel of a linear function `f
: M →ₗ[R] N` is either closed or dense in `M` provided that `N` is a simple module over `R`. This
applies, e.g., to the case when `R = N` is a division ring.
-/

universes u v w

variables {R : Type u} {M : Type v} {N : Type w}
  [ring R] [topological_space R]
  [topological_space M] [add_comm_group M] [add_comm_group N]
  [module R M] [has_continuous_smul R M] [module R N]
  [has_continuous_add M] [is_simple_module R N]

/-- The kernel of a linear map taking values in a simple module over the base ring is closed or
dense. Applies, e.g., to the case when `R = N` is a division ring. -/
lemma linear_map.is_closed_or_dense_ker (l : M →ₗ[R] N) :
  is_closed (l.ker : set M) ∨ dense (l.ker : set M) :=
begin
  rcases l.surjective_or_eq_zero with (hl|rfl),
  { exact l.ker.is_closed_or_dense_of_is_coatom (linear_map.is_coatom_ker_of_surjective hl) },
  { rw linear_map.ker_zero,
    left,
    exact is_closed_univ },
end
