/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.abelian.projective
import algebra.category.Module.abelian
import linear_algebra.basis

universes v u

open category_theory
open category_theory.limits
open linear_map

namespace Module
variables {R : Type u} [ring R] {M : Module.{v} R}

/-- Modules that have a basis are projective. -/
lemma projective_of_free {ι : Type*} {v : ι → M} (hv : is_basis R v) : projective M :=
begin
  introsI X E f e e_epi,
  have : ∀ i, ∃ x, e x = f (v i) := λ i, range_eq_top.1 (range_eq_top_of_epi e) (f (v i)),
  choose w h using this,
  exact ⟨hv.constr w, hv.ext (by simp [h])⟩
end

lemma Module_enough_projectives : enough_projectives (Module.{u} R) :=
begin
  classical,
  intro M,
  refine ⟨Module.of R (M →₀ R), _⟩,
  have hb : is_basis R (λ m : M, finsupp.single m (1 : R)),
  { sorry, },
  refine ⟨hb.constr id, ⟨_, _⟩⟩,
  { apply projective_of_free,
    exact hb },
  apply epi_of_range_eq_top,
  rw range_eq_top,
  intro m,
  use finsupp.single m (1 : R),
  simp
end

end Module
