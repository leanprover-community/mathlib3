/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import category_theory.abelian.projective
import algebra.category.Module.abelian
import linear_algebra.finsupp_vector_space
import algebra.module.projective

/-!
# The category of `R`-modules has enough projectives.
-/

universes v u

open category_theory
open category_theory.limits
open linear_map

open_locale Module

/-- The categorical notion of projective object agrees with the explicit module-theoretic notion. -/
-- Note we only prove this when `R` and `P` live in the same universe.
-- Otherwise to use `of_lifting_property'` we need to deal with
-- morphisms between modules in different universes.
theorem is_projective.iff_projective {R : Type v} [ring R]
  {P : Type v} [add_comm_group P] [module R P] :
  is_projective R P ↔ projective (Module.of R P) :=
⟨λ h, { factors := λ E X f e epi, h.lifting_property _ _ ((Module.epi_iff_surjective _).mp epi), },
  λ h, is_projective.of_lifting_property' (λ E X mE mX sE sX f g s,
  begin
    resetI,
    haveI : epi ↟f := (Module.epi_iff_surjective ↟f).mpr s,
    exact ⟨projective.factor_thru ↟g ↟f, projective.factor_thru_comp ↟g ↟f⟩,
  end)⟩

namespace Module
variables {R : Type u} [ring R] {M : Module.{v} R}

/-- Modules that have a basis are projective. -/
lemma projective_of_free {ι : Type*} {v : ι → M} (hv : is_basis R v) : projective M :=
/-
If we could prove `is_projective.iff_projective` without universe restrictions we could write:
```
projective.of_iso (Module.of_self_iso _)
  ((is_projective.iff_projective).mp (is_projective.of_free hv))
```
but for now it seems easier to just reprove it.
-/
{ factors := begin
  introsI X E f e e_epi,
  have : ∀ i, ∃ x, e x = f (v i) := λ i, range_eq_top.1 (range_eq_top_of_epi e) (f (v i)),
  choose w h using this,
  exact ⟨hv.constr w, hv.ext (by simp [h])⟩
end }

/-- The category of modules has enough projectives, since every module is a quotient of a free
    module. -/
instance Module_enough_projectives : enough_projectives (Module.{u} R) :=
{ presentation :=
  λ M, have hb : is_basis R (λ m : M, finsupp.single m (1 : R)) := finsupp.is_basis_single_one,
  ⟨{ P := Module.of R (M →₀ R),
    projective := projective_of_free finsupp.is_basis_single_one,
    f := hb.constr id,
    epi := (epi_iff_range_eq_top _).mpr
      (range_eq_top.2 (λ m, ⟨finsupp.single m (1 : R), by simp⟩)) }⟩, }

end Module
