/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors : Aaron Anderson
-/

import linear_algebra.basic

/-!
# Simple Modules

## Main Definitions
  * `is_simple_module` indicates that a module has no proper submodules
  (the only submodules are `⊥` and `⊤`).
  * A `division_ring` structure on the endomorphism ring of a simple module.

## Main Results
  * Schur's Lemma: `bijective_or_eq_zero_of_simple` shows that a linear map between simple modules
  is either bijective or 0, leading to a `division_ring` structure on the endomorphism ring.

## TODO
  * Semisimple modules, Artin-Wedderburn Theory
  * Unify with the work on Schur's Lemma in a category theory context

-/

variables (R : Type*) [comm_ring R] (M : Type*) [add_comm_group M] [module R M]

abbreviation is_simple_module := (is_simple_lattice (submodule R M))

instance is_simple_module.nontrivial [is_simple_module R M] : nontrivial M :=
⟨⟨0, begin
  have h : (⊥ : submodule R M) ≠ ⊤ := bot_ne_top,
  contrapose! h,
  ext,
  simp [submodule.mem_bot,submodule.mem_top, h x],
end⟩⟩

variables {R} {M} {N : Type*} [add_comm_group N] [module R N]

namespace linear_map

theorem injective_or_eq_zero_of_simple [is_simple_module R M] (f : M →ₗ[R] N) :
  function.injective f ∨ f = 0 :=
begin
  rw [← ker_eq_bot, ← ker_eq_top],
  apply eq_bot_or_eq_top,
end

theorem surjective_or_eq_zero_of_simple [is_simple_module R N] (f : M →ₗ[R] N) :
  function.surjective f ∨ f = 0 :=
begin
  rw [← range_eq_top, ← range_le_bot_iff, le_bot_iff, or_comm],
  apply eq_bot_or_eq_top,
end

/-- Schur's Lemma for linear maps between (possibly distinct) simple modules -/
theorem bijective_or_eq_zero_of_simple [is_simple_module R M] [is_simple_module R N]
  (f : M →ₗ[R] N) :
  function.bijective f ∨ f = 0 :=
begin
  by_cases h : f = 0,
  { right,
    exact h },
  exact or.intro_left _ ⟨or.resolve_right f.injective_or_eq_zero_of_simple h,
    or.resolve_right f.surjective_or_eq_zero_of_simple h⟩,
end

/-- Schur's Lemma makes the endomorphism ring of a simple module a division ring. -/
noncomputable instance [decidable_eq (M →ₗ[R] M)] [is_simple_module R M] :
  division_ring (M →ₗ[R] M) :=
{ inv := λ f, if h : f = 0 then 0 else (linear_map.inverse f
    (equiv.of_bijective _ (f.bijective_or_eq_zero_of_simple.resolve_right h)).inv_fun
    (equiv.of_bijective _ (f.bijective_or_eq_zero_of_simple.resolve_right h)).left_inv
    (equiv.of_bijective _ (f.bijective_or_eq_zero_of_simple.resolve_right h)).right_inv),
  exists_pair_ne := ⟨0, 1, begin
    have h := exists_pair_ne M,
    contrapose! h,
    intros x y,
    simp_rw [ext_iff, one_app, zero_apply] at h,
    rw [← h x, h y],
  end⟩,
  mul_inv_cancel := begin
    intros a a0,
    change (a * (dite _ _ _)) = 1,
    ext,
    rw [dif_neg a0, mul_eq_comp, one_app, comp_apply],
    exact (equiv.of_bijective _ (a.bijective_or_eq_zero_of_simple.resolve_right a0)).right_inv x,
  end,
  inv_zero := dif_pos rfl,
.. (infer_instance : ring (M →ₗ[R] M))}

end linear_map
