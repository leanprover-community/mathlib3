/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import ring_theory.adjoin.basic
import ring_theory.power_basis

/-!
# Power basis for `algebra.adjoin R {x}`

This file defines the canonical power basis on `algebra.adjoin R {x}`,
where `x` is an integral element over `R`.
-/


variables {K S : Type*} [field K] [comm_ring S] [algebra K S]

namespace algebra

open polynomial
open power_basis

lemma power_basis_is_basis {x : S} (hx : _root_.is_integral K x) :
  is_basis K (λ (i : fin (minpoly K x).nat_degree),
    (⟨x, subset_adjoin (set.mem_singleton x)⟩ ^ (i : ℕ) : adjoin K ({x} : set S))) :=
begin
  have hST : function.injective (algebra_map (adjoin K ({x} : set S)) S) := subtype.coe_injective,
  have hx' : _root_.is_integral K
    (show adjoin K ({x} : set S), from ⟨x, subset_adjoin (set.mem_singleton x)⟩),
  { apply (is_integral_algebra_map_iff hST).mp,
    convert hx,
    apply_instance },
  have minpoly_eq := minpoly.eq_of_algebra_map_eq hST hx' rfl,
  refine ⟨_, _root_.eq_top_iff.mpr _⟩,
  { have := hx'.linear_independent_pow,
    rwa minpoly_eq at this },
  { rintros ⟨y, hy⟩ _,
    have := hx'.mem_span_pow,
    rw minpoly_eq at this,
    apply this,
    { rw [adjoin_singleton_eq_range] at hy,
      obtain ⟨f, rfl⟩ := (aeval x).mem_range.mp hy,
      use f,
      ext,
      exact (is_scalar_tower.algebra_map_aeval K (adjoin K {x}) S ⟨x, _⟩ _).symm } }
end

/-- The power basis `1, x, ..., x ^ (d - 1)` for `K[x]`,
where `d` is the degree of the minimal polynomial of `x`. -/
noncomputable def adjoin.power_basis {x : S} (hx : _root_.is_integral K x) :
  power_basis K (adjoin K ({x} : set S)) :=
{ gen := ⟨x, subset_adjoin (set.mem_singleton x)⟩,
  dim := (minpoly K x).nat_degree,
  is_basis := power_basis_is_basis hx }

end algebra
