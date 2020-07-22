/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import field_theory.minimal_polynomial
import field_theory.splitting_field
import linear_algebra.finite_dimensional

/-!
# Normal field extensions

In this file we define normal field extensions and prove that for a finite extension, being normal
is the same as being a splitting field (TODO).

## Main Definitions

- `normal F K` where `K` is a field extension of `F`.
-/

noncomputable theory
open_locale classical
open polynomial

universes u v

variables (F : Type u) (K : Type v) [field F] [field K] [algebra F K]

/-- Typeclass for normal field extension: `K` is a normal extension of `F` iff the minimal
polynomial of every element `x` in `K` splits in `K`, i.e. every conjugate of `x` is in `K`. -/
@[class] def normal : Prop :=
∀ x : K, ∃ H : is_integral F x, splits (algebra_map F K) (minimal_polynomial H)

theorem normal.is_integral [h : normal F K] (x : K) : is_integral F x := (h x).fst

theorem normal.splits [h : normal F K] (x : K) :
  splits (algebra_map F K) (minimal_polynomial $ normal.is_integral F K x) := (h x).snd

-- MOVE
theorem subalgebra.to_submodule_top : ((⊤ : subalgebra F K) : submodule F K) = ⊤ :=
submodule.ext $ λ x, iff_of_true algebra.mem_top trivial

theorem normal.exists_is_splitting_field [normal F K] [finite_dimensional F K] :
  ∃ p : polynomial F, is_splitting_field F K p :=
begin
  obtain ⟨s, hs⟩ := finite_dimensional.exists_is_basis_finset F K,
  refine ⟨s.prod $ λ x, minimal_polynomial $ normal.is_integral F K x,
    splits_prod _ $ λ x hx, normal.splits F K x,
    subalgebra.to_submodule_injective _⟩,
  rw [subalgebra.to_submodule_top F K, eq_top_iff, ← hs.2, submodule.span_le, set.range_subset_iff],
  refine λ x, algebra.subset_adjoin ((mem_roots $ mt (map_eq_zero $ algebra_map F K).1 $
    finset.prod_ne_zero_iff.2 $ λ x hx, _).2 _),
  { exact minimal_polynomial.ne_zero _ },
  rw [is_root.def, eval_map, ← aeval_def, alg_hom.map_prod],
  exact finset.prod_eq_zero x.2 (minimal_polynomial.aeval _)
end
