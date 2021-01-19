/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import field_theory.minpoly
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

--TODO(Commelin): refactor normal to extend `is_algebraic`??

/-- Typeclass for normal field extension: `K` is a normal extension of `F` iff the minimal
polynomial of every element `x` in `K` splits in `K`, i.e. every conjugate of `x` is in `K`. -/
@[class] def normal : Prop :=
∀ x : K, is_integral F x ∧ splits (algebra_map F K) (minpoly F x)

instance normal_self : normal F F :=
λ x, ⟨is_integral_algebra_map, by { rw minpoly.eq_X_sub_C', exact splits_X_sub_C _ }⟩

variables {K}

theorem normal.is_integral [h : normal F K] (x : K) : is_integral F x := (h x).1

theorem normal.splits [h : normal F K] (x : K) : splits (algebra_map F K) (minpoly F x) := (h x).2

variables (K)

theorem normal.exists_is_splitting_field [normal F K] [finite_dimensional F K] :
  ∃ p : polynomial F, is_splitting_field F K p :=
begin
  obtain ⟨s, hs⟩ := finite_dimensional.exists_is_basis_finset F K,
  refine ⟨s.prod $ λ x, minpoly F x,
    splits_prod _ $ λ x hx, normal.splits F x,
    subalgebra.to_submodule_injective _⟩,
  rw [algebra.coe_top, eq_top_iff, ← hs.2, submodule.span_le, set.range_subset_iff],
  refine λ x, algebra.subset_adjoin (multiset.mem_to_finset.mpr $
    (mem_roots $ mt (map_eq_zero $ algebra_map F K).1 $
    finset.prod_ne_zero_iff.2 $ λ x hx, _).2 _),
  { exact minpoly.ne_zero (normal.is_integral F x) },
  rw [is_root.def, eval_map, ← aeval_def, alg_hom.map_prod],
  exact finset.prod_eq_zero x.2 (minpoly.aeval _ _)
end

section normal_tower

variables (E : Type*) [field E] [algebra F E] [algebra K E] [is_scalar_tower F K E]

lemma normal.tower_top_of_normal [h : normal F E] : normal K E :=
begin
  intros x,
  cases h x with hx hhx,
  rw is_scalar_tower.algebra_map_eq F K E at hhx,
  exact ⟨is_integral_of_is_scalar_tower x hx, polynomial.splits_of_splits_of_dvd (algebra_map K E)
    (polynomial.map_ne_zero (minpoly.ne_zero hx))
    ((polynomial.splits_map_iff (algebra_map F K) (algebra_map K E)).mpr hhx)
    (minpoly.dvd_map_of_is_scalar_tower F K x)⟩,
end

variables {F} {E} {E' : Type*} [field E'] [algebra F E']

lemma normal.of_alg_equiv [h : normal F E] (f : E ≃ₐ[F] E') : normal F E' :=
begin
  intro x,
  cases h (f.symm x) with hx hhx,
  have H := is_integral_alg_hom f.to_alg_hom hx,
  rw [alg_equiv.to_alg_hom_eq_coe, alg_equiv.coe_alg_hom, alg_equiv.apply_symm_apply] at H,
  use H,
  apply polynomial.splits_of_splits_of_dvd (algebra_map F E') (minpoly.ne_zero hx),
  { rw ← alg_hom.comp_algebra_map f.to_alg_hom,
    exact polynomial.splits_comp_of_splits (algebra_map F E) f.to_alg_hom.to_ring_hom hhx },
  { apply minpoly.dvd _ _,
    rw ← add_equiv.map_eq_zero_iff f.symm.to_add_equiv,
    exact eq.trans (polynomial.aeval_alg_hom_apply f.symm.to_alg_hom x
      (minpoly F (f.symm x))).symm (minpoly.aeval _ _) },
end

lemma alg_equiv.transfer_normal (f : E ≃ₐ[F] E') : normal F E ↔ normal F E' :=
⟨λ h, by exactI normal.of_alg_equiv f, λ h, by exactI normal.of_alg_equiv f.symm⟩

end normal_tower
