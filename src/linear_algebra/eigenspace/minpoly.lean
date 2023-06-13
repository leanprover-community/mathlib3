/-
Copyright (c) 2020 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/

import linear_algebra.eigenspace.basic
import field_theory.minpoly.field

/-!
# Eigenvalues are the roots of the minimal polynomial.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Tags

eigenvalue, minimal polynomial
-/

universes u v w

namespace module
namespace End

open polynomial finite_dimensional
open_locale polynomial

variables {K : Type v} {V : Type w} [field K] [add_comm_group V] [module K V]

lemma eigenspace_aeval_polynomial_degree_1
  (f : End K V) (q : K[X]) (hq : degree q = 1) :
  eigenspace f (- q.coeff 0 / q.leading_coeff) = (aeval f q).ker :=
calc
  eigenspace f (- q.coeff 0 / q.leading_coeff)
      = (q.leading_coeff • f - algebra_map K (End K V) (- q.coeff 0)).ker
    : by { rw eigenspace_div, intro h, rw leading_coeff_eq_zero_iff_deg_eq_bot.1 h at hq, cases hq }
  ... = (aeval f (C q.leading_coeff * X + C (q.coeff 0))).ker
    : by { rw [C_mul', aeval_def], simp [algebra_map, algebra.to_ring_hom], }
  ... = (aeval f q).ker
    : by rwa ← eq_X_add_C_of_degree_eq_one

lemma ker_aeval_ring_hom'_unit_polynomial
  (f : End K V) (c : (K[X])ˣ) :
  (aeval f (c : K[X])).ker = ⊥ :=
begin
  rw polynomial.eq_C_of_degree_eq_zero (degree_coe_units c),
  simp only [aeval_def, eval₂_C],
  apply ker_algebra_map_End,
  apply coeff_coe_units_zero_ne_zero c
end

theorem aeval_apply_of_has_eigenvector {f : End K V}
  {p : K[X]} {μ : K} {x : V} (h : f.has_eigenvector μ x) :
  aeval f p x = (p.eval μ) • x :=
begin
  apply p.induction_on,
  { intro a, simp [module.algebra_map_End_apply] },
  { intros p q hp hq, simp [hp, hq, add_smul] },
  { intros n a hna,
    rw [mul_comm, pow_succ, mul_assoc, alg_hom.map_mul, linear_map.mul_apply, mul_comm, hna],
    simp only [mem_eigenspace_iff.1 h.1, smul_smul, aeval_X, eval_mul, eval_C, eval_pow, eval_X,
      linear_map.map_smulₛₗ, ring_hom.id_apply, mul_comm] }
end

theorem is_root_of_has_eigenvalue {f : End K V} {μ : K} (h : f.has_eigenvalue μ) :
  (minpoly K f).is_root μ :=
begin
  rcases (submodule.ne_bot_iff _).1 h with ⟨w, ⟨H, ne0⟩⟩,
  refine or.resolve_right (smul_eq_zero.1 _) ne0,
  simp [← aeval_apply_of_has_eigenvector ⟨H, ne0⟩, minpoly.aeval K f],
end

variables [finite_dimensional K V] (f : End K V)

variables {f} {μ : K}

theorem has_eigenvalue_of_is_root (h : (minpoly K f).is_root μ) :
  f.has_eigenvalue μ :=
begin
  cases dvd_iff_is_root.2 h with p hp,
  rw [has_eigenvalue, eigenspace],
  intro con,
  cases (linear_map.is_unit_iff_ker_eq_bot _).2 con with u hu,
  have p_ne_0 : p ≠ 0,
  { intro con,
    apply minpoly.ne_zero f.is_integral,
    rw [hp, con, mul_zero] },
  have h_deg := minpoly.degree_le_of_ne_zero K f p_ne_0 _,
  { rw [hp, degree_mul, degree_X_sub_C, polynomial.degree_eq_nat_degree p_ne_0] at h_deg,
    norm_cast at h_deg,
    linarith, },
  { have h_aeval := minpoly.aeval K f,
    revert h_aeval,
    simp [hp, ← hu] },
end

theorem has_eigenvalue_iff_is_root :
  f.has_eigenvalue μ ↔ (minpoly K f).is_root μ :=
⟨is_root_of_has_eigenvalue, has_eigenvalue_of_is_root⟩

/-- An endomorphism of a finite-dimensional vector space has finitely many eigenvalues. -/
noncomputable instance (f : End K V) : fintype f.eigenvalues :=
set.finite.fintype $ show {μ | eigenspace f μ ≠ ⊥}.finite,
begin
  have h : minpoly K f ≠ 0 := minpoly.ne_zero f.is_integral,
  convert (minpoly K f).root_set_finite K using 1,
  ext μ,
  simp [polynomial.root_set_def, polynomial.mem_roots h, ← has_eigenvalue_iff_is_root,
    has_eigenvalue],
end

end End
end module
