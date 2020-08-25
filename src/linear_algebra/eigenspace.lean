/-
Copyright (c) 2020 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexander Bentkamp.
-/

import field_theory.algebraic_closure
import linear_algebra.finsupp

/-!
# Eigenvectors and eigenvalues

This file defines eigenspaces and eigenvalues.

An eigenspace of a linear map `f` for a scalar `μ` is the kernel of the map `(f - μ • id)`.
The nonzero elements of an eigenspace are eigenvectors `x`. They have the property `f x = μ • x`.
If there are eigenvectors for a scalar `μ`, the scalar `μ` is called an eigenvalue.

## Notations

The expression `algebra_map α (β →ₗ[α] β)` appears very often, which is why we
use `am` as a local notation for it.

## References

* [Sheldon Axler, *Down with determinants!*,
  https://www.maa.org/sites/default/files/pdf/awards/Axler-Ford-1996.pdf][axler1996]
* https://en.wikipedia.org/wiki/Eigenvalues_and_eigenvectors

## Tags

eigenspace, eigenvector, eigenvalue, eigen
-/

universes u v w

open vector_space principal_ideal_ring polynomial finite_dimensional

variables {α : Type v} {β : Type w} [add_comm_group β]

local notation `am` := algebra_map α (β →ₗ[α] β)

/-- The subspace `eigenspace f μ` for a linear map `f` and a scalar `μ` consists of all vectors `x`
    such that `f x = μ • x`. -/
def eigenspace [field α] [vector_space α β] (f : β →ₗ[α] β) (μ : α) : submodule α β :=
(f - am μ).ker

/-- A nonzero element of an eigenspace is an eigenvector. -/
def eigenvector [field α] [vector_space α β] (f : β →ₗ[α] β) (μ : α) (x : β) : Prop :=
x ≠ 0 ∧ x ∈ eigenspace f μ

/-- A scalar `μ` is an eigenvalue for a linear map `f` if there are nonzero vectors `x`
    such that `f x = μ • x`. -/
def eigenvalue [field α] [vector_space α β] (f : β →ₗ[α] β) (a : α) : Prop :=
eigenspace f a ≠ ⊥.

lemma eigenspace_div [field α] [vector_space α β] (f : β →ₗ[α] β) (a b : α) (hb : b ≠ 0):
  eigenspace f (a / b) = (b • f - am a).ker :=
calc
  eigenspace f (a / b) = eigenspace f (b⁻¹ * a) : by { dsimp [(/)], rw mul_comm }
  ... = (f - (b⁻¹ * a) • linear_map.id).ker : by refl
  ... = (f - b⁻¹ • a • linear_map.id).ker : by rw smul_smul
  ... = (f - b⁻¹ • am a).ker : by refl
  ... = (b • (f - b⁻¹ • am a)).ker : by rw linear_map.ker_smul _ b hb
  ... = (b • f - am a).ker : by rw [smul_sub, smul_inv_smul' hb]

lemma eigenspace_eval₂_polynomial_degree_1 [field α] [vector_space α β]
  (f : β →ₗ[α] β) (q : polynomial α) (hq : degree q = 1) :
  eigenspace f (- q.coeff 0 / q.leading_coeff) = (eval₂ am f q).ker :=
calc
  eigenspace f (- q.coeff 0 / q.leading_coeff) = (q.leading_coeff • f - am (- q.coeff 0)).ker
    : by { rw eigenspace_div, intro h, rw leading_coeff_eq_zero_iff_deg_eq_bot.1 h at hq, cases hq }
  ... = (eval₂ am f (C q.leading_coeff * X + C (q.coeff 0))).ker
    : by { rw C_mul', simpa [algebra_map, algebra.to_ring_hom] }
  ... = (eval₂ am f q).ker
     : by { congr, apply (eq_X_add_C_of_degree_eq_one hq).symm }

lemma mem_eigenspace_iff [field α] [vector_space α β]
 {f : β →ₗ[α] β} {μ : α} {x : β} : x ∈ eigenspace f μ ↔ f x = μ • x :=
by rw [eigenspace, linear_map.mem_ker, linear_map.sub_apply, module.endomorphism_algebra_map_apply2,
   sub_eq_zero]

lemma ne_0_of_mem_factors {α : Type v} [field α] {p q : polynomial α}
  (hp : p ≠ 0) (hq : q ∈ factors p) : q ≠ 0 :=
begin
  intro h_q_eq_0,
  rw h_q_eq_0 at hq,
  apply hp ((associated_zero_iff_eq_zero p).1 _),
  rw ←multiset.prod_eq_zero hq,
  apply (factors_spec p hp).2
end

/-- Every linear operator on a vector space over an algebraically closed field has
    an eigenvalue. (Axler's Theorem 2.1.) -/
lemma exists_eigenvalue
  [field α] [is_alg_closed α] [vector_space α β] [finite_dimensional α β]
  (f : β →ₗ[α] β) (hex : ∃ v : β, v ≠ 0) :
  ∃ (c : α), eigenvalue f c :=
begin
  classical,
  obtain ⟨v, hv⟩ : ∃ v : β, v ≠ 0 := hex,
  have h_lin_dep : ¬ linear_independent α (λ n : ℕ, (f ^ n) v),
  { intro h_lin_indep,
    have : cardinal.mk ℕ < cardinal.omega,
      by apply (lt_omega_of_linear_independent h_lin_indep),
    have := cardinal.lift_lt.2 this,
    rw [cardinal.omega, cardinal.lift_lift] at this,
    apply lt_irrefl _ this, },
  obtain ⟨p, hp⟩ : ∃ p, ¬(eval₂ am f p v = 0 → p = 0),
  { exact not_forall.1 (λ h, h_lin_dep ((linear_independent_powers_iff_eval₂ f v).2 h)) },
  obtain ⟨h_eval_p, h_p_ne_0⟩ : eval₂ am f p v = 0 ∧ p ≠ 0 := not_imp.1 hp,
  have h_eval_p_not_unit : eval₂_ring_hom_noncomm am _ f p ∉ is_unit.submonoid (β →ₗ[α] β),
  { rw [is_unit.mem_submonoid_iff, linear_map.is_unit_iff, linear_map.ker_eq_bot'],
    intro h,
    exact hv (h v h_eval_p) },
  have h_eval_unit : ∀ (c : units (polynomial α)),
      (eval₂_ring_hom_noncomm am _ f) ↑c ∈ is_unit.submonoid (β →ₗ[α] β),
  { intro c,
    rw polynomial.eq_C_of_degree_eq_zero (degree_coe_units c),
    simp only [eval₂_ring_hom_noncomm, ring_hom.of, ring_hom.coe_mk, eval₂_C],
    rw [is_unit.mem_submonoid_iff, linear_map.is_unit_iff],
    apply module.endomorphism_algebra_map_ker,
    apply coeff_coe_units_zero_ne_zero c },
  obtain ⟨q, hq_factor, hq_nonunit⟩ : ∃ q, q ∈ factors p ∧ ¬ is_unit (eval₂ am f q),
  { simp only [←not_imp, (is_unit.mem_submonoid_iff _).symm],
    apply not_forall.1 (λ h, h_eval_p_not_unit (ring_hom_factors_submonoid
      (eval₂_ring_hom_noncomm am (λ x y, (algebra.commutes x y).symm) f)
      (is_unit.submonoid (β →ₗ[α] β)) p h_p_ne_0 h h_eval_unit)) },
  have h_q_ne_0 : q ≠ 0 := ne_0_of_mem_factors h_p_ne_0 hq_factor,
  have h_deg_q : q.degree = 1 := is_alg_closed.degree_eq_one_of_irreducible _ h_q_ne_0
    ((factors_spec p h_p_ne_0).1 q hq_factor),
  have h_eigenspace: eigenspace f (-q.coeff 0 / q.leading_coeff) = (eval₂ am f q).ker,
    from eigenspace_eval₂_polynomial_degree_1 f q h_deg_q,
  show ∃ (c : α), eigenvalue f c,
  { use -q.coeff 0 / q.leading_coeff,
    rw [eigenvalue, h_eigenspace],
    intro h_eval_ker,
    exact hq_nonunit ((linear_map.is_unit_iff (eval₂ am f q)).2 h_eval_ker) }
end

/-- Eigenvectors corresponding to distinct eigenvalues of a linear operator are
    linearly independent (Axler's Proposition 2.2) -/
lemma eigenvectors_linear_independent [field α] [vector_space α β]
  (f : β →ₗ[α] β) (μs : set α) (xs : μs → β)
  (h_eigenvec : ∀ μ : μs, eigenvector f μ (xs μ)) :
  linear_independent α xs :=
begin
  classical,
  rw linear_independent_iff,
  intros l hl,
  induction h_l_support : l.support using finset.induction with μ₀ l_support' hμ₀ ih generalizing l,
  { exact finsupp.support_eq_empty.1 h_l_support },
  { let l'_f := (λ μ : μs, (↑μ - ↑μ₀) * l μ),
    have h_l_support' : ∀ (μ : μs), l'_f μ ≠ 0 ↔ μ ∈ l_support',
    { intros μ,
      dsimp only [l'_f],
      rw [mul_ne_zero_iff, sub_ne_zero, ←not_iff_not, not_and_distrib, not_not, not_not, ←subtype.ext_iff],
      split,
      { intro h,
        cases h,
        { rwa h },
        { intro h_mem_l_support',
          apply finsupp.mem_support_iff.1 _ h,
          rw h_l_support,
          apply finset.subset_insert _ _ h_mem_l_support' } },
      { intro h,
        apply or_iff_not_imp_right.2,
        intro hlμ,
        have := finsupp.mem_support_iff.2 hlμ,
        rw [h_l_support, finset.mem_insert] at this,
        cc } },
    let l' : μs →₀ α := finsupp.on_finset l_support' l'_f (λ μ, (h_l_support' μ).1),
    have total_l' : (@linear_map.to_fun α (finsupp μs α) β _ _ _ _ _ (finsupp.total μs β α xs)) l' = 0,
    { let g := f - am μ₀,
      have h_gμ₀: g (l μ₀ • xs μ₀) = 0,
        by rw [linear_map.map_smul, linear_map.sub_apply, mem_eigenspace_iff.1 (h_eigenvec _).2,
          module.endomorphism_algebra_map_apply2, sub_self, smul_zero],
      have h_useless_filter : finset.filter (λ (a : μs), l'_f a ≠ 0) l_support' = l_support',
      { rw finset.filter_congr _,
        { apply finset.filter_true },
        { apply_instance },
        exact λ μ hμ, iff_of_true ((h_l_support' μ).2 hμ) true.intro },
      have bodies_eq : ∀ (μ : μs), l'_f μ • xs μ = g (l μ • xs μ),
      { intro μ,
        dsimp only [g, l'_f],
        rw [linear_map.map_smul, linear_map.sub_apply, mem_eigenspace_iff.1 (h_eigenvec _).2,
          module.endomorphism_algebra_map_apply2, ←sub_smul, smul_smul, mul_comm] },
      have := finsupp.total_on_finset _ l_support' l'_f xs _,
      unfold_coes at this,
      rw [this, ←linear_map.map_zero g,
          ←congr_arg g hl, finsupp.total_apply, finsupp.sum, linear_map.map_sum, h_l_support,
          finset.sum_insert hμ₀, h_gμ₀, zero_add],
      simp only [bodies_eq],
      congr,
      convert finset.filter_congr _,
      { apply finset.filter_true.symm },
      { apply_instance },
      exact λ μ hμ, iff_of_true ((h_l_support' μ).2 hμ) true.intro, },
    have h_l'_support_eq : l'.support = l_support',
    { dsimp only [l'],
      ext μ,
      rw finsupp.on_finset_mem_support l_support' l'_f _ μ,
      by_cases h_cases: μ ∈ l_support',
      { refine iff_of_true _ h_cases,
        exact (h_l_support' μ).2 h_cases },
      { refine iff_of_false _ h_cases,
        rwa not_iff_not.2 (h_l_support' μ) } },
    have l'_eq_0 : l' = 0 := ih l' total_l' h_l'_support_eq,

    have h_mul_eq_0 : ∀ μ : μs, (↑μ - ↑μ₀) * l μ = 0,
    { intro μ,
      calc (↑μ - ↑μ₀) * l μ = l' μ : rfl
      ... = 0 : by { rw [l'_eq_0], refl } },

    have h_lμ_eq_0 : ∀ μ : μs, μ ≠ μ₀ → l μ = 0,
    { intros μ hμ,
      apply or_iff_not_imp_left.1 (mul_eq_zero.1 (h_mul_eq_0 μ)),
      rwa [sub_eq_zero, ←subtype.ext_iff] },

    have h_sum_l_support'_eq_0 : finset.sum l_support' (λ (μ : ↥μs), l μ • xs μ) = 0,
    { rw ←finset.sum_const_zero,
      apply finset.sum_congr rfl,
      intros μ hμ,
      rw h_lμ_eq_0,
      apply zero_smul,
      intro h,
      rw h at hμ,
      contradiction },

    have : l μ₀ = 0,
    { rw [finsupp.total_apply, finsupp.sum, h_l_support,
          finset.sum_insert hμ₀, h_sum_l_support'_eq_0, add_zero] at hl,
      by_contra h,
      exact (h_eigenvec μ₀).1 ((smul_eq_zero.1 hl).resolve_left h) },

    show l = 0,
    { ext μ,
      by_cases h_cases : μ = μ₀,
      { rw h_cases,
        assumption },
      exact h_lμ_eq_0 μ h_cases } }
end
