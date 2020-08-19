/-
Copyright (c) 2020 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexander Bentkamp.
-/

import field_theory.algebraic_closure
import linear_algebra.finsupp

/-!
# Eigenvectors and eigenvalues

This file defines eigenvectors and eigenvalues, as well as generalized
eigenvectors and eigenvalues.

An eigenvector of a linear map `f` is a vector `x` such that `f x = μ • x` for
some scalar `μ`. If `x ≠ 0`, the scalar `μ` is called an eigenvalue. We express
this by writing `eigenvector f μ x` and `eigenvalue f μ x`, respectively.

A generalized eigenvector of a linear map `f` is a nonzero vector `x` such that
`(f x - μ • x) ^ k = 0` for some scalar `μ` and some natural number `k`.
If `x ≠ 0`, the scalar `μ` is called a generalized eigenvalue. We express this by
writing `generalized_eigenvector f k μ x`. and `generalized_eigenvalue f k μ x`,
respectively.

We follow Axler's approach [axler1996] that allows us to prove a lot of
properties of eigenvectors without choosing a basis, without determinants and
without matrices.

## Notations

The expression `algebra_map α (β →ₗ[α] β)` appears very often, which is why we
use `am` as a local notation for it.

## References

* [Sheldon Axler, *Down with determinants!*,
  https://www.maa.org/sites/default/files/pdf/awards/Axler-Ford-1996.pdf][axler1996]
* https://en.wikipedia.org/wiki/Eigenvalues_and_eigenvectors

## Tags

eigenvector, eigenvalues, eigen
-/

universes u v w

open vector_space principal_ideal_ring polynomial finite_dimensional

variables {α : Type v} {β : Type w} [add_comm_group β]

/-- An eigenvector of a linear map `f` is a vector `x` such that there exists a scalar `μ`
    with `f x = μ • x`. -/
def eigenvector [field α] [vector_space α β]
  (f : β →ₗ[α] β) (μ : α) (x : β) : Prop := f x = μ • x

/-- An eigenvalue of a nonzero eigenvector `x` of a linear map `f` is
    the scalar `μ` such that `f x = μ • x`. -/
def eigenvalue [field α] [vector_space α β]
  (f : β →ₗ[α] β) (μ : α) (x : β) : Prop := x ≠ 0 ∧ f x = μ • x

local notation `am` := algebra_map α (β →ₗ[α] β)

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
  ∃ (x : β) (c : α), eigenvalue f c x :=
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
  have h_q_eval₂ : polynomial.eval₂ am f q = q.leading_coeff • f + am (q.coeff 0),
  { rw [polynomial.eq_X_add_C_of_degree_eq_one h_deg_q],
    simp [eval₂_mul_noncomm am f (λ x y, ( algebra.commutes' x y).symm)],
    simp [leading_coeff_X_add_C _ _ (λ h, h_q_ne_0 (leading_coeff_eq_zero.1 h))],
    refl },
  obtain ⟨x, hx₁, hx₂⟩ : ∃ (x : β), eval₂ am f q x = 0 ∧ ¬x = 0,
  { rw [linear_map.is_unit_iff, linear_map.ker_eq_bot', not_forall] at hq_nonunit,
    simpa only [not_imp] using hq_nonunit },
  have h_fx_x_lin_dep: leading_coeff q • f x + coeff q 0 • x = 0,
  { rw h_q_eval₂ at hx₁,
    exact hx₁ },
  show ∃ (x : β) (c : α), x ≠ 0 ∧ f x = c • x,
  { use x,
    use -(coeff q 0 / q.leading_coeff),
    refine ⟨hx₂, _⟩,
    rw neg_smul,
    have : (leading_coeff q)⁻¹ • leading_coeff q • f x = (leading_coeff q)⁻¹ • -(coeff q 0 • x) :=
      congr_arg (λ x, (leading_coeff q)⁻¹ • x) (add_eq_zero_iff_eq_neg.1 h_fx_x_lin_dep),
    simpa [smul_smul, inv_mul_cancel (λ h, h_q_ne_0 (leading_coeff_eq_zero.1 h)),
      mul_comm _ (coeff q 0), div_eq_mul_inv.symm] }
end

/-- Nonzero eigenvectors corresponding to distinct eigenvalues of a linear operator are
    linearly independent (Axler's Proposition 2.2) -/
lemma eigenvectors_linear_independent [field α] [vector_space α β]
  (f : β →ₗ[α] β) (μs : set α) (xs : μs → β) (h_eigenval : ∀ μ : μs, eigenvalue f μ (xs μ)):
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
        by rw [linear_map.map_smul, linear_map.sub_apply, (h_eigenval _).2,
          module.endomorphism_algebra_map_apply2, sub_self, smul_zero],
      have h_useless_filter : finset.filter (λ (a : μs), l'_f a ≠ 0) l_support' = l_support',
      { rw finset.filter_congr _,
        { apply finset.filter_true },
        { apply_instance },
        exact λ μ hμ, iff_of_true ((h_l_support' μ).2 hμ) true.intro },
      have bodies_eq : ∀ (μ : μs), l'_f μ • xs μ = g (l μ • xs μ),
      { intro μ,
        dsimp only [g, l'_f],
        rw [linear_map.map_smul, linear_map.sub_apply, (h_eigenval _).2,
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
      exact (h_eigenval μ₀).1 ((smul_eq_zero.1 hl).resolve_left h) },

    show l = 0,
    { ext μ,
      by_cases h_cases : μ = μ₀,
      { rw h_cases,
        assumption },
      exact h_lμ_eq_0 μ h_cases } }
end

/-- A generalized eigenvector (also called eventual eigenvector) of a linear map
    $f$ is a vector $x$ such that $(f - \mu I) ^ k) x = 0$ for some scalar $\mu$
    and some natural number $k$ (where $I$ is the identity map). -/
def generalized_eigenvector [field α] [vector_space α β]
  (f : β →ₗ[α] β) (k : ℕ) (μ : α) (x : β) : Prop := ((f - am μ) ^ k) x = 0

/-- A generalized eigenvalue (also called eventual eigenvalue) of a linear map
    $f$ is a scalar $\mu$ such that $(f - \mu I) ^ k) x = 0$ for some nonzero
    vector $x$ and some natural number $k$ (where $I$ is the identity map). -/
def generalized_eigenvalue [field α] [vector_space α β]
  (f : β →ₗ[α] β) (k : ℕ) (μ : α) (x : β) : Prop := x ≠ 0 ∧ ((f - am μ) ^ k) x = 0

/-- The natural number of a generalized eigenvalue is never 0. -/
lemma exp_ne_zero_of_generalized_eigenvalue_ne_zero [field α] [vector_space α β]
  {f : β →ₗ[α] β} {k : ℕ} {μ : α} {x : β} (h : generalized_eigenvalue f k μ x) :
  k ≠ 0 :=
begin
  rcases h with ⟨h_nz, h⟩,
  contrapose h_nz,
  rw not_not at h_nz ⊢,
  rwa [h_nz, pow_zero] at h
end

/-- A generalized eigenvalue for some number `k` is also a generalized
    eigenvalue for number larger than `k`. -/
lemma generalized_eigenvalue_zero_beyond [field α] [vector_space α β]
  {f : β →ₗ[α] β} {k : ℕ} {μ : α} {x : β} (h : generalized_eigenvalue f k μ x) :
  ∀ m : ℕ, k ≤ m → generalized_eigenvalue f m μ x :=
begin
  intros m hm,
  refine ⟨h.1, _⟩,
  rw ←pow_sub_mul_pow _ hm,
  change ((f - am μ) ^ (m - k)) (((f - am μ) ^ k) x) = 0,
  unfold generalized_eigenvalue at h,
  rw [h.2, linear_map.map_zero]
end

/-- All eigenvalues are generalized eigenvalues. -/
lemma generalized_eigenvalue_of_eigenvalue [field α] [vector_space α β]
  {f : β →ₗ[α] β} {k : ℕ} {μ : α} {x : β} (hx : eigenvalue f μ x) (hk : 0 < k) :
  generalized_eigenvalue f k μ x :=
begin
  rw [generalized_eigenvalue, ←nat.succ_pred_eq_of_pos hk, pow_succ'],
  change x ≠ 0 ∧ ((f - am μ) ^ nat.pred k) ((f - am μ) x) = 0,
  have : (f - am μ) x = 0 := by simp [hx.2, module.endomorphism_algebra_map_apply2],
  simp [this, hx.1]
end

/-- The set of generalized eigenvectors of f corresponding to a generalized eigenvalue μ equals the
    kernel of (f - am μ) ^ n, where n is the dimension of the vector space (Axler's Lemma 3.1). -/
lemma generalized_eigenvalue_dim
  [field α] [vector_space α β] [finite_dimensional α β]
  (f : β →ₗ[α] β) (μ : α) (x : β) :
  (∃ k : ℕ, generalized_eigenvalue f k μ x)
    ↔ generalized_eigenvalue f (findim α β) μ x :=
begin
  classical,
  split,
  { show (∃ (k : ℕ), generalized_eigenvalue f k μ x) → x ≠ 0 ∧ ((f - am μ) ^ findim α β) x = 0,
    intro h_exists_eigenval,
    let k := @nat.find (λ k : ℕ, generalized_eigenvalue f k μ x) _ h_exists_eigenval,
    let z := (λ i : fin k, ((f - am μ) ^ (i : ℕ)) x),

    have h_x_nz : x ≠ 0,
    { rcases h_exists_eigenval with ⟨k, h⟩,
      exact h.1 },

    have h_lin_indep : linear_independent α z,
    { rw linear_independent_iff,
      intros l hl,
      ext i,
      induction h_i_val : i.val using nat.strong_induction_on with i_val ih generalizing i,
      simp only [h_i_val.symm] at *,
      clear h_i_val i_val,

      have h_zero_of_lt : ∀ j, j < i → ((f - am μ) ^ (k - i.val - 1)) (l j • z j) = 0,
      { intros j hj,
        simp [ih j hj j rfl] },

      have h_zero_beyond_k : ∀ m, k ≤ m → ((f - am μ) ^ m) x = 0,
      { intros m hm,
        apply (generalized_eigenvalue_zero_beyond
            (@nat.find_spec (λ k : ℕ, generalized_eigenvalue f k μ x) _ h_exists_eigenval) _ hm).2 },

      have h_zero_of_gt : ∀ j, j > i → ((f - am μ) ^ (k - i.val - 1)) (l j • z j) = 0,
      { intros j hj,
        dsimp only [z],
        rw [linear_map.map_smul],
        change l j • ((f - am μ) ^ (k - i.val - 1) * ((f - am μ) ^ ↑j)) x = 0,
        rw [←pow_add, h_zero_beyond_k, smul_zero],
        rw [nat.sub_sub, ←nat.sub_add_comm (nat.succ_le_of_lt i.2)],
        apply nat.le_sub_right_of_add_le,
        apply nat.add_le_add_left,
        rw ←nat.lt_iff_add_one_le,
        unfold_coes,
        change i.val < (j : ℕ),
        exact hj },

      have h_zero_of_ne : ∀ j, j ≠ i → ((f - am μ) ^ (k - i.val - 1)) (l j • z j) = 0,
      { intros j hj,
        cases lt_or_gt_of_ne hj with h_lt h_gt,
        apply h_zero_of_lt j h_lt,
        apply h_zero_of_gt j h_gt },

      have h_zero_of_not_support : i ∉ l.support → ((f - am μ) ^ (k - i.val - 1)) (l i • z i) = 0,
      { intros hi,
        rw [finsupp.mem_support_iff, not_not] at hi,
        rw [hi, zero_smul, linear_map.map_zero] },

      have h_l_smul_pow_k_sub_1 : l i • (((f - am μ) ^ (k - 1)) x) = 0,
      { have h_k_sub_1 : k - i.val - 1 + i.val = k - 1,
        { rw ←nat.sub_add_comm,
          { rw nat.sub_add_cancel,
            apply le_of_lt i.2 },
          { apply nat.le_sub_left_of_add_le,
            apply nat.succ_le_of_lt i.2 } },
        rw [←h_k_sub_1, pow_add],
        let g := (f - am μ) ^ (k - i.val - 1),
        rw [finsupp.total_apply, finsupp.sum] at hl,
        have := congr_arg g hl,
        rw [linear_map.map_sum, linear_map.map_zero g] at this,
        dsimp only [g] at this,
        rw finset.sum_eq_single i (λ j _, h_zero_of_ne j) h_zero_of_not_support at this,
        simp only [linear_map.map_smul, z] at this,
        apply this },

      have h_pow_k_sub_1 : ((f - am μ) ^ (k - 1)) x ≠ 0 :=
        not_and.1 (@nat.find_min (λ k : ℕ, generalized_eigenvalue f k μ x) _ h_exists_eigenval _
            (nat.sub_lt (nat.lt_of_le_of_lt (nat.zero_le _) i.2) nat.zero_lt_one)) h_x_nz,

      show l i = 0,
      { contrapose h_pow_k_sub_1 with h_li_ne_0,
        rw not_not,
        apply (smul_eq_zero.1 h_l_smul_pow_k_sub_1).resolve_left h_li_ne_0 } },

    show x ≠ 0 ∧ ((f - am μ) ^ findim α β) x = 0,
    { split,
      { exact h_x_nz },
      apply (generalized_eigenvalue_zero_beyond
        (@nat.find_spec (λ k : ℕ, generalized_eigenvalue f k μ x) _ h_exists_eigenval) _ _).2,
      rw [←cardinal.nat_cast_le, ←cardinal.lift_mk_fin _, ←cardinal.lift_le, cardinal.lift_lift],
      rw findim_eq_dim,
      apply h_lin_indep.le_lift_dim} },

  { show generalized_eigenvalue f (findim α β) μ x → (∃ (k : ℕ), generalized_eigenvalue f k μ x),
    exact λh, ⟨_, h⟩, }
end

lemma generalized_eigenvector_restrict_aux [field α] [vector_space α β]
  (f : β →ₗ[α] β) (p : submodule α β) (k : ℕ) (μ : α) (x : p)
  (hfp : ∀ (x : β), x ∈ p → f x ∈ p) :
  (((f.restrict p p hfp - algebra_map _ _ μ) ^ k) x : β)
  = ((f - algebra_map _ _ μ) ^ k) x :=
begin
  induction k with k ih,
  { rw [pow_zero, pow_zero, linear_map.one_app, linear_map.one_app] },
  { rw [pow_succ, pow_succ],
    change ((f.restrict p p hfp - algebra_map _ _ μ) (((f.restrict p p hfp - algebra_map _ _ μ) ^ k) x) : β) =
        (f - algebra_map _ _ μ) (((f - algebra_map _ _ μ) ^ k) x),
    rw [linear_map.sub_apply, linear_map.sub_apply, linear_map.restrict_apply, ←ih],
    refl }
end

/-- If `f` maps a subspace `p` into itself, then the generalized eigenvectors of
    `f` restricted to `p` are the generalized eigenvectors of `f` that lie in
    `p`.
-/
lemma generalized_eigenvector_restrict [field α] [vector_space α β]
  (f : β →ₗ[α] β) (p : submodule α β) (k : ℕ) (μ : α) (x : p) (hfp : ∀ (x : β), x ∈ p → f x ∈ p) :
  generalized_eigenvector (linear_map.restrict f p p hfp) k μ x
    ↔ generalized_eigenvector f k μ x :=
begin
  rw [generalized_eigenvector, subtype.ext_iff,  generalized_eigenvector_restrict_aux],
  simp [generalized_eigenvector]
end

/-- If a vector is a generalized eigenvalue for some number `k`, then it is
    also a generalized eigenvalue for the dimension of the vector space. -/
lemma generalized_eigenvalue_dim_of_any
  [field α] [vector_space α β] [finite_dimensional α β]
  {f : β →ₗ[α] β} {μ : α}
  {k : ℕ} {x : β} (h : generalized_eigenvalue f k μ x) :
  generalized_eigenvalue f (findim α β) μ x :=
begin
  rw ←generalized_eigenvalue_dim,
  { exact ⟨k, h⟩ }
end

/-- Kernel and range of $(f - \mu I) ^ n$ are disjoint, where $f$ is a linear
    map, $\mu$ is a scalar, $I$ is the identity matrix, and $n$ is the dimension of
    the vector space. -/
lemma generalized_eigenvec_disjoint_range_ker
  [field α] [vector_space α β] [finite_dimensional α β]
  (f : β →ₗ[α] β) (μ : α) :
  disjoint ((f - am μ) ^ findim α β).range ((f - am μ) ^ findim α β).ker :=
begin
  rintros v ⟨⟨u, _, hu⟩, hv⟩,
  have h2n : ((f - am μ) ^ (findim α β + findim α β)) u = 0,
  { rw [pow_add, ←linear_map.mem_ker.1 hv, ←hu], refl },
  have hn : ((f - am μ) ^ findim α β) u = 0,
  { by_cases h_cases: u = 0,
    { simp [h_cases] },
    { apply (generalized_eigenvalue_dim_of_any ⟨h_cases, h2n⟩).2 } },
  have hv0 : v = 0, by rw [←hn, hu],
  show v ∈ ↑⊥, by simp [hv0]
end

/-- The kernel of $(f - \mu I) ^ k$ for $k > 0$ has positive dimension if $\mu$
    is an eigenvalue. -/
lemma pos_dim_eigenker_of_eigenval [field α] [vector_space α β]
  {f : β →ₗ[α] β} {n : ℕ} {μ : α} {x : β} (hx : eigenvalue f μ x) :
  0 < dim α ((f - am μ) ^ n.succ).ker :=
begin
  have x_mem : x ∈ ((f - am μ) ^ n.succ).ker,
  { simp [pow_succ', hx.2, module.endomorphism_algebra_map_apply2] },
  apply dim_pos_iff_exists_ne_zero.2 (exists.intro (⟨x, x_mem⟩ : ((f - am μ) ^ n.succ).ker) _),
  intros h,
  apply hx.1,
  exact congr_arg subtype.val h,
end

/-- Variant of `pos_dim_eigenker_of_eigenval` for finite dimensional vector spaces. -/
lemma pos_findim_eigenker_of_eigenval
  [field α] [vector_space α β] [finite_dimensional α β]
  {f : β →ₗ[α] β} {n : ℕ} {μ : α} {x : β} (hx : eigenvalue f μ x) :
  0 < findim α ((f - am μ) ^ n.succ).ker :=
begin
  apply cardinal.nat_cast_lt.1,
  rw findim_eq_dim,
  apply pos_dim_eigenker_of_eigenval hx,
end

/-- The kernel of $(f - \mu I) ^ k$ is contained in the span of all generalized eigenvectors. -/
lemma eigenker_le_span_gen_eigenvec [field α] [vector_space α β]
  (f : β →ₗ[α] β) (μ₀ : α) (n : ℕ) :
((f - am μ₀) ^ n).ker
  ≤ submodule.span α ({x : β | ∃ (k : ℕ) (μ : α), generalized_eigenvector f k μ x}) :=
by exact λ x hx, submodule.subset_span ⟨n, μ₀, linear_map.mem_ker.1 hx⟩

/-- If $x$ is in the range of $(f - \mu I) ^ k$, then so is $f(x)$. -/
lemma image_mem_eigenrange_of_mem_eigenrange [field α] [vector_space α β]
  {f : β →ₗ[α] β} {μ : α} {x : β} {n : ℕ}
  (hx : x ∈ ((f - am μ) ^ n).range) :
  f x ∈ ((f - am μ) ^ n).range :=
begin
  rw linear_map.mem_range at *,
  rcases hx with ⟨w, hw⟩,
  use f w,
  have hcommutes : f.comp ((f - am μ) ^ n) = ((f - am μ) ^ n).comp f :=
    algebra.mul_sub_algebra_map_pow_commutes f μ n,
  rw [←linear_map.comp_apply, ←hcommutes, linear_map.comp_apply, hw],
end

/-- The generalized eigenvectors of f span the vectorspace β. (Axler's Proposition 3.4). -/
lemma generalized_eigenvector_span
  [field α] [is_alg_closed α] [vector_space α β] [finite_dimensional α β]
  (f : β →ₗ[α] β) :
  submodule.span α {x | ∃ k μ, generalized_eigenvector f k μ x} = ⊤ :=
begin
  rw ←top_le_iff,
  tactic.unfreeze_local_instances,
  induction h_dim : findim α β using nat.strong_induction_on with n ih generalizing β,
  cases n,
  { have h_findim_top: findim α (⊤ : submodule α β) = 0 := eq.trans findim_top h_dim,
    have h_top_eq_bot : (⊤ : submodule α β) = ⊥ := findim_eq_zero.1 h_findim_top,
    simp only [h_top_eq_bot, bot_le] },
  { have h_dim_pos : 0 < findim α β,
    { rw [h_dim],
      apply nat.zero_lt_succ },
    obtain ⟨x, μ₀, hx_ne_0, hμ₀⟩ : ∃ (x : β) (μ₀ : α), x ≠ 0 ∧ f x = μ₀ • x,
    { apply exists_eigenvalue f
        (findim_pos_iff_exists_ne_zero.1 h_dim_pos) },
    let V₁ := ((f - am μ₀) ^ n.succ).ker,
    let V₂ := ((f - am μ₀) ^ n.succ).range,
    have h_disjoint : disjoint V₂ V₁,
    { simp only [V₁, V₂, h_dim.symm],
      exact generalized_eigenvec_disjoint_range_ker f μ₀ },
    have h_dim_add : findim α V₂ + findim α V₁ = findim α β,
    { apply linear_map.findim_range_add_findim_ker },
    have h_dim_V₁_pos : 0 < findim α V₁,
    { apply pos_findim_eigenker_of_eigenval ⟨hx_ne_0, hμ₀⟩ },
    have h_findim_V₂ : findim α V₂ < n.succ := by omega,
    have h_f_V₂ : ∀ (x : β), x ∈ V₂ → f x ∈ V₂,
    { intros x hx,
      apply image_mem_eigenrange_of_mem_eigenrange hx, },
    have hV₂ : V₂ ≤ submodule.span α ({x : β | ∃ (k : ℕ) (μ : α), generalized_eigenvector f k μ x}),
    { have : V₂ ≤ submodule.span α ({x : β | ∃ (k : ℕ) (μ : α), generalized_eigenvector f k μ x} ∩ V₂),
      { rw ←subtype.image_preimage_val,
        rw ←submodule.subtype_eq_val V₂,
        rw submodule.span_image (submodule.subtype V₂),
        rw set.preimage_set_of_eq,
        rw submodule.subtype_eq_val,
        have h₀ : ∀ p, submodule.map (submodule.subtype V₂) ⊤
              ≤ submodule.map (submodule.subtype V₂) p
              ↔ ⊤ ≤ p
            := λ _, (linear_map.map_le_map_iff' (submodule.ker_subtype V₂)),
        have := submodule.range_subtype V₂,
        unfold linear_map.range at this,
        rw this at h₀,
        rw h₀,
        have := ih (findim α V₂) h_findim_V₂ (f.restrict V₂ V₂ h_f_V₂) rfl,
        simp only [generalized_eigenvector_restrict] at this,
        apply this },
      refine le_trans this _,
      apply submodule.span_mono,
      apply set.inter_subset_left },
    have hV₁ : V₁ ≤ submodule.span α ({x : β | ∃ (k : ℕ) (μ : α), generalized_eigenvector f k μ x}),
    { apply eigenker_le_span_gen_eigenvec },
    show ⊤ ≤ submodule.span α {x : β | ∃ (k : ℕ) (μ : α), generalized_eigenvector f k μ x},
    { rw ←submodule.eq_top_of_disjoint V₂ V₁ h_dim_add h_disjoint,
      apply sup_le hV₂ hV₁ } }
end
