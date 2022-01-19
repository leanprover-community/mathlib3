/-
Copyright (c) 2020 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/

import field_theory.is_alg_closed.basic
import linear_algebra.finsupp
import linear_algebra.matrix.to_lin
import order.preorder_hom
import linear_algebra.charpoly.basic

/-!
# Eigenvectors and eigenvalues

This file defines eigenspaces, eigenvalues, and eigenvalues, as well as their generalized
counterparts. We follow Axler's approach [axler2015] because it allows us to derive many properties
without choosing a basis and without using matrices.

An eigenspace of a linear map `f` for a scalar `μ` is the kernel of the map `(f - μ • id)`. The
nonzero elements of an eigenspace are eigenvectors `x`. They have the property `f x = μ • x`. If
there are eigenvectors for a scalar `μ`, the scalar `μ` is called an eigenvalue.

There is no consensus in the literature whether `0` is an eigenvector. Our definition of
`has_eigenvector` permits only nonzero vectors. For an eigenvector `x` that may also be `0`, we
write `x ∈ f.eigenspace μ`.

A generalized eigenspace of a linear map `f` for a natural number `k` and a scalar `μ` is the kernel
of the map `(f - μ • id) ^ k`. The nonzero elements of a generalized eigenspace are generalized
eigenvectors `x`. If there are generalized eigenvectors for a natural number `k` and a scalar `μ`,
the scalar `μ` is called a generalized eigenvalue.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2015]
* https://en.wikipedia.org/wiki/Eigenvalues_and_eigenvectors

## Tags

eigenspace, eigenvector, eigenvalue, eigen
-/

universes u v w

namespace module
namespace End

open module principal_ideal_ring polynomial finite_dimensional

variables {K R : Type v} {V M : Type w}
  [comm_ring R] [add_comm_group M] [module R M] [field K] [add_comm_group V] [module K V]

/-- The submodule `eigenspace f μ` for a linear map `f` and a scalar `μ` consists of all vectors `x`
    such that `f x = μ • x`. (Def 5.36 of [axler2015])-/
def eigenspace (f : End R M) (μ : R) : submodule R M :=
(f - algebra_map R (End R M) μ).ker

/-- A nonzero element of an eigenspace is an eigenvector. (Def 5.7 of [axler2015]) -/
def has_eigenvector (f : End R M) (μ : R) (x : M) : Prop :=
x ∈ eigenspace f μ ∧ x ≠ 0

/-- A scalar `μ` is an eigenvalue for a linear map `f` if there are nonzero vectors `x`
    such that `f x = μ • x`. (Def 5.5 of [axler2015]) -/
def has_eigenvalue (f : End R M) (a : R) : Prop :=
eigenspace f a ≠ ⊥

/-- The eigenvalues of the endomorphism `f`, as a subtype of `R`. -/
def eigenvalues (f : End R M) : Type* := {μ : R // f.has_eigenvalue μ}

instance (f : End R M) : has_coe f.eigenvalues R := coe_subtype

lemma has_eigenvalue_of_has_eigenvector {f : End R M} {μ : R} {x : M} (h : has_eigenvector f μ x) :
  has_eigenvalue f μ :=
begin
  rw [has_eigenvalue, submodule.ne_bot_iff],
  use x, exact h,
end

lemma mem_eigenspace_iff {f : End R M} {μ : R} {x : M} : x ∈ eigenspace f μ ↔ f x = μ • x :=
by rw [eigenspace, linear_map.mem_ker, linear_map.sub_apply, algebra_map_End_apply,
  sub_eq_zero]

lemma has_eigenvalue.exists_has_eigenvector {f : End R M} {μ : R} (hμ : f.has_eigenvalue μ) :
  ∃ v, f.has_eigenvector μ v :=
submodule.exists_mem_ne_zero_of_ne_bot hμ

lemma eigenspace_div (f : End K V) (a b : K) (hb : b ≠ 0) :
  eigenspace f (a / b) = (b • f - algebra_map K (End K V) a).ker :=
calc
  eigenspace f (a / b) = eigenspace f (b⁻¹ * a) : by { rw [div_eq_mul_inv, mul_comm] }
  ... = (f - (b⁻¹ * a) • linear_map.id).ker : rfl
  ... = (f - b⁻¹ • a • linear_map.id).ker : by rw smul_smul
  ... = (f - b⁻¹ • algebra_map K (End K V) a).ker : rfl
  ... = (b • (f - b⁻¹ • algebra_map K (End K V) a)).ker : by rw linear_map.ker_smul _ b hb
  ... = (b • f - algebra_map K (End K V) a).ker : by rw [smul_sub, smul_inv_smul₀ hb]

lemma eigenspace_aeval_polynomial_degree_1
  (f : End K V) (q : polynomial K) (hq : degree q = 1) :
  eigenspace f (- q.coeff 0 / q.leading_coeff) = (aeval f q).ker :=
calc
  eigenspace f (- q.coeff 0 / q.leading_coeff)
      = (q.leading_coeff • f - algebra_map K (End K V) (- q.coeff 0)).ker
    : by { rw eigenspace_div, intro h, rw leading_coeff_eq_zero_iff_deg_eq_bot.1 h at hq, cases hq }
  ... = (aeval f (C q.leading_coeff * X + C (q.coeff 0))).ker
    : by { rw [C_mul', aeval_def], simp [algebra_map, algebra.to_ring_hom], }
  ... = (aeval f q).ker
     : by { congr, apply (eq_X_add_C_of_degree_eq_one hq).symm }

lemma ker_aeval_ring_hom'_unit_polynomial
  (f : End K V) (c : units (polynomial K)) :
  (aeval f (c : polynomial K)).ker = ⊥ :=
begin
  rw polynomial.eq_C_of_degree_eq_zero (degree_coe_units c),
  simp only [aeval_def, eval₂_C],
  apply ker_algebra_map_End,
  apply coeff_coe_units_zero_ne_zero c
end

theorem aeval_apply_of_has_eigenvector {f : End K V}
  {p : polynomial K} {μ : K} {x : V} (h : f.has_eigenvector μ x) :
  aeval f p x = (p.eval μ) • x :=
begin
  apply p.induction_on,
  { intro a, simp [module.algebra_map_End_apply] },
  { intros p q hp hq, simp [hp, hq, add_smul] },
  { intros n a hna,
    rw [mul_comm, pow_succ, mul_assoc, alg_hom.map_mul, linear_map.mul_apply, mul_comm, hna],
    simp [algebra_map_End_apply, mem_eigenspace_iff.1 h.1, smul_smul, mul_comm] }
end

section minpoly

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
  cases (linear_map.is_unit_iff _).2 con with u hu,
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
set.finite.fintype
begin
  have h : minpoly K f ≠ 0 := minpoly.ne_zero f.is_integral,
  convert (minpoly K f).root_set_finite K,
  ext μ,
  have : (μ ∈ {μ : K | f.eigenspace μ = ⊥ → false}) ↔ ¬f.eigenspace μ = ⊥ := by tauto,
  convert rfl.mpr this,
  simp [polynomial.root_set_def, polynomial.mem_roots h, ← has_eigenvalue_iff_is_root,
    has_eigenvalue]
end

end minpoly

/-- Every linear operator on a vector space over an algebraically closed field has
    an eigenvalue. -/
-- This is Lemma 5.21 of [axler2015], although we are no longer following that proof.
lemma exists_eigenvalue [is_alg_closed K] [finite_dimensional K V] [nontrivial V] (f : End K V) :
  ∃ (c : K), f.has_eigenvalue c :=
begin
  obtain ⟨c, nu⟩ := exists_spectrum_of_is_alg_closed_of_finite_dimensional K f,
  use c,
  rw linear_map.is_unit_iff at nu,
  exact has_eigenvalue_of_has_eigenvector (submodule.exists_mem_ne_zero_of_ne_bot nu).some_spec,
end

noncomputable instance [is_alg_closed K] [finite_dimensional K V] [nontrivial V] (f : End K V) :
  inhabited f.eigenvalues :=
⟨⟨f.exists_eigenvalue.some, f.exists_eigenvalue.some_spec⟩⟩

/-- Eigenvectors corresponding to distinct eigenvalues of a linear operator are linearly
    independent. (Lemma 5.10 of [axler2015])

    We use the eigenvalues as indexing set to ensure that there is only one eigenvector for each
    eigenvalue in the image of `xs`. -/
lemma eigenvectors_linear_independent (f : End K V) (μs : set K) (xs : μs → V)
  (h_eigenvec : ∀ μ : μs, f.has_eigenvector μ (xs μ)) :
  linear_independent K xs :=
begin
  classical,
  -- We need to show that if a linear combination `l` of the eigenvectors `xs` is `0`, then all
  -- its coefficients are zero.
  suffices : ∀ l, finsupp.total μs V K xs l = 0 → l = 0,
  { rw linear_independent_iff,
    apply this },
  intros l hl,
  -- We apply induction on the finite set of eigenvalues whose eigenvectors have nonzero
  -- coefficients, i.e. on the support of `l`.
  induction h_l_support : l.support using finset.induction with μ₀ l_support' hμ₀ ih generalizing l,
  -- If the support is empty, all coefficients are zero and we are done.
  { exact finsupp.support_eq_empty.1 h_l_support },
  -- Now assume that the support of `l` contains at least one eigenvalue `μ₀`. We define a new
  -- linear combination `l'` to apply the induction hypothesis on later. The linear combination `l'`
  -- is derived from `l` by multiplying the coefficient of the eigenvector with eigenvalue `μ`
  -- by `μ - μ₀`.
  -- To get started, we define `l'` as a function `l'_f : μs → K` with potentially infinite support.
  { let l'_f : μs → K := (λ μ : μs, (↑μ - ↑μ₀) * l μ),
    -- The support of `l'_f` is the support of `l` without `μ₀`.
    have h_l_support' : ∀ (μ : μs), μ ∈ l_support' ↔ l'_f μ ≠ 0 ,
    { intro μ,
      suffices : μ ∈ l_support' → μ ≠ μ₀,
      { simp [l'_f, ← finsupp.not_mem_support_iff, h_l_support, sub_eq_zero, ←subtype.ext_iff],
        tauto },
      rintro hμ rfl,
      contradiction },
    -- Now we can define `l'_f` as an actual linear combination `l'` because we know that the
    -- support is finite.
    let l' : μs →₀ K :=
      { to_fun := l'_f, support := l_support', mem_support_to_fun := h_l_support' },
    -- The linear combination `l'` over `xs` adds up to `0`.
    have total_l' : finsupp.total μs V K xs l' = 0,
    { let g := f - algebra_map K (End K V) μ₀,
      have h_gμ₀: g (l μ₀ • xs μ₀) = 0,
        by rw [linear_map.map_smul, linear_map.sub_apply, mem_eigenspace_iff.1 (h_eigenvec _).1,
          algebra_map_End_apply, sub_self, smul_zero],
      have h_useless_filter : finset.filter (λ (a : μs), l'_f a ≠ 0) l_support' = l_support',
      { rw finset.filter_congr _,
        { apply finset.filter_true },
        { apply_instance },
        exact λ μ hμ, (iff_true _).mpr ((h_l_support' μ).1 hμ) },
      have bodies_eq : ∀ (μ : μs), l'_f μ • xs μ = g (l μ • xs μ),
      { intro μ,
        dsimp only [g, l'_f],
        rw [linear_map.map_smul, linear_map.sub_apply, mem_eigenspace_iff.1 (h_eigenvec _).1,
          algebra_map_End_apply, ←sub_smul, smul_smul, mul_comm] },
      rw [←linear_map.map_zero g, ←hl, finsupp.total_apply, finsupp.total_apply,
          finsupp.sum, finsupp.sum, linear_map.map_sum, h_l_support,
          finset.sum_insert hμ₀, h_gμ₀, zero_add],
      refine finset.sum_congr rfl (λ μ _, _),
      apply bodies_eq },
    -- Therefore, by the induction hypothesis, all coefficients in `l'` are zero.
    have l'_eq_0 : l' = 0 := ih l' total_l' rfl,
    -- By the defintion of `l'`, this means that `(μ - μ₀) * l μ = 0` for all `μ`.
    have h_mul_eq_0 : ∀ μ : μs, (↑μ - ↑μ₀) * l μ = 0,
    { intro μ,
      calc (↑μ - ↑μ₀) * l μ = l' μ : rfl
      ... = 0 : by { rw [l'_eq_0], refl } },
    -- Thus, the coefficients in `l` for all `μ ≠ μ₀` are `0`.
    have h_lμ_eq_0 : ∀ μ : μs, μ ≠ μ₀ → l μ = 0,
    { intros μ hμ,
      apply or_iff_not_imp_left.1 (mul_eq_zero.1 (h_mul_eq_0 μ)),
      rwa [sub_eq_zero, ←subtype.ext_iff] },
    -- So if we sum over all these coefficients, we obtain `0`.
    have h_sum_l_support'_eq_0 : finset.sum l_support' (λ (μ : ↥μs), l μ • xs μ) = 0,
    { rw ←finset.sum_const_zero,
      apply finset.sum_congr rfl,
      intros μ hμ,
      rw h_lμ_eq_0,
      apply zero_smul,
      intro h,
      rw h at hμ,
      contradiction },
    -- The only potentially nonzero coefficient in `l` is the one corresponding to `μ₀`. But since
    -- the overall sum is `0` by assumption, this coefficient must also be `0`.
    have : l μ₀ = 0,
    { rw [finsupp.total_apply, finsupp.sum, h_l_support,
          finset.sum_insert hμ₀, h_sum_l_support'_eq_0, add_zero] at hl,
      by_contra h,
      exact (h_eigenvec μ₀).2 ((smul_eq_zero.1 hl).resolve_left h) },
    -- Thus, all coefficients in `l` are `0`.
    show l = 0,
    { ext μ,
      by_cases h_cases : μ = μ₀,
      { rw h_cases,
        assumption },
      exact h_lμ_eq_0 μ h_cases } }
end

/-- The generalized eigenspace for a linear map `f`, a scalar `μ`, and an exponent `k ∈ ℕ` is the
kernel of `(f - μ • id) ^ k`. (Def 8.10 of [axler2015]). Furthermore, a generalized eigenspace for
some exponent `k` is contained in the generalized eigenspace for exponents larger than `k`. -/
def generalized_eigenspace (f : End R M) (μ : R) : ℕ →ₘ submodule R M :=
{ to_fun    := λ k, ((f - algebra_map R (End R M) μ) ^ k).ker,
  monotone' := λ k m hm,
  begin
    simp only [← pow_sub_mul_pow _ hm],
    exact linear_map.ker_le_ker_comp
      ((f - algebra_map R (End R M) μ) ^ k) ((f - algebra_map R (End R M) μ) ^ (m - k)),
  end }

@[simp] lemma mem_generalized_eigenspace (f : End R M) (μ : R) (k : ℕ) (m : M) :
  m ∈ f.generalized_eigenspace μ k ↔ ((f - μ • 1)^k) m = 0 :=
iff.rfl

/-- A nonzero element of a generalized eigenspace is a generalized eigenvector.
    (Def 8.9 of [axler2015])-/
def has_generalized_eigenvector (f : End R M) (μ : R) (k : ℕ) (x : M) : Prop :=
x ≠ 0 ∧ x ∈ generalized_eigenspace f μ k

/-- A scalar `μ` is a generalized eigenvalue for a linear map `f` and an exponent `k ∈ ℕ` if there
    are generalized eigenvectors for `f`, `k`, and `μ`. -/
def has_generalized_eigenvalue (f : End R M) (μ : R) (k : ℕ) : Prop :=
generalized_eigenspace f μ k ≠ ⊥

/-- The generalized eigenrange for a linear map `f`, a scalar `μ`, and an exponent `k ∈ ℕ` is the
    range of `(f - μ • id) ^ k`. -/
def generalized_eigenrange (f : End R M) (μ : R) (k : ℕ) : submodule R M :=
((f - algebra_map R (End R M) μ) ^ k).range

/-- The exponent of a generalized eigenvalue is never 0. -/
lemma exp_ne_zero_of_has_generalized_eigenvalue {f : End R M} {μ : R} {k : ℕ}
  (h : f.has_generalized_eigenvalue μ k) : k ≠ 0 :=
begin
  rintro rfl,
  exact h linear_map.ker_id
end

/-- The union of the kernels of `(f - μ • id) ^ k` over all `k`. -/
def maximal_generalized_eigenspace (f : End R M) (μ : R) : submodule R M :=
⨆ k, f.generalized_eigenspace μ k

lemma generalized_eigenspace_le_maximal (f : End R M) (μ : R) (k : ℕ) :
  f.generalized_eigenspace μ k ≤ f.maximal_generalized_eigenspace μ :=
le_supr _ _

@[simp] lemma mem_maximal_generalized_eigenspace (f : End R M) (μ : R) (m : M) :
  m ∈ f.maximal_generalized_eigenspace μ ↔ ∃ (k : ℕ), ((f - μ • 1)^k) m = 0 :=
by simp only [maximal_generalized_eigenspace, ← mem_generalized_eigenspace,
  submodule.mem_supr_of_chain]

/-- If there exists a natural number `k` such that the kernel of `(f - μ • id) ^ k` is the
maximal generalized eigenspace, then this value is the least such `k`. If not, this value is not
meaningful. -/
noncomputable def maximal_generalized_eigenspace_index (f : End R M) (μ : R) :=
monotonic_sequence_limit_index (f.generalized_eigenspace μ)

/-- For an endomorphism of a Noetherian module, the maximal eigenspace is always of the form kernel
`(f - μ • id) ^ k` for some `k`. -/
lemma maximal_generalized_eigenspace_eq [h : is_noetherian R M] (f : End R M) (μ : R) :
  maximal_generalized_eigenspace f μ =
  f.generalized_eigenspace μ (maximal_generalized_eigenspace_index f μ) :=
begin
  rw is_noetherian_iff_well_founded at h,
  exact (well_founded.supr_eq_monotonic_sequence_limit h (f.generalized_eigenspace μ) : _),
end

/-- A generalized eigenvalue for some exponent `k` is also
    a generalized eigenvalue for exponents larger than `k`. -/
lemma has_generalized_eigenvalue_of_has_generalized_eigenvalue_of_le
  {f : End R M} {μ : R} {k : ℕ} {m : ℕ} (hm : k ≤ m) (hk : f.has_generalized_eigenvalue μ k) :
  f.has_generalized_eigenvalue μ m :=
begin
  unfold has_generalized_eigenvalue at *,
  contrapose! hk,
  rw [←le_bot_iff, ←hk],
  exact (f.generalized_eigenspace μ).monotone hm,
end

/-- The eigenspace is a subspace of the generalized eigenspace. -/
lemma eigenspace_le_generalized_eigenspace {f : End R M} {μ : R} {k : ℕ} (hk : 0 < k) :
  f.eigenspace μ ≤ f.generalized_eigenspace μ k :=
(f.generalized_eigenspace μ).monotone (nat.succ_le_of_lt hk)

/-- All eigenvalues are generalized eigenvalues. -/
lemma has_generalized_eigenvalue_of_has_eigenvalue
  {f : End R M} {μ : R} {k : ℕ} (hk : 0 < k) (hμ : f.has_eigenvalue μ) :
  f.has_generalized_eigenvalue μ k :=
begin
  apply has_generalized_eigenvalue_of_has_generalized_eigenvalue_of_le hk,
  rw [has_generalized_eigenvalue, generalized_eigenspace, preorder_hom.coe_fun_mk, pow_one],
  exact hμ,
end

/-- All generalized eigenvalues are eigenvalues. -/
lemma has_eigenvalue_of_has_generalized_eigenvalue
  {f : End R M} {μ : R} {k : ℕ} (hμ : f.has_generalized_eigenvalue μ k) :
  f.has_eigenvalue μ :=
begin
  intros contra, apply hμ,
  erw linear_map.ker_eq_bot at ⊢ contra, rw linear_map.coe_pow,
  exact function.injective.iterate contra k,
end

/-- Generalized eigenvalues are actually just eigenvalues. -/
@[simp] lemma has_generalized_eigenvalue_iff_has_eigenvalue
  {f : End R M} {μ : R} {k : ℕ} (hk : 0 < k) :
  f.has_generalized_eigenvalue μ k ↔ f.has_eigenvalue μ :=
⟨has_eigenvalue_of_has_generalized_eigenvalue, has_generalized_eigenvalue_of_has_eigenvalue hk⟩

/-- Every generalized eigenvector is a generalized eigenvector for exponent `finrank K V`.
    (Lemma 8.11 of [axler2015]) -/
lemma generalized_eigenspace_le_generalized_eigenspace_finrank
  [finite_dimensional K V] (f : End K V) (μ : K) (k : ℕ) :
  f.generalized_eigenspace μ k ≤ f.generalized_eigenspace μ (finrank K V) :=
ker_pow_le_ker_pow_finrank _ _

/-- Generalized eigenspaces for exponents at least `finrank K V` are equal to each other. -/
lemma generalized_eigenspace_eq_generalized_eigenspace_finrank_of_le [finite_dimensional K V]
  (f : End K V) (μ : K) {k : ℕ} (hk : finrank K V ≤ k) :
  f.generalized_eigenspace μ k = f.generalized_eigenspace μ (finrank K V) :=
ker_pow_eq_ker_pow_finrank_of_le hk

/-- If `f` maps a subspace `p` into itself, then the generalized eigenspace of the restriction
    of `f` to `p` is the part of the generalized eigenspace of `f` that lies in `p`. -/
lemma generalized_eigenspace_restrict
  (f : End R M) (p : submodule R M) (k : ℕ) (μ : R) (hfp : ∀ (x : M), x ∈ p → f x ∈ p) :
  generalized_eigenspace (linear_map.restrict f hfp) μ k =
    submodule.comap p.subtype (f.generalized_eigenspace μ k) :=
begin
  simp only [generalized_eigenspace, preorder_hom.coe_fun_mk, ← linear_map.ker_comp],
  induction k with k ih,
  { rw [pow_zero, pow_zero, linear_map.one_eq_id],
    apply (submodule.ker_subtype _).symm },
  { erw [pow_succ', pow_succ', linear_map.ker_comp, linear_map.ker_comp, ih,
      ← linear_map.ker_comp, ← linear_map.ker_comp, linear_map.comp_assoc] },
end

/-- If `p` is an invariant submodule of an endomorphism `f`, then the `μ`-eigenspace of the
restriction of `f` to `p` is a submodule of the `μ`-eigenspace of `f`. -/
lemma eigenspace_restrict_le_eigenspace (f : End R M) {p : submodule R M}
  (hfp : ∀ x ∈ p, f x ∈ p) (μ : R) :
  (eigenspace (f.restrict hfp) μ).map p.subtype ≤ f.eigenspace μ :=
begin
  rintros a ⟨x, hx, rfl⟩,
  simp only [set_like.mem_coe, mem_eigenspace_iff, linear_map.restrict_apply] at hx ⊢,
  exact congr_arg coe hx
end

/-- Generalized eigenrange and generalized eigenspace for exponent `finrank K V` are disjoint. -/
lemma generalized_eigenvec_disjoint_range_ker [finite_dimensional K V] (f : End K V) (μ : K) :
  disjoint (f.generalized_eigenrange μ (finrank K V)) (f.generalized_eigenspace μ (finrank K V))  :=
begin
  have h := calc
    submodule.comap ((f - algebra_map _ _ μ) ^ finrank K V)
        (f.generalized_eigenspace μ (finrank K V))
      = ((f - algebra_map _ _ μ) ^ finrank K V *
          (f - algebra_map K (End K V) μ) ^ finrank K V).ker :
        by { simpa only [generalized_eigenspace, preorder_hom.coe_fun_mk, ← linear_map.ker_comp] }
  ... = f.generalized_eigenspace μ (finrank K V + finrank K V) :
        by { rw ←pow_add, refl }
  ... = f.generalized_eigenspace μ (finrank K V) :
        by { rw generalized_eigenspace_eq_generalized_eigenspace_finrank_of_le, linarith },
  rw [disjoint, generalized_eigenrange, linear_map.range_eq_map, submodule.map_inf_eq_map_inf_comap,
    top_inf_eq, h],
  apply submodule.map_comap_le
end

/-- If an invariant subspace `p` of an endomorphism `f` is disjoint from the `μ`-eigenspace of `f`,
then the restriction of `f` to `p` has trivial `μ`-eigenspace. -/
lemma eigenspace_restrict_eq_bot {f : End R M} {p : submodule R M}
  (hfp : ∀ x ∈ p, f x ∈ p) {μ : R} (hμp : disjoint (f.eigenspace μ) p) :
  eigenspace (f.restrict hfp) μ = ⊥ :=
begin
  rw eq_bot_iff,
  intros x hx,
  simpa using hμp ⟨eigenspace_restrict_le_eigenspace f hfp μ ⟨x, hx, rfl⟩, x.prop⟩,
end

/-- The generalized eigenspace of an eigenvalue has positive dimension for positive exponents. -/
lemma pos_finrank_generalized_eigenspace_of_has_eigenvalue [finite_dimensional K V]
  {f : End K V} {k : ℕ} {μ : K} (hx : f.has_eigenvalue μ) (hk : 0 < k):
  0 < finrank K (f.generalized_eigenspace μ k) :=
calc
    0 = finrank K (⊥ : submodule K V) : by rw finrank_bot
  ... < finrank K (f.eigenspace μ) : submodule.finrank_lt_finrank_of_lt (bot_lt_iff_ne_bot.2 hx)
  ... ≤ finrank K (f.generalized_eigenspace μ k) :
    submodule.finrank_mono ((f.generalized_eigenspace μ).monotone (nat.succ_le_of_lt hk))

/-- A linear map maps a generalized eigenrange into itself. -/
lemma map_generalized_eigenrange_le {f : End K V} {μ : K} {n : ℕ} :
  submodule.map f (f.generalized_eigenrange μ n) ≤ f.generalized_eigenrange μ n :=
calc submodule.map f (f.generalized_eigenrange μ n)
       = (f * ((f - algebra_map _ _ μ) ^ n)).range : (linear_map.range_comp _ _).symm
   ... = (((f - algebra_map _ _ μ) ^ n) * f).range : by rw algebra.mul_sub_algebra_map_pow_commutes
   ... = submodule.map ((f - algebra_map _ _ μ) ^ n) f.range : linear_map.range_comp _ _
   ... ≤ f.generalized_eigenrange μ n : linear_map.map_le_range

/-- The generalized eigenvectors span the entire vector space (Lemma 8.21 of [axler2015]). -/
lemma supr_generalized_eigenspace_eq_top [is_alg_closed K] [finite_dimensional K V] (f : End K V) :
  (⨆ (μ : K) (k : ℕ), f.generalized_eigenspace μ k) = ⊤ :=
begin
  tactic.unfreeze_local_instances,
  -- We prove the claim by strong induction on the dimension of the vector space.
  induction h_dim : finrank K V using nat.strong_induction_on with n ih generalizing V,
  cases n,
  -- If the vector space is 0-dimensional, the result is trivial.
  { rw ←top_le_iff,
    simp only [finrank_eq_zero.1 (eq.trans finrank_top h_dim), bot_le] },
  -- Otherwise the vector space is nontrivial.
  { haveI : nontrivial V := finrank_pos_iff.1 (by { rw h_dim, apply nat.zero_lt_succ }),
    -- Hence, `f` has an eigenvalue `μ₀`.
    obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀, f.has_eigenvalue μ₀ := exists_eigenvalue f,
    -- We define `ES` to be the generalized eigenspace
    let ES := f.generalized_eigenspace μ₀ (finrank K V),
    -- and `ER` to be the generalized eigenrange.
    let ER := f.generalized_eigenrange μ₀ (finrank K V),
    -- `f` maps `ER` into itself.
    have h_f_ER : ∀ (x : V), x ∈ ER → f x ∈ ER,
      from λ x hx, map_generalized_eigenrange_le (submodule.mem_map_of_mem hx),
    -- Therefore, we can define the restriction `f'` of `f` to `ER`.
    let f' : End K ER := f.restrict h_f_ER,
    -- The dimension of `ES` is positive
    have h_dim_ES_pos : 0 < finrank K ES,
    { dsimp only [ES],
      rw h_dim,
      apply pos_finrank_generalized_eigenspace_of_has_eigenvalue hμ₀ (nat.zero_lt_succ n) },
    -- and the dimensions of `ES` and `ER` add up to `finrank K V`.
    have h_dim_add : finrank K ER + finrank K ES = finrank K V,
    { apply linear_map.finrank_range_add_finrank_ker },
    -- Therefore the dimension `ER` mus be smaller than `finrank K V`.
    have h_dim_ER : finrank K ER < n.succ, by linarith,
    -- This allows us to apply the induction hypothesis on `ER`:
    have ih_ER : (⨆ (μ : K) (k : ℕ), f'.generalized_eigenspace μ k) = ⊤,
      from ih (finrank K ER) h_dim_ER f' rfl,
    -- The induction hypothesis gives us a statement about subspaces of `ER`. We can transfer this
    -- to a statement about subspaces of `V` via `submodule.subtype`:
    have ih_ER' : (⨆ (μ : K) (k : ℕ), (f'.generalized_eigenspace μ k).map ER.subtype) = ER,
      by simp only [(submodule.map_supr _ _).symm, ih_ER, submodule.map_subtype_top ER],
    -- Moreover, every generalized eigenspace of `f'` is contained in the corresponding generalized
    -- eigenspace of `f`.
    have hff' : ∀ μ k,
        (f'.generalized_eigenspace μ k).map ER.subtype ≤ f.generalized_eigenspace μ k,
    { intros,
      rw generalized_eigenspace_restrict,
      apply submodule.map_comap_le },
    -- It follows that `ER` is contained in the span of all generalized eigenvectors.
    have hER : ER ≤ ⨆ (μ : K) (k : ℕ), f.generalized_eigenspace μ k,
    { rw ← ih_ER',
      apply supr_le_supr _,
      exact λ μ, supr_le_supr (λ k, hff' μ k), },
    -- `ES` is contained in this span by definition.
    have hES : ES ≤ ⨆ (μ : K) (k : ℕ), f.generalized_eigenspace μ k,
      from le_trans
        (le_supr (λ k, f.generalized_eigenspace μ₀ k) (finrank K V))
        (le_supr (λ (μ : K), ⨆ (k : ℕ), f.generalized_eigenspace μ k) μ₀),
    -- Moreover, we know that `ER` and `ES` are disjoint.
    have h_disjoint : disjoint ER ES,
      from generalized_eigenvec_disjoint_range_ker f μ₀,
    -- Since the dimensions of `ER` and `ES` add up to the dimension of `V`, it follows that the
    -- span of all generalized eigenvectors is all of `V`.
    show (⨆ (μ : K) (k : ℕ), f.generalized_eigenspace μ k) = ⊤,
    { rw [←top_le_iff, ←submodule.eq_top_of_disjoint ER ES h_dim_add h_disjoint],
      apply sup_le hER hES } }
end

end End
end module
