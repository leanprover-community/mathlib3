/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Eric Wieser, Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import algebra.direct_sum.internal
import ring_theory.mv_polynomial.weighted_homogeneous

/-!
# Homogeneous polynomials

A multivariate polynomial `φ` is homogeneous of degree `n : ℕ` if all monomials occuring in `φ`
have degree `n`. Equivalently, `φ` is weighted homogeneous with respect to the constant weight
function `1 : σ → ℕ`.

## Main definitions/lemmas

* `is_homogeneous φ n`: a predicate that asserts that `φ` is homogeneous of degree `n`.
* `homogeneous_submodule σ R n`: the submodule of homogeneous polynomials of degree `n`.
* `homogeneous_component n`: the additive morphism that projects polynomials onto
  their summand that is homogeneous of degree `n`.
* `sum_homogeneous_component`: every polynomial is the sum of its homogeneous components
-/

noncomputable theory

open_locale big_operators

open mv_polynomial.is_weighted_homogeneous

namespace mv_polynomial
variables {σ : Type*} {τ : Type*} {R : Type*} {S : Type*}

lemma weighted_degree'_one (m : σ →₀ ℕ) : (weighted_degree' (1 : σ → ℕ)) m = finsum m :=
by simp only [weighted_degree', pi.one_apply, algebra.id.smul_eq_mul, mul_one,
    add_monoid_hom.coe_mk]

/-- A multivariate polynomial `φ` is homogeneous of degree `n` if all monomials occuring in `φ`
  have degree `n`. -/
def is_homogeneous [comm_semiring R] (φ : mv_polynomial σ R) (n : ℕ) :=
is_weighted_homogeneous (1 : σ → ℕ) φ n

lemma degree'_eq_weighted_degree' (d : σ →₀ ℕ) :
  ∑ i in d.support, d i = weighted_degree' (1 : σ → ℕ) d :=
begin
  rw [weighted_degree'_one, finsum_eq_sum_of_support_subset],
  rw finsupp.fun_support_eq d,
end

variables (σ R)

/-- The submodule of homogeneous `mv_polynomial`s of degree `n`. -/
def homogeneous_submodule [comm_semiring R] (n : ℕ) :
  submodule R (mv_polynomial σ R) :=
weighted_homogeneous_submodule R (1 : σ → ℕ) n

variables {σ R}

@[simp] lemma mem_homogeneous_submodule [comm_semiring R] (n : ℕ) (p : mv_polynomial σ R) :
  p ∈ homogeneous_submodule σ R n ↔ p.is_homogeneous n := iff.rfl

variables (σ R)

/-- While equal, the former has a convenient definitional reduction. -/
lemma homogeneous_submodule_eq_finsupp_supported [comm_semiring R] (n : ℕ) :
  homogeneous_submodule σ R n = finsupp.supported _ R {d | ∑ i in d.support, d i = n} :=
begin
  simp_rw degree'_eq_weighted_degree',
  exact weighted_homogeneous_submodule_eq_finsupp_supported R 1 n,
end

variables {σ R}

lemma homogeneous_submodule_mul [comm_semiring R] (m n : ℕ) :
  homogeneous_submodule σ R m * homogeneous_submodule σ R n ≤ homogeneous_submodule σ R (m + n) :=
weighted_homogeneous_submodule_mul (1 : σ → ℕ) m n

section
variables [comm_semiring R]

variables {σ R}

lemma is_homogeneous_monomial (d : σ →₀ ℕ) (r : R) (n : ℕ) (hn : ∑ i in d.support, d i = n) :
  is_homogeneous (monomial d r) n :=
begin
  simp_rw degree'_eq_weighted_degree' at hn,
  exact is_weighted_homogeneous_monomial 1 d r hn
end

variables (σ) {R}

lemma is_homogeneous_of_total_degree_zero {p : mv_polynomial σ R} (hp : p.total_degree = 0) :
  is_homogeneous p 0 :=
begin
  intros m hm,
  simp only [weighted_degree'_one],
  apply finsum_eq_zero_of_forall_eq_zero,
  intro x,
  by_cases hx : x ∈ m.support,
  { change _ = ⊥ at hp,
    simp_rw [total_degree, finset.sup_eq_bot_iff, mem_support_iff] at hp,
    specialize hp m hm,
    change _ = 0 at hp,
    simp only [finsupp.sum, finset.sum_eq_zero_iff] at hp,
    exact hp x hx, },
  { simp only [finsupp.mem_support_iff, not_not] at hx,
    exact hx, },
end

lemma is_homogeneous_C (r : R) :
  is_homogeneous (C r : mv_polynomial σ R) 0 :=
is_weighted_homogeneous_C (1 : σ → ℕ) r

variables (σ R)

lemma is_homogeneous_zero (n : ℕ) : is_homogeneous (0 : mv_polynomial σ R) n :=
is_weighted_homogeneous_zero R (1 : σ → ℕ) n

lemma is_homogeneous_one : is_homogeneous (1 : mv_polynomial σ R) 0 :=
is_weighted_homogeneous_one R (1 : σ → ℕ)

variables {σ} (R)

lemma is_homogeneous_X (i : σ) :
  is_homogeneous (X i : mv_polynomial σ R) 1 :=
is_weighted_homogeneous_X R (1 : σ → ℕ) i

end

namespace is_homogeneous
variables [comm_semiring R] {φ ψ : mv_polynomial σ R} {m n : ℕ}

lemma coeff_eq_zero (hφ : is_homogeneous φ n) (d : σ →₀ ℕ) (hd : ∑ i in d.support, d i ≠ n) :
  coeff d φ = 0 :=
by simp_rw degree'_eq_weighted_degree' at hd; exact is_weighted_homogeneous.coeff_eq_zero hφ d hd

lemma inj_right (hm : is_homogeneous φ m) (hn : is_homogeneous φ n) (hφ : φ ≠ 0) :
  m = n :=
is_weighted_homogeneous.inj_right hm hn hφ

lemma add (hφ : is_homogeneous φ n) (hψ : is_homogeneous ψ n) :
  is_homogeneous (φ + ψ) n :=
is_weighted_homogeneous.add hφ hψ

lemma sum {ι : Type*} (s : finset ι) (φ : ι → mv_polynomial σ R) (n : ℕ)
  (h : ∀ i ∈ s, is_homogeneous (φ i) n) :
  is_homogeneous (∑ i in s, φ i) n :=
is_weighted_homogeneous.sum s φ n h

lemma mul (hφ : is_homogeneous φ m) (hψ : is_homogeneous ψ n) :
  is_homogeneous (φ * ψ) (m + n) :=
is_weighted_homogeneous.mul hφ hψ

lemma prod {ι : Type*} (s : finset ι) (φ : ι → mv_polynomial σ R) (n : ι → ℕ)
  (h : ∀ i ∈ s, is_homogeneous (φ i) (n i)) :
  is_homogeneous (∏ i in s, φ i) (∑ i in s, n i) :=
is_weighted_homogeneous.prod s φ n h

lemma total_degree_eq_weighted_total_degree :
  total_degree φ = weighted_total_degree (1 : σ → ℕ) φ :=
begin
  simp only [total_degree, weighted_total_degree, weighted_degree'_one],
  apply finset.sup_congr rfl,
  intros a ha,
  simp only [finsupp.sum_eq_finsum, eq_self_iff_true, implies_true_iff],
end

lemma total_degree (hφ : is_homogeneous φ n) (h : φ ≠ 0) :
  total_degree φ = n :=
by rw [total_degree_eq_weighted_total_degree, ← with_bot.coe_eq_coe,
    ← weighted_total_degree_coe _ φ h,
    is_weighted_homogeneous.weighted_total_degree hφ h]

/--
The homogeneous submodules form a graded ring. This instance is used by `direct_sum.comm_semiring`
and `direct_sum.algebra`. -/
instance homogeneous_submodule.gcomm_semiring :
  set_like.graded_monoid (homogeneous_submodule σ R) :=
is_weighted_homogeneous.weighted_homogeneous_submodule.gcomm_semiring


open_locale direct_sum
noncomputable example : comm_semiring (⨁ i, homogeneous_submodule σ R i) := infer_instance
noncomputable example : algebra R (⨁ i, homogeneous_submodule σ R i) := infer_instance

end is_homogeneous

section
noncomputable theory
open_locale classical
open finset

/-- `homogeneous_component n φ` is the part of `φ` that is homogeneous of degree `n`.
See `sum_homogeneous_component` for the statement that `φ` is equal to the sum
of all its homogeneous components. -/
def homogeneous_component [comm_semiring R] (n : ℕ) :
  mv_polynomial σ R →ₗ[R] mv_polynomial σ R :=
weighted_homogeneous_component (1 : σ → ℕ) n

section homogeneous_component
open finset
variables [comm_semiring R] (n : ℕ) (φ ψ : mv_polynomial σ R)

lemma coeff_homogeneous_component (d : σ →₀ ℕ) :
  coeff d (homogeneous_component n φ) = if ∑ i in d.support, d i = n then coeff d φ else 0 :=
begin
  simp_rw degree'_eq_weighted_degree',
  convert coeff_weighted_homogeneous_component n φ d,
end

lemma homogeneous_component_apply :
  homogeneous_component n φ =
  ∑ d in φ.support.filter (λ d, ∑ i in d.support, d i = n), monomial d (coeff d φ) :=
begin
  simp_rw degree'_eq_weighted_degree',
  convert weighted_homogeneous_component_apply n φ,
end

lemma homogeneous_component_is_homogeneous :
  (homogeneous_component n φ).is_homogeneous n :=
weighted_homogeneous_component_is_weighted_homogeneous n φ

@[simp] lemma homogeneous_component_zero : homogeneous_component 0 φ = C (coeff 0 φ) :=
weighted_homogeneous_component_zero φ (λ x : σ, one_ne_zero)

@[simp] lemma homogeneous_component_C_mul (n : ℕ) (r : R) :
  homogeneous_component n (C r * φ) = C r * homogeneous_component n φ :=
weighted_homogeneous_component_C_mul φ n r

lemma homogeneous_component_eq_zero' (h : ∀ d : σ →₀ ℕ, d ∈ φ.support → ∑ i in d.support, d i ≠ n) :
  homogeneous_component n φ = 0 :=
begin
  simp_rw degree'_eq_weighted_degree' at h,
  exact weighted_homogeneous_component_eq_zero' n φ h,
end

lemma homogeneous_component_eq_zero (h : φ.total_degree < n) :
  homogeneous_component n φ = 0 :=
begin
  apply weighted_homogeneous_component_eq_zero,
  rw ← is_homogeneous.total_degree_eq_weighted_total_degree,
  exact h,
end

-- Question for reviewers: should the proof use `sum_weighted_homogeneous_component`?
-- It seems that it would lead to a longer proof, because of conversions between various
-- types of sums.
lemma sum_homogeneous_component :
  ∑ i in range (φ.total_degree + 1), homogeneous_component i φ = φ :=
begin
  ext1 d,
  suffices : φ.total_degree < d.support.sum d → 0 = coeff d φ,
    by simpa [coeff_sum, coeff_homogeneous_component],
  exact λ h, (coeff_eq_zero_of_total_degree_lt h).symm
end

lemma homogeneous_component_homogeneous_polynomial (m n : ℕ)
  (p : mv_polynomial σ R) (h : p ∈ homogeneous_submodule σ R n) :
  homogeneous_component m p = if m = n then p else 0 :=
by convert weighted_homogeneous_component_weighted_homogeneous_polynomial m n p h

end homogeneous_component

end

end mv_polynomial
