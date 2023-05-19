/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import algebra.graded_monoid
import data.mv_polynomial.variables

/-!
# Weighted homogeneous polynomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

It is possible to assign weights (in a commutative additive monoid `M`) to the variables of a
multivariate polynomial ring, so that monomials of the ring then have a weighted degree with
respect to the weights of the variables. The weights are represented by a function `w : σ → M`,
where `σ` are the indeterminates.

A multivariate polynomial `φ` is weighted homogeneous of weighted degree `m : M` if all monomials
occuring in `φ` have the same weighted degree `m`.

## Main definitions/lemmas

* `weighted_total_degree' w φ` : the weighted total degree of a multivariate polynomial with respect
to the weights `w`, taking values in `with_bot M`.

* `weighted_total_degree w φ` : When `M` has a `⊥` element, we can define the weighted total degree
of a multivariate polynomial as a function taking values in `M`.

* `is_weighted_homogeneous w φ m`: a predicate that asserts that `φ` is weighted homogeneous
of weighted degree `m` with respect to the weights `w`.

* `weighted_homogeneous_submodule R w m`: the submodule of homogeneous polynomials
of weighted degree `m`.

* `weighted_homogeneous_component w m`: the additive morphism that projects polynomials
onto their summand that is weighted homogeneous of degree `n` with respect to `w`.

* `sum_weighted_homogeneous_component`: every polynomial is the sum of its weighted homogeneous
components.
-/

noncomputable theory

open_locale big_operators

open set function finset finsupp add_monoid_algebra

variables {R M : Type*} [comm_semiring R]

namespace mv_polynomial
variables {σ : Type*}

section add_comm_monoid
variables [add_comm_monoid M]

/-! ### `weighted_degree'` -/

/-- The `weighted degree'` of the finitely supported function `s : σ →₀ ℕ` is the sum
  `∑(s i)•(w i)`. -/
def weighted_degree' (w : σ → M) : (σ →₀ ℕ) →+ M :=
(finsupp.total σ M ℕ w).to_add_monoid_hom

section semilattice_sup
variable [semilattice_sup M]

/-- The weighted total degree of a multivariate polynomial, taking values in `with_bot M`. -/
def weighted_total_degree' (w : σ → M) (p : mv_polynomial σ R) : with_bot M :=
p.support.sup (λ s, weighted_degree' w s)

/-- The `weighted_total_degree'` of a polynomial `p` is `⊥` if and only if `p = 0`. -/
lemma weighted_total_degree'_eq_bot_iff (w : σ → M) (p : mv_polynomial σ R) :
  weighted_total_degree' w p = ⊥ ↔ p = 0 :=
begin
  simp only [weighted_total_degree',finset.sup_eq_bot_iff, mem_support_iff, with_bot.coe_ne_bot,
    mv_polynomial.eq_zero_iff ],
  exact forall_congr (λ _, not_not)
end

/-- The `weighted_total_degree'` of the zero polynomial is `⊥`. -/
lemma weighted_total_degree'_zero (w : σ → M) :
  weighted_total_degree' w (0 : mv_polynomial σ R) = ⊥ :=
by simp only [weighted_total_degree', support_zero, finset.sup_empty]

section order_bot
variable [order_bot M]

/-- When `M` has a `⊥` element, we can define the weighted total degree of a multivariate
  polynomial as a function taking values in `M`. -/
def weighted_total_degree (w : σ → M) (p : mv_polynomial σ R) : M :=
p.support.sup (λ s, weighted_degree' w s)

/-- This lemma relates `weighted_total_degree` and `weighted_total_degree'`. -/
lemma weighted_total_degree_coe (w : σ → M) (p : mv_polynomial σ R) (hp : p ≠ 0):
  weighted_total_degree' w p = ↑(weighted_total_degree w p) :=
begin
  rw [ne.def, ← weighted_total_degree'_eq_bot_iff w p, ← ne.def, with_bot.ne_bot_iff_exists] at hp,
  obtain ⟨m, hm⟩ := hp,
  apply le_antisymm,
  { simp only [weighted_total_degree, weighted_total_degree', finset.sup_le_iff,
      with_bot.coe_le_coe],
    intro b,
    exact finset.le_sup },
  { simp only [weighted_total_degree],
    have hm' : weighted_total_degree' w p ≤ m := le_of_eq hm.symm,
    rw ← hm,
    simpa [weighted_total_degree'] using hm' }
end

/-- The `weighted_total_degree` of the zero polynomial is `⊥`. -/
lemma weighted_total_degree_zero (w : σ → M) :
  weighted_total_degree w (0 : mv_polynomial σ R) = ⊥ :=
by simp only [weighted_total_degree, support_zero, finset.sup_empty]

lemma le_weighted_total_degree (w : σ → M) {φ : mv_polynomial σ R} {d : σ →₀ ℕ}
  (hd : d ∈ φ.support) : weighted_degree' w d ≤ φ.weighted_total_degree w :=
le_sup hd

end order_bot
end semilattice_sup

/-- A multivariate polynomial `φ` is weighted homogeneous of weighted degree `m` if all monomials
  occuring in `φ` have weighted degree `m`. -/
def is_weighted_homogeneous (w : σ → M) (φ : mv_polynomial σ R) (m : M) : Prop :=
∀ ⦃d⦄, coeff d φ ≠ 0 → weighted_degree' w d = m

variable (R)

/-- The submodule of homogeneous `mv_polynomial`s of degree `n`. -/
def weighted_homogeneous_submodule (w : σ → M) (m : M) :
  submodule R (mv_polynomial σ R) :=
{ carrier := { x | x.is_weighted_homogeneous w m },
  smul_mem' := λ r a ha c hc, begin
    rw coeff_smul at hc,
    exact ha (right_ne_zero_of_mul hc),
  end,
  zero_mem' := λ d hd, false.elim (hd $ coeff_zero _),
  add_mem' := λ a b ha hb c hc, begin
    rw coeff_add at hc,
    obtain h|h : coeff c a ≠ 0 ∨ coeff c b ≠ 0,
    { contrapose! hc, simp only [hc, add_zero] },
    { exact ha h },
    { exact hb h },
  end }

@[simp] lemma mem_weighted_homogeneous_submodule (w : σ → M) (m : M) (p : mv_polynomial σ R) :
  p ∈ weighted_homogeneous_submodule R w m ↔ p.is_weighted_homogeneous w m := iff.rfl

variables (R)

/-- The submodule ` weighted_homogeneous_submodule R w m` of homogeneous `mv_polynomial`s of
  degree `n` is equal to the `R`-submodule of all `p : (σ →₀ ℕ) →₀ R` such that
  `p.support ⊆ {d | weighted_degree' w d = m}`. While equal, the former has a
  convenient definitional reduction. -/
lemma weighted_homogeneous_submodule_eq_finsupp_supported (w : σ → M) (m : M) :
  weighted_homogeneous_submodule R w m =
  finsupp.supported _ R {d | weighted_degree' w d = m} :=
begin
  ext,
  simp only [mem_supported, set.subset_def, finsupp.mem_support_iff, mem_coe],
  refl,
end

variables {R}

/-- The submodule generated by products `Pm *Pn` of weighted homogeneous polynomials of degrees `m`
  and `n` is contained in the submodule of weighted homogeneous polynomials of degree `m + n`. -/
lemma weighted_homogeneous_submodule_mul (w : σ → M) (m n : M) :
  weighted_homogeneous_submodule R w m * weighted_homogeneous_submodule R w n ≤
    weighted_homogeneous_submodule R w (m + n) :=
begin
  rw submodule.mul_le,
  intros φ hφ ψ hψ c hc,
  rw [coeff_mul] at hc,
  obtain ⟨⟨d, e⟩, hde, H⟩ := finset.exists_ne_zero_of_sum_ne_zero hc,
  have aux : coeff d φ ≠ 0 ∧ coeff e ψ ≠ 0,
  { contrapose! H,
    by_cases h : coeff d φ = 0;
    simp only [*, ne.def, not_false_iff, zero_mul, mul_zero] at * },
  rw [← (finsupp.mem_antidiagonal.mp hde), ← hφ aux.1, ← hψ aux.2, map_add],
end

/-- Monomials are weighted homogeneous. -/
lemma is_weighted_homogeneous_monomial (w : σ → M) (d : σ →₀ ℕ) (r : R) {m : M}
  (hm : weighted_degree' w d = m) : is_weighted_homogeneous w (monomial d r) m :=
begin
  classical,
  intros c hc,
  rw coeff_monomial at hc,
  split_ifs at hc with h,
  { subst c, exact hm },
  { contradiction }
end

/-- A polynomial of weighted_total_degree `⊥` is weighted_homogeneous of degree `⊥`. -/
lemma is_weighted_homogeneous_of_total_degree_zero [semilattice_sup M] [order_bot M]
  (w : σ → M) {p : mv_polynomial σ R} (hp : weighted_total_degree w p = (⊥ : M)) :
  is_weighted_homogeneous w p (⊥ : M) :=
begin
  intros d hd,
  have h := weighted_total_degree_coe w p (mv_polynomial.ne_zero_iff.mpr ⟨d, hd⟩),
  simp only [weighted_total_degree', hp] at h,
  rw [eq_bot_iff, ← with_bot.coe_le_coe, ← h],
  exact finset.le_sup (mem_support_iff.mpr hd),
end

/-- Constant polynomials are weighted homogeneous of degree 0. -/
lemma is_weighted_homogeneous_C (w : σ → M) (r : R) :
  is_weighted_homogeneous w (C r : mv_polynomial σ R) 0 :=
is_weighted_homogeneous_monomial _ _ _ (map_zero _)

variables (R)

/-- 0 is weighted homogeneous of any degree. -/
lemma is_weighted_homogeneous_zero (w : σ → M) (m : M) :
  is_weighted_homogeneous w (0 : mv_polynomial σ R) m :=
(weighted_homogeneous_submodule R w m).zero_mem

/-- 1 is weighted homogeneous of degree 0. -/
lemma is_weighted_homogeneous_one (w : σ → M) :
  is_weighted_homogeneous w (1 : mv_polynomial σ R) 0 :=
is_weighted_homogeneous_C _ _

/-- An indeterminate `i : σ` is weighted homogeneous of degree `w i`. -/
lemma is_weighted_homogeneous_X (w : σ → M) (i : σ) :
  is_weighted_homogeneous w (X i : mv_polynomial σ R) (w i) :=
begin
  apply is_weighted_homogeneous_monomial,
  simp only [weighted_degree', linear_map.to_add_monoid_hom_coe, total_single, one_nsmul],
end

namespace is_weighted_homogeneous
variables {R} {φ ψ : mv_polynomial σ R} {m n : M}

/-- The weighted degree of a weighted homogeneous polynomial controls its support. -/
lemma coeff_eq_zero {w : σ → M} (hφ : is_weighted_homogeneous w φ n) (d : σ →₀ ℕ)
  (hd : weighted_degree' w d ≠ n) : coeff d φ = 0 :=
by { have aux := mt (@hφ d) hd, rwa not_not at aux }

/-- The weighted degree of a nonzero weighted homogeneous polynomial is well-defined. -/
lemma inj_right {w : σ → M} (hφ : φ ≠ 0) (hm : is_weighted_homogeneous w φ m)
  (hn : is_weighted_homogeneous w φ n) : m = n :=
begin
  obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero hφ,
  rw [← hm hd, ← hn hd]
end

/-- The sum of two weighted homogeneous polynomials of degree `n` is weighted homogeneous of
  weighted degree `n`. -/
lemma add {w : σ → M} (hφ : is_weighted_homogeneous w φ n) (hψ : is_weighted_homogeneous w ψ n) :
  is_weighted_homogeneous w (φ + ψ) n :=
(weighted_homogeneous_submodule R w n).add_mem hφ hψ

/-- The sum of weighted homogeneous polynomials of degree `n` is weighted homogeneous of
  weighted degree `n`. -/
lemma sum  {ι : Type*} (s : finset ι)  (φ : ι → mv_polynomial σ R) (n : M) {w : σ → M}
  (h : ∀ i ∈ s, is_weighted_homogeneous w (φ i) n) :
  is_weighted_homogeneous w (∑ i in s, φ i) n :=
(weighted_homogeneous_submodule R w n).sum_mem h

/-- The product of weighted homogeneous polynomials of weighted degrees `m` and `n` is weighted
  homogeneous of weighted degree `m + n`. -/
lemma mul {w : σ → M} (hφ : is_weighted_homogeneous w φ m) (hψ : is_weighted_homogeneous w ψ n) :
  is_weighted_homogeneous w (φ * ψ) (m + n) :=
weighted_homogeneous_submodule_mul w m n $ submodule.mul_mem_mul hφ hψ

/-- A product of weighted homogeneous polynomials is weighted homogeneous, with weighted degree
  equal to the sum of the weighted degrees. -/
lemma prod {ι : Type*} (s : finset ι) (φ : ι → mv_polynomial σ R) (n : ι → M) {w : σ → M} :
  (∀ i ∈ s, is_weighted_homogeneous w (φ i) (n i)) →
  is_weighted_homogeneous w (∏ i in s, φ i) (∑ i in s, n i) :=
begin
  classical,
  apply finset.induction_on s,
  { intro, simp only [is_weighted_homogeneous_one, finset.sum_empty, finset.prod_empty] },
  { intros i s his IH h,
    simp only [his, finset.prod_insert, finset.sum_insert, not_false_iff],
    apply (h i (finset.mem_insert_self _ _)).mul (IH _),
    intros j hjs,
    exact h j (finset.mem_insert_of_mem hjs) }
end

/-- A non zero weighted homogeneous polynomial of weighted degree `n` has weighted total degree
  `n`. -/
lemma weighted_total_degree [semilattice_sup M] {w : σ → M} (hφ : is_weighted_homogeneous w φ n)
  (h : φ ≠ 0) : weighted_total_degree' w φ = n :=
begin
  simp only [weighted_total_degree'],
  apply le_antisymm,
  { simp only [finset.sup_le_iff, mem_support_iff, with_bot.coe_le_coe],
    exact λ d hd, le_of_eq (hφ hd), },
  { obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero h,
    simp only [← hφ hd, finsupp.sum],
    replace hd := finsupp.mem_support_iff.mpr hd,
    exact finset.le_sup hd, }
end

/-- The weighted homogeneous submodules form a graded monoid. -/
instance weighted_homogeneous_submodule.gcomm_monoid {w : σ → M} :
  set_like.graded_monoid (weighted_homogeneous_submodule R w) :=
{ one_mem := is_weighted_homogeneous_one R w,
  mul_mem := λ i j xi xj, is_weighted_homogeneous.mul }

end is_weighted_homogeneous

variables {R}

/-- `weighted_homogeneous_component w n φ` is the part of `φ` that is weighted homogeneous of
  weighted degree `n`, with respect to the weights `w`.
  See `sum_weighted_homogeneous_component` for the statement that `φ` is equal to the sum
  of all its weighted homogeneous components. -/
def weighted_homogeneous_component (w : σ → M) (n : M) :
  mv_polynomial σ R →ₗ[R] mv_polynomial σ R :=
(submodule.subtype _).comp $ finsupp.restrict_dom _ _ {d | weighted_degree' w d = n}

section weighted_homogeneous_component

variables {w : σ → M} (n : M) (φ ψ : mv_polynomial σ R)

lemma coeff_weighted_homogeneous_component [decidable_eq M] (d : σ →₀ ℕ) :
  coeff d (weighted_homogeneous_component w n φ) =
    if weighted_degree' w d = n then coeff d φ else 0 :=
finsupp.filter_apply (λ d : σ →₀ ℕ, weighted_degree' w d = n) φ d

lemma weighted_homogeneous_component_apply [decidable_eq M] :
  weighted_homogeneous_component w n φ =
  ∑ d in φ.support.filter (λ d, weighted_degree' w d = n), monomial d (coeff d φ) :=
finsupp.filter_eq_sum (λ d : σ →₀ ℕ, weighted_degree' w d = n) φ

/-- The `n` weighted homogeneous component of a polynomial is weighted homogeneous of
weighted degree `n`. -/
lemma weighted_homogeneous_component_is_weighted_homogeneous :
  (weighted_homogeneous_component w n φ).is_weighted_homogeneous w n :=
begin
  classical,
  intros d hd,
  contrapose! hd,
  rw [coeff_weighted_homogeneous_component, if_neg hd]
end

@[simp] lemma weighted_homogeneous_component_C_mul (n : M) (r : R) :
  weighted_homogeneous_component w n (C r * φ) = C r * weighted_homogeneous_component w n φ :=
by simp only [C_mul', linear_map.map_smul]

lemma weighted_homogeneous_component_eq_zero' (h : ∀ d : σ →₀ ℕ, d ∈ φ.support →
  weighted_degree' w d ≠ n) : weighted_homogeneous_component w n φ = 0 :=
begin
  classical,
  rw [weighted_homogeneous_component_apply, sum_eq_zero],
  intros d hd, rw mem_filter at hd,
  exfalso, exact h _ hd.1 hd.2
end

lemma weighted_homogeneous_component_eq_zero [semilattice_sup M] [order_bot M]
  (h : weighted_total_degree w φ < n) : weighted_homogeneous_component w n φ = 0 :=
begin
  classical,
  rw [weighted_homogeneous_component_apply, sum_eq_zero],
  intros d hd, rw mem_filter at hd,
  exfalso,
  apply lt_irrefl n,
  nth_rewrite 0 ← hd.2,
  exact lt_of_le_of_lt (le_weighted_total_degree w hd.1) h,
end

lemma weighted_homogeneous_component_finsupp :
  (function.support (λ m, weighted_homogeneous_component w m φ)).finite :=
begin
  suffices : function.support (λ m, weighted_homogeneous_component w m φ) ⊆
    (λ d, weighted_degree' w d) '' φ.support,
  { exact finite.subset ((λ (d : σ →₀ ℕ), (weighted_degree' w) d) '' ↑(support φ)).to_finite this },
  intros m hm,
  by_contradiction hm', apply hm,
  simp only [mem_support, ne.def] at hm,
  simp only [set.mem_image, not_exists, not_and] at hm',
  exact weighted_homogeneous_component_eq_zero' m φ hm',
end

variable (w)

/-- Every polynomial is the sum of its weighted homogeneous components. -/
lemma sum_weighted_homogeneous_component :
  finsum (λ m, weighted_homogeneous_component w m φ) = φ :=
begin
  classical,
  rw finsum_eq_sum _ (weighted_homogeneous_component_finsupp φ),
  ext1 d,
  simp only [coeff_sum, coeff_weighted_homogeneous_component],
  rw finset.sum_eq_single (weighted_degree' w d),
  { rw if_pos rfl, },
  { intros m hm hm', rw if_neg hm'.symm, },
  { intro hm, rw if_pos rfl,
    simp only [finite.mem_to_finset, mem_support, ne.def, not_not] at hm,
    have := coeff_weighted_homogeneous_component (_ : M) φ d,
    rw [hm, if_pos rfl, coeff_zero] at this,
    exact this.symm, },
end

variable {w}

/-- The weighted homogeneous components of a weighted homogeneous polynomial. -/
lemma weighted_homogeneous_component_weighted_homogeneous_polynomial [decidable_eq M] (m n : M)
  (p : mv_polynomial σ R) (h : p ∈ weighted_homogeneous_submodule R w n) :
  weighted_homogeneous_component w m p = if m = n then p else 0 :=
begin
  simp only [mem_weighted_homogeneous_submodule] at h,
  ext x,
  rw coeff_weighted_homogeneous_component,
  by_cases zero_coeff : coeff x p = 0,
  { split_ifs,
    all_goals { simp only [zero_coeff, coeff_zero], }, },
  { rw h zero_coeff,
    simp only [show n = m ↔ m = n, from eq_comm],
    split_ifs with h1,
    { refl },
    { simp only [coeff_zero] } }
end

end weighted_homogeneous_component

end add_comm_monoid

section canonically_ordered_add_monoid

variables [canonically_ordered_add_monoid M] {w : σ → M} (φ : mv_polynomial σ R)

/-- If `M` is a `canonically_ordered_add_monoid`, then the `weighted_homogeneous_component`
  of weighted degree `0` of a polynomial is its constant coefficient. -/
@[simp] lemma weighted_homogeneous_component_zero [no_zero_smul_divisors ℕ M]
  (hw : ∀ i : σ, w i ≠ 0) : weighted_homogeneous_component w 0 φ = C (coeff 0 φ) :=
begin
  classical,
  ext1 d,
  rcases em (d = 0) with (rfl|hd),
  { simp only [coeff_weighted_homogeneous_component, if_pos, map_zero, coeff_zero_C] },
  { rw [coeff_weighted_homogeneous_component, if_neg, coeff_C, if_neg (ne.symm hd)],
    simp only [weighted_degree', linear_map.to_add_monoid_hom_coe, finsupp.total_apply,
      finsupp.sum, sum_eq_zero_iff, finsupp.mem_support_iff, ne.def, smul_eq_zero,
      not_forall, not_or_distrib, and_self_left, exists_prop],
    simp only [finsupp.ext_iff, finsupp.coe_zero, pi.zero_apply, not_forall] at hd,
    obtain ⟨i, hi⟩ := hd,
    exact ⟨i, hi, hw i⟩ }
end

end canonically_ordered_add_monoid

end mv_polynomial
