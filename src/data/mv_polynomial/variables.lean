/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
import algebra.big_operators.order
import data.mv_polynomial.monad
import data.set.pairwise

/-!
# Degrees and variables of polynomials

This file establishes many results about the degree and variable sets of a multivariate polynomial.

The *variable set* of a polynomial $P \in R[X]$ is a `finset` containing each $x \in X$
that appears in a monomial in $P$.

The *degree set* of a polynomial $P \in R[X]$ is a `multiset` containing, for each $x$ in the
variable set, $n$ copies of $x$, where $n$ is the maximum number of copies of $x$ appearing in a
monomial of $P$.

## Main declarations

* `mv_polynomial.degrees p` : the multiset of variables representing the union of the multisets
  corresponding to each non-zero monomial in `p`.
  For example if `7 ≠ 0` in `R` and `p = x²y+7y³` then `degrees p = {x, x, y, y, y}`

* `mv_polynomial.vars p` : the finset of variables occurring in `p`.
  For example if `p = x⁴y+yz` then `vars p = {x, y, z}`

* `mv_polynomial.degree_of n p : ℕ` : the total degree of `p` with respect to the variable `n`.
  For example if `p = x⁴y+yz` then `degree_of y p = 1`.

* `mv_polynomial.total_degree p : ℕ` :
  the max of the sizes of the multisets `s` whose monomials `X^s` occur in `p`.
  For example if `p = x⁴y+yz` then `total_degree p = 5`.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ τ : Type*` (indexing the variables)

+ `R : Type*` `[comm_semiring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `r : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ R`

-/

noncomputable theory

open_locale classical big_operators

open set function finsupp add_monoid_algebra
open_locale big_operators

universes u v w
variables {R : Type u} {S : Type v}

namespace mv_polynomial
variables {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section comm_semiring
variables [comm_semiring R] {p q : mv_polynomial σ R}


section degrees

/-! ### `degrees` -/

/--
The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset.

(For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
-/
def degrees (p : mv_polynomial σ R) : multiset σ :=
p.support.sup (λs:σ →₀ ℕ, s.to_multiset)

lemma degrees_monomial (s : σ →₀ ℕ) (a : R) : degrees (monomial s a) ≤ s.to_multiset :=
finset.sup_le $ assume t h,
begin
  have := finsupp.support_single_subset h,
  rw [finset.mem_singleton] at this,
  rw this
end

lemma degrees_monomial_eq (s : σ →₀ ℕ) (a : R) (ha : a ≠ 0) :
  degrees (monomial s a) = s.to_multiset :=
le_antisymm (degrees_monomial s a) $ finset.le_sup $
  by rw [support_monomial, if_neg ha, finset.mem_singleton]

lemma degrees_C (a : R) : degrees (C a : mv_polynomial σ R) = 0 :=
multiset.le_zero.1 $ degrees_monomial _ _

lemma degrees_X' (n : σ) : degrees (X n : mv_polynomial σ R) ≤ {n} :=
le_trans (degrees_monomial _ _) $ le_of_eq $ to_multiset_single _ _

@[simp] lemma degrees_X [nontrivial R] (n : σ) : degrees (X n : mv_polynomial σ R) = {n} :=
(degrees_monomial_eq _ (1 : R) one_ne_zero).trans (to_multiset_single _ _)

@[simp] lemma degrees_zero : degrees (0 : mv_polynomial σ R) = 0 :=
by { rw ← C_0, exact degrees_C 0 }

@[simp] lemma degrees_one : degrees (1 : mv_polynomial σ R) = 0 := degrees_C 1

lemma degrees_add (p q : mv_polynomial σ R) : (p + q).degrees ≤ p.degrees ⊔ q.degrees :=
begin
  refine finset.sup_le (assume b hb, _),
  have := finsupp.support_add hb, rw finset.mem_union at this,
  cases this,
  { exact le_sup_of_le_left (finset.le_sup this) },
  { exact le_sup_of_le_right (finset.le_sup this) },
end

lemma degrees_sum {ι : Type*} (s : finset ι) (f : ι → mv_polynomial σ R) :
  (∑ i in s, f i).degrees ≤ s.sup (λi, (f i).degrees) :=
begin
  refine s.induction _ _,
  { simp only [finset.sum_empty, finset.sup_empty, degrees_zero], exact le_refl _ },
  { assume i s his ih,
    rw [finset.sup_insert, finset.sum_insert his],
    exact le_trans (degrees_add _ _) (sup_le_sup_left ih _) }
end

lemma degrees_mul (p q : mv_polynomial σ R) : (p * q).degrees ≤ p.degrees + q.degrees :=
begin
  refine finset.sup_le (assume b hb, _),
  have := support_mul p q hb,
  simp only [finset.mem_bUnion, finset.mem_singleton] at this,
  rcases this with ⟨a₁, h₁, a₂, h₂, rfl⟩,
  rw [finsupp.to_multiset_add],
  exact add_le_add (finset.le_sup h₁) (finset.le_sup h₂)
end

lemma degrees_prod {ι : Type*} (s : finset ι) (f : ι → mv_polynomial σ R) :
  (∏ i in s, f i).degrees ≤ ∑ i in s, (f i).degrees :=
begin
  refine s.induction _ _,
  { simp only [finset.prod_empty, finset.sum_empty, degrees_one] },
  { assume i s his ih,
    rw [finset.prod_insert his, finset.sum_insert his],
    exact le_trans (degrees_mul _ _) (add_le_add_left ih _) }
end

lemma degrees_pow (p : mv_polynomial σ R) :
  ∀(n : ℕ), (p^n).degrees ≤ n • p.degrees
| 0       := begin rw [pow_zero, degrees_one], exact multiset.zero_le _ end
| (n + 1) := by { rw [pow_succ, add_smul, add_comm, one_smul],
    exact le_trans (degrees_mul _ _) (add_le_add_left (degrees_pow n) _) }

lemma mem_degrees {p : mv_polynomial σ R} {i : σ} :
  i ∈ p.degrees ↔ ∃ d, p.coeff d ≠ 0 ∧ i ∈ d.support :=
by simp only [degrees, multiset.mem_sup, ← mem_support_iff,
    finsupp.mem_to_multiset, exists_prop]

lemma le_degrees_add {p q : mv_polynomial σ R} (h : p.degrees.disjoint q.degrees) :
  p.degrees ≤ (p + q).degrees :=
begin
  apply finset.sup_le,
  intros d hd,
  rw multiset.disjoint_iff_ne at h,
  rw multiset.le_iff_count,
  intros i,
  rw [degrees, multiset.count_sup],
  simp only [finsupp.count_to_multiset],
  by_cases h0 : d = 0,
  { simp only [h0, zero_le, finsupp.zero_apply], },
  { refine @finset.le_sup _ _ _ (p + q).support _ d _,
    rw [mem_support_iff, coeff_add],
    suffices : q.coeff d = 0,
    { rwa [this, add_zero, coeff, ← finsupp.mem_support_iff], },
    rw [← finsupp.support_eq_empty, ← ne.def, ← finset.nonempty_iff_ne_empty] at h0,
    obtain ⟨j, hj⟩ := h0,
    contrapose! h,
    rw mem_support_iff at hd,
    refine ⟨j, _, j, _, rfl⟩,
    all_goals { rw mem_degrees, refine ⟨d, _, hj⟩, assumption } }
end

lemma degrees_add_of_disjoint
  {p q : mv_polynomial σ R} (h : multiset.disjoint p.degrees q.degrees) :
  (p + q).degrees = p.degrees ∪ q.degrees :=
begin
  apply le_antisymm,
  { apply degrees_add },
  { apply multiset.union_le,
    { apply le_degrees_add h },
    { rw add_comm, apply le_degrees_add h.symm } }
end

lemma degrees_map [comm_semiring S] (p : mv_polynomial σ R) (f : R →+* S) :
  (map f p).degrees ⊆ p.degrees :=
begin
  dsimp only [degrees],
  apply multiset.subset_of_le,
  apply finset.sup_mono,
  apply mv_polynomial.support_map_subset
end

lemma degrees_rename (f : σ → τ) (φ : mv_polynomial σ R) :
  (rename f φ).degrees ⊆ (φ.degrees.map f) :=
begin
  intros i,
  rw [mem_degrees, multiset.mem_map],
  rintro ⟨d, hd, hi⟩,
  obtain ⟨x, rfl, hx⟩ := coeff_rename_ne_zero _ _ _ hd,
  simp only [map_domain, finsupp.mem_support_iff] at hi,
  rw [sum_apply, finsupp.sum] at hi,
  contrapose! hi,
  rw [finset.sum_eq_zero],
  intros j hj,
  simp only [exists_prop, mem_degrees] at hi,
  specialize hi j ⟨x, hx, hj⟩,
  rw [single_apply, if_neg hi],
end

lemma degrees_map_of_injective [comm_semiring S] (p : mv_polynomial σ R)
  {f : R →+* S} (hf : injective f) : (map f p).degrees = p.degrees :=
by simp only [degrees, mv_polynomial.support_map_of_injective _ hf]

end degrees

section vars

/-! ### `vars` -/

/-- `vars p` is the set of variables appearing in the polynomial `p` -/
def vars (p : mv_polynomial σ R) : finset σ := p.degrees.to_finset

@[simp] lemma vars_0 : (0 : mv_polynomial σ R).vars = ∅ :=
by rw [vars, degrees_zero, multiset.to_finset_zero]

@[simp] lemma vars_monomial (h : r ≠ 0) : (monomial s r).vars = s.support :=
by rw [vars, degrees_monomial_eq _ _ h, finsupp.to_finset_to_multiset]

@[simp] lemma vars_C : (C r : mv_polynomial σ R).vars = ∅ :=
by rw [vars, degrees_C, multiset.to_finset_zero]

@[simp] lemma vars_X [nontrivial R] : (X n : mv_polynomial σ R).vars = {n} :=
by rw [X, vars_monomial (@one_ne_zero R _ _), finsupp.support_single_ne_zero (one_ne_zero : 1 ≠ 0)]

lemma mem_vars (i : σ) :
  i ∈ p.vars ↔ ∃ (d : σ →₀ ℕ) (H : d ∈ p.support), i ∈ d.support :=
by simp only [vars, multiset.mem_to_finset, mem_degrees, mem_support_iff,
  exists_prop]

lemma mem_support_not_mem_vars_zero
  {f : mv_polynomial σ R} {x : σ →₀ ℕ} (H : x ∈ f.support) {v : σ} (h : v ∉ vars f) :
  x v = 0 :=
begin
  rw [vars, multiset.mem_to_finset] at h,
  rw ← finsupp.not_mem_support_iff,
  contrapose! h,
  unfold degrees,
  rw (show f.support = insert x f.support, from eq.symm $ finset.insert_eq_of_mem H),
  rw finset.sup_insert,
  simp only [multiset.mem_union, multiset.sup_eq_union],
  left,
  rwa [←to_finset_to_multiset, multiset.mem_to_finset] at h,
end

lemma vars_add_subset (p q : mv_polynomial σ R) :
  (p + q).vars ⊆ p.vars ∪ q.vars :=
begin
  intros x hx,
  simp only [vars, finset.mem_union, multiset.mem_to_finset] at hx ⊢,
  simpa using multiset.mem_of_le (degrees_add _ _) hx,
end

lemma vars_add_of_disjoint (h : disjoint p.vars q.vars) :
  (p + q).vars = p.vars ∪ q.vars :=
begin
  apply finset.subset.antisymm (vars_add_subset p q),
  intros x hx,
  simp only [vars, multiset.disjoint_to_finset] at h hx ⊢,
  rw [degrees_add_of_disjoint h, multiset.to_finset_union],
  exact hx
end

section mul

lemma vars_mul (φ ψ : mv_polynomial σ R) : (φ * ψ).vars ⊆ φ.vars ∪ ψ.vars :=
begin
  intro i,
  simp only [mem_vars, finset.mem_union],
  rintro ⟨d, hd, hi⟩,
  rw [mem_support_iff, coeff_mul] at hd,
  contrapose! hd, cases hd,
  rw finset.sum_eq_zero,
  rintro ⟨d₁, d₂⟩ H,
  rw finsupp.mem_antidiagonal at H,
  subst H,
  obtain H|H : i ∈ d₁.support ∨ i ∈ d₂.support,
  { simpa only [finset.mem_union] using finsupp.support_add hi, },
  { suffices : coeff d₁ φ = 0, by simp [this],
    rw [coeff, ← finsupp.not_mem_support_iff], intro, solve_by_elim, },
  { suffices : coeff d₂ ψ = 0, by simp [this],
    rw [coeff, ← finsupp.not_mem_support_iff], intro, solve_by_elim, },
end

@[simp] lemma vars_one : (1 : mv_polynomial σ R).vars = ∅ :=
vars_C

lemma vars_pow (φ : mv_polynomial σ R) (n : ℕ) : (φ ^ n).vars ⊆ φ.vars :=
begin
  induction n with n ih,
  { simp },
  { rw pow_succ,
    apply finset.subset.trans (vars_mul _ _),
    exact finset.union_subset (finset.subset.refl _) ih }
end

/--
The variables of the product of a family of polynomials
are a subset of the union of the sets of variables of each polynomial.
-/
lemma vars_prod {ι : Type*} {s : finset ι} (f : ι → mv_polynomial σ R) :
  (∏ i in s, f i).vars ⊆ s.bUnion (λ i, (f i).vars) :=
begin
  apply s.induction_on,
  { simp },
  { intros a s hs hsub,
    simp only [hs, finset.bUnion_insert, finset.prod_insert, not_false_iff],
    apply finset.subset.trans (vars_mul _ _),
    exact finset.union_subset_union (finset.subset.refl _) hsub }
end

section integral_domain
variables {A : Type*} [integral_domain A]

lemma vars_C_mul (a : A) (ha : a ≠ 0) (φ : mv_polynomial σ A) : (C a * φ).vars = φ.vars :=
begin
  ext1 i,
  simp only [mem_vars, exists_prop, mem_support_iff],
  apply exists_congr,
  intro d,
  apply and_congr _ iff.rfl,
  rw [coeff_C_mul, mul_ne_zero_iff, eq_true_intro ha, true_and],
end

end integral_domain

end mul

section sum

variables {ι : Type*} (t : finset ι) (φ : ι → mv_polynomial σ R)

lemma vars_sum_subset :
  (∑ i in t, φ i).vars ⊆ finset.bUnion t (λ i, (φ i).vars) :=
begin
  apply t.induction_on,
  { simp },
  { intros a s has hsum,
    rw [finset.bUnion_insert, finset.sum_insert has],
    refine finset.subset.trans (vars_add_subset _ _)
      (finset.union_subset_union (finset.subset.refl _) _),
    assumption }
end

lemma vars_sum_of_disjoint (h : pairwise $ disjoint on (λ i, (φ i).vars)) :
  (∑ i in t, φ i).vars = finset.bUnion t (λ i, (φ i).vars) :=
begin
  apply t.induction_on,
  { simp },
  { intros a s has hsum,
    rw [finset.bUnion_insert, finset.sum_insert has, vars_add_of_disjoint, hsum],
    unfold pairwise on_fun at h,
    rw hsum,
    simp only [finset.disjoint_iff_ne] at h ⊢,
    intros v hv v2 hv2,
    rw finset.mem_bUnion at hv2,
    rcases hv2 with ⟨i, his, hi⟩,
    refine h a i _ _ hv _ hi,
    rintro rfl,
    contradiction }
end

end sum

section map

variables [comm_semiring S] (f : R →+* S)
variable (p)

lemma vars_map : (map f p).vars ⊆ p.vars :=
by simp [vars, degrees_map]

variable {f}
lemma vars_map_of_injective (hf : injective f) :
  (map f p).vars = p.vars :=
by simp [vars, degrees_map_of_injective _ hf]

lemma vars_monomial_single (i : σ) {e : ℕ} {r : R} (he : e ≠ 0) (hr : r ≠ 0) :
  (monomial (finsupp.single i e) r).vars = {i} :=
by rw [vars_monomial hr, finsupp.support_single_ne_zero he]

lemma vars_eq_support_bUnion_support : p.vars = p.support.bUnion finsupp.support :=
by { ext i, rw [mem_vars, finset.mem_bUnion] }

end map

end vars

section degree_of

/-! ### `degree_of` -/

/-- `degree_of n p` gives the highest power of X_n that appears in `p` -/
def degree_of (n : σ) (p : mv_polynomial σ R) : ℕ := p.degrees.count n

end degree_of

section total_degree

/-! ### `total_degree` -/

/-- `total_degree p` gives the maximum |s| over the monomials X^s in `p` -/
def total_degree (p : mv_polynomial σ R) : ℕ := p.support.sup (λs, s.sum $ λn e, e)

lemma total_degree_eq (p : mv_polynomial σ R) :
  p.total_degree = p.support.sup (λm, m.to_multiset.card) :=
begin
  rw [total_degree],
  congr, funext m,
  exact (finsupp.card_to_multiset _).symm
end

lemma total_degree_le_degrees_card (p : mv_polynomial σ R) :
  p.total_degree ≤ p.degrees.card :=
begin
  rw [total_degree_eq],
  exact finset.sup_le (assume s hs, multiset.card_le_of_le $ finset.le_sup hs)
end

@[simp] lemma total_degree_C (a : R) : (C a : mv_polynomial σ R).total_degree = 0 :=
nat.eq_zero_of_le_zero $ finset.sup_le $ assume n hn,
  have _ := finsupp.support_single_subset hn,
  begin
    rw [finset.mem_singleton] at this,
    subst this,
    exact le_refl _
  end

@[simp] lemma total_degree_zero : (0 : mv_polynomial σ R).total_degree = 0 :=
by rw [← C_0]; exact total_degree_C (0 : R)

@[simp] lemma total_degree_one : (1 : mv_polynomial σ R).total_degree = 0 :=
total_degree_C (1 : R)

@[simp] lemma total_degree_X {R} [comm_semiring R] [nontrivial R] (s : σ) :
  (X s : mv_polynomial σ R).total_degree = 1 :=
begin
  rw [total_degree, support_X],
  simp only [finset.sup, sum_single_index, finset.fold_singleton, sup_bot_eq],
end

lemma total_degree_add (a b : mv_polynomial σ R) :
  (a + b).total_degree ≤ max a.total_degree b.total_degree :=
finset.sup_le $ assume n hn,
  have _ := finsupp.support_add hn,
  begin
    rw finset.mem_union at this,
    cases this,
    { exact le_max_of_le_left (finset.le_sup this) },
    { exact le_max_of_le_right (finset.le_sup this) }
  end

lemma total_degree_mul (a b : mv_polynomial σ R) :
  (a * b).total_degree ≤ a.total_degree + b.total_degree :=
finset.sup_le $ assume n hn,
  have _ := add_monoid_algebra.support_mul a b hn,
  begin
    simp only [finset.mem_bUnion, finset.mem_singleton] at this,
    rcases this with ⟨a₁, h₁, a₂, h₂, rfl⟩,
    rw [finsupp.sum_add_index],
    { exact add_le_add (finset.le_sup h₁) (finset.le_sup h₂) },
    { assume a, refl },
    { assume a b₁ b₂, refl }
  end

lemma total_degree_pow (a : mv_polynomial σ R) (n : ℕ) :
  (a ^ n).total_degree ≤ n * a.total_degree :=
begin
  induction n with n ih,
  { simp only [nat.nat_zero_eq_zero, zero_mul, pow_zero, total_degree_one] },
  rw pow_succ,
  calc total_degree (a * a ^ n) ≤ a.total_degree + (a^n).total_degree : total_degree_mul _ _
    ... ≤ a.total_degree + n * a.total_degree : add_le_add_left ih _
    ... = (n+1) * a.total_degree : by rw [add_mul, one_mul, add_comm]
end

lemma total_degree_list_prod :
  ∀(s : list (mv_polynomial σ R)), s.prod.total_degree ≤ (s.map mv_polynomial.total_degree).sum
| []        := by rw [@list.prod_nil (mv_polynomial σ R) _, total_degree_one]; refl
| (p :: ps) :=
  begin
    rw [@list.prod_cons (mv_polynomial σ R) _, list.map, list.sum_cons],
    exact le_trans (total_degree_mul _ _) (add_le_add_left (total_degree_list_prod ps) _)
  end

lemma total_degree_multiset_prod (s : multiset (mv_polynomial σ R)) :
  s.prod.total_degree ≤ (s.map mv_polynomial.total_degree).sum :=
begin
  refine quotient.induction_on s (assume l, _),
  rw [multiset.quot_mk_to_coe, multiset.coe_prod, multiset.coe_map, multiset.coe_sum],
  exact total_degree_list_prod l
end

lemma total_degree_finset_prod {ι : Type*}
  (s : finset ι) (f : ι → mv_polynomial σ R) :
  (s.prod f).total_degree ≤ ∑ i in s, (f i).total_degree :=
begin
  refine le_trans (total_degree_multiset_prod _) _,
  rw [multiset.map_map],
  refl
end

lemma exists_degree_lt [fintype σ] (f : mv_polynomial σ R) (n : ℕ)
  (h : f.total_degree < n * fintype.card σ) {d : σ →₀ ℕ} (hd : d ∈ f.support) :
  ∃ i, d i < n :=
begin
  contrapose! h,
  calc n * fintype.card σ
        = ∑ s:σ, n         : by rw [finset.sum_const, nat.nsmul_eq_mul, mul_comm, finset.card_univ]
    ... ≤ ∑ s, d s         : finset.sum_le_sum (λ s _, h s)
    ... ≤ d.sum (λ i e, e) : by { rw [finsupp.sum_fintype], intros, refl }
    ... ≤ f.total_degree   : finset.le_sup hd,
end

lemma coeff_eq_zero_of_total_degree_lt {f : mv_polynomial σ R} {d : σ →₀ ℕ}
  (h : f.total_degree < ∑ i in d.support, d i) :
  coeff d f = 0 :=
begin
  classical,
  rw [total_degree, finset.sup_lt_iff] at h,
  { specialize h d, rw mem_support_iff at h,
    refine not_not.mp (mt h _), exact lt_irrefl _, },
  { exact lt_of_le_of_lt (nat.zero_le _) h, }
end

lemma total_degree_rename_le (f : σ → τ) (p : mv_polynomial σ R) :
  (rename f p).total_degree ≤ p.total_degree :=
finset.sup_le $ assume b,
begin
  assume h,
  rw rename_eq at h,
  have h' := finsupp.map_domain_support h,
  rw finset.mem_image at h',
  rcases h' with ⟨s, hs, rfl⟩,
  rw finsupp.sum_map_domain_index,
  exact le_trans (le_refl _) (finset.le_sup hs),
  exact assume _, rfl,
  exact assume _ _ _, rfl
end

end total_degree

section eval_vars

/-! ### `vars` and `eval` -/

variables [comm_semiring S]

lemma eval₂_hom_eq_constant_coeff_of_vars (f : R →+* S) {g : σ → S}
  {p : mv_polynomial σ R} (hp : ∀ i ∈ p.vars, g i = 0) :
  eval₂_hom f g p = f (constant_coeff p) :=
begin
  conv_lhs { rw p.as_sum },
  simp only [ring_hom.map_sum, eval₂_hom_monomial],
  by_cases h0 : constant_coeff p = 0,
  work_on_goal 0
  { rw [h0, f.map_zero, finset.sum_eq_zero],
    intros d hd },
  work_on_goal 1
  { rw [finset.sum_eq_single (0 : σ →₀ ℕ)],
    { rw [finsupp.prod_zero_index, mul_one],
      refl },
    intros d hd hd0, },
  repeat
  { obtain ⟨i, hi⟩ : d.support.nonempty,
    { rw [constant_coeff_eq, coeff, ← finsupp.not_mem_support_iff] at h0,
      rw [finset.nonempty_iff_ne_empty, ne.def, finsupp.support_eq_empty],
      rintro rfl, contradiction },
    rw [finsupp.prod, finset.prod_eq_zero hi, mul_zero],
    rw [hp, zero_pow (nat.pos_of_ne_zero $ finsupp.mem_support_iff.mp hi)],
    rw [mem_vars],
    exact ⟨d, hd, hi⟩ },
  { rw [constant_coeff_eq, coeff, ← ne.def, ← finsupp.mem_support_iff] at h0,
    intro, contradiction }
end

lemma aeval_eq_constant_coeff_of_vars [algebra R S] {g : σ → S}
  {p : mv_polynomial σ R} (hp : ∀ i ∈ p.vars, g i = 0) :
  aeval g p = algebra_map _ _ (constant_coeff p) :=
eval₂_hom_eq_constant_coeff_of_vars _ hp

lemma eval₂_hom_congr' {f₁ f₂ : R →+* S} {g₁ g₂ : σ → S} {p₁ p₂ : mv_polynomial σ R} :
  f₁ = f₂ → (∀ i, i ∈ p₁.vars → i ∈ p₂.vars → g₁ i = g₂ i) → p₁ = p₂ →
   eval₂_hom f₁ g₁ p₁ = eval₂_hom f₂ g₂ p₂ :=
begin
  rintro rfl h rfl,
  rename [p₁ p, f₁ f],
  rw p.as_sum,
  simp only [ring_hom.map_sum, eval₂_hom_monomial],
  apply finset.sum_congr rfl,
  intros d hd,
  congr' 1,
  simp only [finsupp.prod],
  apply finset.prod_congr rfl,
  intros i hi,
  have : i ∈ p.vars, { rw mem_vars, exact ⟨d, hd, hi⟩ },
  rw h i this this,
end

/-- If `f₁` and `f₂` are ring homs out of the polynomial ring and `p₁` and `p₂` are polynomials,
  then `f₁ p₁ = f₂ p₂` if `p₁ = p₂` and `f₁` and `f₂` are equal on `R` and on the variables
  of `p₁`.  -/
lemma hom_congr_vars {f₁ f₂ : mv_polynomial σ R →+* S} {p₁ p₂ : mv_polynomial σ R}
  (hC : f₁.comp C = f₂.comp C) (hv : ∀ i, i ∈ p₁.vars → i ∈ p₂.vars → f₁ (X i) = f₂ (X i))
  (hp : p₁ = p₂) : f₁ p₁ = f₂ p₂ :=
calc f₁ p₁ = eval₂_hom (f₁.comp C) (f₁ ∘ X) p₁ : ring_hom.congr_fun (by ext; simp) _
... = eval₂_hom (f₂.comp C) (f₂ ∘ X) p₂ :
  eval₂_hom_congr' hC hv hp
... = f₂ p₂ : ring_hom.congr_fun (by ext; simp) _

lemma exists_rename_eq_of_vars_subset_range
  (p : mv_polynomial σ R) (f : τ → σ)
  (hfi : injective f) (hf : ↑p.vars ⊆ set.range f) :
  ∃ q : mv_polynomial τ R, rename f q = p :=
⟨bind₁ (λ i : σ, option.elim (partial_inv f i) 0 X) p,
  begin
    show (rename f).to_ring_hom.comp _ p = ring_hom.id _ p,
    refine hom_congr_vars _ _ _,
    { ext1,
      simp [algebra_map_eq] },
    { intros i hip _,
      rcases hf hip with ⟨i, rfl⟩,
      simp [partial_inv_left hfi] },
    { refl }
  end⟩

lemma vars_bind₁ (f : σ → mv_polynomial τ R) (φ : mv_polynomial σ R) :
  (bind₁ f φ).vars ⊆ φ.vars.bUnion (λ i, (f i).vars) :=
begin
  calc (bind₁ f φ).vars
      = (φ.support.sum (λ (x : σ →₀ ℕ), (bind₁ f) (monomial x (coeff x φ)))).vars :
        by { rw [← alg_hom.map_sum, ← φ.as_sum], }
  ... ≤ φ.support.bUnion (λ (i : σ →₀ ℕ), ((bind₁ f) (monomial i (coeff i φ))).vars) :
        vars_sum_subset _ _
  ... = φ.support.bUnion (λ (d : σ →₀ ℕ), (C (coeff d φ) * ∏ i in d.support, f i ^ d i).vars) :
        by simp only [bind₁_monomial]
  ... ≤ φ.support.bUnion (λ (d : σ →₀ ℕ), d.support.bUnion (λ i, (f i).vars)) : _ -- proof below
  ... ≤ φ.vars.bUnion (λ (i : σ), (f i).vars) : _, -- proof below
  { apply finset.bUnion_mono,
    intros d hd,
    calc (C (coeff d φ) * ∏ (i : σ) in d.support, f i ^ d i).vars
        ≤ (C (coeff d φ)).vars ∪ (∏ (i : σ) in d.support, f i ^ d i).vars : vars_mul _ _
    ... ≤ (∏ (i : σ) in d.support, f i ^ d i).vars :
      by simp only [finset.empty_union, vars_C, finset.le_iff_subset, finset.subset.refl]
    ... ≤ d.support.bUnion (λ (i : σ), (f i ^ d i).vars) : vars_prod _
    ... ≤ d.support.bUnion (λ (i : σ), (f i).vars) : _,
    apply finset.bUnion_mono,
    intros i hi,
    apply vars_pow, },
  { intro j,
    simp_rw finset.mem_bUnion,
    rintro ⟨d, hd, ⟨i, hi, hj⟩⟩,
    exact ⟨i, (mem_vars _).mpr ⟨d, hd, hi⟩, hj⟩ }
end

lemma mem_vars_bind₁ (f : σ → mv_polynomial τ R) (φ : mv_polynomial σ R) {j : τ}
  (h : j ∈ (bind₁ f φ).vars) :
  ∃ (i : σ), i ∈ φ.vars ∧ j ∈ (f i).vars :=
by simpa only [exists_prop, finset.mem_bUnion, mem_support_iff, ne.def] using vars_bind₁ f φ h

lemma vars_rename (f : σ → τ) (φ : mv_polynomial σ R) :
  (rename f φ).vars ⊆ (φ.vars.image f) :=
begin
  intros i hi,
  simp only [vars, exists_prop, multiset.mem_to_finset, finset.mem_image] at hi ⊢,
  simpa only [multiset.mem_map] using degrees_rename _ _ hi
end

lemma mem_vars_rename (f : σ → τ) (φ : mv_polynomial σ R) {j : τ} (h : j ∈ (rename f φ).vars) :
  ∃ (i : σ), i ∈ φ.vars ∧ f i = j :=
by simpa only [exists_prop, finset.mem_image] using vars_rename f φ h

end eval_vars

end comm_semiring

end mv_polynomial
