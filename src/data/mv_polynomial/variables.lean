/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/

import data.mv_polynomial.basic
import data.set.disjointed

/-!
# Degrees and variables of polynomials

This file establishes many results about the degree and variable sets of a multivariate polynomial.

The *variable set* of a polynomial $P \in R[X]$ is a `finset` containing each $x \in X$
that appears in a monomial in $P$.

The *degree set* of a polynomial $P \in R[X]$ is a `multiset` containing, for each $x$ in the
variable set, $n$ copies of $x$, where $n$ is the maximum number of copies of $x$ appearing in a
monomial of $P$.

## Main declarations

* `mv_polynomial.degrees p` : the multiset of variables representing the union of the multisets corresponding
  to each non-zero monomial in `p`. For example if `7 ≠ 0` in `R` and `p = x²y+7y³` then
  `degrees p = {x, x, y, y, y}`

* `mv_polynomial.vars p` : the finset of variables occurring in `p`. For example if `p = x⁴y+yz` then
  `vars p = {x, y, z}`

* `mv_polynomial.degree_of n p : ℕ` -- the total degree of `p` with respect to the variable `n`. For example
  if `p = x⁴y+yz` then `degree_of y p = 1`.

* `mv_polynomial.total_degree p : ℕ` -- the max of the sizes of the multisets `s` whose monomials `X^s` occur
  in `p`. For example if `p = x⁴y+yz` then `total_degree p = 5`.

## Notation

As in other polynomial files we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `α : Type*` `[comm_semiring α]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `a : α`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ α`

-/

noncomputable theory

open_locale classical big_operators

open set function finsupp add_monoid_algebra
open_locale big_operators

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

namespace mv_polynomial
variables {σ : Type*} {a a' a₁ a₂ : α} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section comm_semiring
variables [comm_semiring α] {p q : mv_polynomial σ α}


section degrees

/--
The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset.

(For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
-/
def degrees (p : mv_polynomial σ α) : multiset σ :=
p.support.sup (λs:σ →₀ ℕ, s.to_multiset)

lemma degrees_monomial (s : σ →₀ ℕ) (a : α) : degrees (monomial s a) ≤ s.to_multiset :=
finset.sup_le $ assume t h,
begin
  have := finsupp.support_single_subset h,
  rw [finset.mem_singleton] at this,
  rw this
end

lemma degrees_monomial_eq (s : σ →₀ ℕ) (a : α) (ha : a ≠ 0) :
  degrees (monomial s a) = s.to_multiset :=
le_antisymm (degrees_monomial s a) $ finset.le_sup $
  by rw [monomial, finsupp.support_single_ne_zero ha, finset.mem_singleton]

lemma degrees_C (a : α) : degrees (C a : mv_polynomial σ α) = 0 :=
multiset.le_zero.1 $ degrees_monomial _ _

lemma degrees_X (n : σ) : degrees (X n : mv_polynomial σ α) ≤ {n} :=
le_trans (degrees_monomial _ _) $ le_of_eq $ to_multiset_single _ _

lemma degrees_zero : degrees (0 : mv_polynomial σ α) = 0 :=
by { rw ← C_0, exact degrees_C 0 }

lemma degrees_one : degrees (1 : mv_polynomial σ α) = 0 := degrees_C 1

lemma degrees_add (p q : mv_polynomial σ α) : (p + q).degrees ≤ p.degrees ⊔ q.degrees :=
begin
  refine finset.sup_le (assume b hb, _),
  have := finsupp.support_add hb, rw finset.mem_union at this,
  cases this,
  { exact le_sup_left_of_le (finset.le_sup this) },
  { exact le_sup_right_of_le (finset.le_sup this) },
end

lemma degrees_sum {ι : Type*} (s : finset ι) (f : ι → mv_polynomial σ α) :
  (∑ i in s, f i).degrees ≤ s.sup (λi, (f i).degrees) :=
begin
  refine s.induction _ _,
  { simp only [finset.sum_empty, finset.sup_empty, degrees_zero], exact le_refl _ },
  { assume i s his ih,
    rw [finset.sup_insert, finset.sum_insert his],
    exact le_trans (degrees_add _ _) (sup_le_sup_left ih _) }
end

lemma degrees_mul (p q : mv_polynomial σ α) : (p * q).degrees ≤ p.degrees + q.degrees :=
begin
  refine finset.sup_le (assume b hb, _),
  have := support_mul p q hb,
  simp only [finset.mem_bind, finset.mem_singleton] at this,
  rcases this with ⟨a₁, h₁, a₂, h₂, rfl⟩,
  rw [finsupp.to_multiset_add],
  exact add_le_add (finset.le_sup h₁) (finset.le_sup h₂)
end

lemma degrees_prod {ι : Type*} (s : finset ι) (f : ι → mv_polynomial σ α) :
  (∏ i in s, f i).degrees ≤ ∑ i in s, (f i).degrees :=
begin
  refine s.induction _ _,
  { simp only [finset.prod_empty, finset.sum_empty, degrees_one] },
  { assume i s his ih,
    rw [finset.prod_insert his, finset.sum_insert his],
    exact le_trans (degrees_mul _ _) (add_le_add_left ih _) }
end

lemma degrees_pow (p : mv_polynomial σ α) :
  ∀(n : ℕ), (p^n).degrees ≤ n •ℕ p.degrees
| 0       := begin rw [pow_zero, degrees_one], exact multiset.zero_le _ end
| (n + 1) := le_trans (degrees_mul _ _) (add_le_add_left (degrees_pow n) _)

lemma mem_degrees {p : mv_polynomial σ α} {i : σ} :
  i ∈ p.degrees ↔ ∃ d, p.coeff d ≠ 0 ∧ i ∈ d.support :=
by simp only [degrees, finset.mem_sup, ← finsupp.mem_support_iff, coeff,
    finsupp.mem_to_multiset, exists_prop]

lemma le_degrees_add {p q : mv_polynomial σ α} (h : p.degrees.disjoint q.degrees) :
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
    rw [finsupp.mem_support_iff, ← coeff, coeff_add],
    suffices : q.coeff d = 0,
    { rwa [this, add_zero, coeff, ← finsupp.mem_support_iff], },
    rw [← finsupp.support_eq_empty, ← ne.def, ← finset.nonempty_iff_ne_empty] at h0,
    obtain ⟨j, hj⟩ := h0,
    contrapose! h,
    rw finsupp.mem_support_iff at hd,
    refine ⟨j, _, j, _, rfl⟩,
    all_goals { rw mem_degrees, refine ⟨d, _, hj⟩, assumption } }
end

lemma degrees_add_of_disjoint {p q : mv_polynomial σ α} (h : multiset.disjoint p.degrees q.degrees) :
  (p + q).degrees = p.degrees ∪ q.degrees :=
begin
  apply le_antisymm,
  { apply degrees_add },
  { apply multiset.union_le,
    { apply le_degrees_add h },
    { rw add_comm, apply le_degrees_add h.symm } }
end

lemma degrees_map [comm_semiring β] (p : mv_polynomial σ α) (f : α →+* β) :
  (map f p).degrees ⊆ p.degrees :=
begin
  dsimp only [degrees],
  apply multiset.subset_of_le,
  convert finset.sup_subset _ _,
  apply mv_polynomial.support_map_subset
end

lemma degrees_map_of_injective [comm_semiring β] (p : mv_polynomial σ α)
  {f : α →+* β} (hf : injective f) : (map f p).degrees = p.degrees :=
by simp only [degrees, mv_polynomial.support_map_of_injective _ hf]

end degrees

section vars

/-- `vars p` is the set of variables appearing in the polynomial `p` -/
def vars (p : mv_polynomial σ α) : finset σ := p.degrees.to_finset

@[simp] lemma vars_0 : (0 : mv_polynomial σ α).vars = ∅ :=
by rw [vars, degrees_zero, multiset.to_finset_zero]

@[simp] lemma vars_monomial (h : a ≠ 0) : (monomial s a).vars = s.support :=
by rw [vars, degrees_monomial_eq _ _ h, finsupp.to_finset_to_multiset]

@[simp] lemma vars_C : (C a : mv_polynomial σ α).vars = ∅ :=
by rw [vars, degrees_C, multiset.to_finset_zero]

@[simp] lemma vars_X (h : 0 ≠ (1 : α)) : (X n : mv_polynomial σ α).vars = {n} :=
by rw [X, vars_monomial h.symm, finsupp.support_single_ne_zero (one_ne_zero : 1 ≠ 0)]

lemma mem_support_not_mem_vars_zero {f : mv_polynomial σ α} {x : σ →₀ ℕ} (H : x ∈ f.support) {v : σ} (h : v ∉ vars f) :
  x v = 0 :=
begin
  rw [vars, multiset.mem_to_finset] at h,
  rw ←not_mem_support_iff,
  contrapose! h,
  unfold degrees,
  rw (show f.support = insert x f.support, from eq.symm $ finset.insert_eq_of_mem H),
  rw finset.sup_insert,
  simp only [multiset.mem_union, multiset.sup_eq_union],
  left,
  rwa [←to_finset_to_multiset, multiset.mem_to_finset] at h,
end

lemma vars_add_subset (p q : mv_polynomial σ α) :
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

section sum

variables {ι : Type*} (t : finset ι) (φ : ι → mv_polynomial σ α)

lemma vars_sum_subset :
  (∑ i in t, φ i).vars ⊆ finset.bind t (λ i, (φ i).vars) :=
begin
  apply t.induction_on,
  { simp },
  { intros a s has hsum,
    rw [finset.bind_insert, finset.sum_insert has],
    refine finset.subset.trans (vars_add_subset _ _)
      (finset.union_subset_union (finset.subset.refl _) _),
    assumption }
end

lemma vars_sum_of_disjoint (h : pairwise $ disjoint on (λ i, (φ i).vars)) :
  (∑ i in t, φ i).vars = finset.bind t (λ i, (φ i).vars) :=
begin
  apply t.induction_on,
  { simp },
  { intros a s has hsum,
    rw [finset.bind_insert, finset.sum_insert has, vars_add_of_disjoint, hsum],
    unfold pairwise on_fun at h,
    rw hsum,
    simp only [finset.disjoint_iff_ne] at h ⊢,
    intros v hv v2 hv2,
    rw finset.mem_bind at hv2,
    rcases hv2 with ⟨i, his, hi⟩,
    refine h a i _ _ hv _ hi,
    rintro rfl,
    contradiction }
end

end sum

section map

variables [comm_semiring β] (f : α →+* β)
variable (p)

lemma vars_map : (map f p).vars ⊆ p.vars :=
by simp [vars, degrees_map]

variable {f}
lemma vars_map_of_injective (hf : injective f) :
  (map f p).vars = p.vars :=
by simp [vars, degrees_map_of_injective _ hf]

lemma vars_monomial_single (i : σ) {e : ℕ} {r : α} (he : e ≠ 0) (hr : r ≠ 0) :
  (monomial (finsupp.single i e) r).vars = {i} :=
by rw [vars_monomial hr, finsupp.support_single_ne_zero he]

lemma mem_vars (i : σ) :
  i ∈ p.vars ↔ ∃ (d : σ →₀ ℕ) (H : d ∈ p.support), i ∈ d.support :=
by simp only [vars, multiset.mem_to_finset, mem_degrees, coeff, finsupp.mem_support_iff, exists_prop]

lemma vars_eq_support_bind_support : p.vars = p.support.bind finsupp.support :=
by { ext i, rw [mem_vars, finset.mem_bind] }

end map

end vars

section degree_of

/-- `degree_of n p` gives the highest power of X_n that appears in `p` -/
def degree_of (n : σ) (p : mv_polynomial σ α) : ℕ := p.degrees.count n

end degree_of

section total_degree
/-- `total_degree p` gives the maximum |s| over the monomials X^s in `p` -/
def total_degree (p : mv_polynomial σ α) : ℕ := p.support.sup (λs, s.sum $ λn e, e)

lemma total_degree_eq (p : mv_polynomial σ α) :
  p.total_degree = p.support.sup (λm, m.to_multiset.card) :=
begin
  rw [total_degree],
  congr, funext m,
  exact (finsupp.card_to_multiset _).symm
end

lemma total_degree_le_degrees_card (p : mv_polynomial σ α) :
  p.total_degree ≤ p.degrees.card :=
begin
  rw [total_degree_eq],
  exact finset.sup_le (assume s hs, multiset.card_le_of_le $ finset.le_sup hs)
end

@[simp] lemma total_degree_C (a : α) : (C a : mv_polynomial σ α).total_degree = 0 :=
nat.eq_zero_of_le_zero $ finset.sup_le $ assume n hn,
  have _ := finsupp.support_single_subset hn,
  begin
    rw [finset.mem_singleton] at this,
    subst this,
    exact le_refl _
  end

@[simp] lemma total_degree_zero : (0 : mv_polynomial σ α).total_degree = 0 :=
by rw [← C_0]; exact total_degree_C (0 : α)

@[simp] lemma total_degree_one : (1 : mv_polynomial σ α).total_degree = 0 :=
total_degree_C (1 : α)

@[simp] lemma total_degree_X {α} [comm_semiring α] [nontrivial α] (s : σ) :
  (X s : mv_polynomial σ α).total_degree = 1 :=
begin
  rw [total_degree, X, monomial, finsupp.support_single_ne_zero (one_ne_zero : (1 : α) ≠ 0)],
  simp only [finset.sup, sum_single_index, finset.fold_singleton, sup_bot_eq],
end

lemma total_degree_add (a b : mv_polynomial σ α) :
  (a + b).total_degree ≤ max a.total_degree b.total_degree :=
finset.sup_le $ assume n hn,
  have _ := finsupp.support_add hn,
  begin
    rw finset.mem_union at this,
    cases this,
    { exact le_max_left_of_le (finset.le_sup this) },
    { exact le_max_right_of_le (finset.le_sup this) }
  end

lemma total_degree_mul (a b : mv_polynomial σ α) :
  (a * b).total_degree ≤ a.total_degree + b.total_degree :=
finset.sup_le $ assume n hn,
  have _ := add_monoid_algebra.support_mul a b hn,
  begin
    simp only [finset.mem_bind, finset.mem_singleton] at this,
    rcases this with ⟨a₁, h₁, a₂, h₂, rfl⟩,
    rw [finsupp.sum_add_index],
    { exact add_le_add (finset.le_sup h₁) (finset.le_sup h₂) },
    { assume a, refl },
    { assume a b₁ b₂, refl }
  end

lemma total_degree_pow (a : mv_polynomial σ α) (n : ℕ) :
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
  ∀(s : list (mv_polynomial σ α)), s.prod.total_degree ≤ (s.map mv_polynomial.total_degree).sum
| []        := by rw [@list.prod_nil (mv_polynomial σ α) _, total_degree_one]; refl
| (p :: ps) :=
  begin
    rw [@list.prod_cons (mv_polynomial σ α) _, list.map, list.sum_cons],
    exact le_trans (total_degree_mul _ _) (add_le_add_left (total_degree_list_prod ps) _)
  end

lemma total_degree_multiset_prod (s : multiset (mv_polynomial σ α)) :
  s.prod.total_degree ≤ (s.map mv_polynomial.total_degree).sum :=
begin
  refine quotient.induction_on s (assume l, _),
  rw [multiset.quot_mk_to_coe, multiset.coe_prod, multiset.coe_map, multiset.coe_sum],
  exact total_degree_list_prod l
end

lemma total_degree_finset_prod {ι : Type*}
  (s : finset ι) (f : ι → mv_polynomial σ α) :
  (s.prod f).total_degree ≤ ∑ i in s, (f i).total_degree :=
begin
  refine le_trans (total_degree_multiset_prod _) _,
  rw [multiset.map_map],
  refl
end

lemma exists_degree_lt [fintype σ] (f : mv_polynomial σ α) (n : ℕ)
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

lemma coeff_eq_zero_of_total_degree_lt {f : mv_polynomial σ α} {d : σ →₀ ℕ}
  (h : f.total_degree < ∑ i in d.support, d i) :
  coeff d f = 0 :=
begin
  classical,
  rw [total_degree, finset.sup_lt_iff] at h,
  { specialize h d, rw mem_support_iff at h,
    refine not_not.mp (mt h _), exact lt_irrefl _, },
  { exact lt_of_le_of_lt (nat.zero_le _) h, }
end

end total_degree

section eval_vars

variables {R : Type u} {A : Type v} {S : Type w} (f : σ → A)
variables [comm_semiring R] [comm_semiring A] [algebra R A] [comm_semiring S]

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

end eval_vars

end comm_semiring

end mv_polynomial
