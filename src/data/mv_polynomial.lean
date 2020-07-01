/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro, Shing Tak Lam
-/
import data.polynomial
import data.equiv.ring
import data.equiv.fin
import tactic.omega

/-!
# Multivariate polynomials

This file defines polynomial rings over a base ring (or even semiring),
with variables from a general type `σ` (which could be infinite).

## Important definitions

Let `R` be a commutative ring (or a semiring) and let `σ` be an arbitrary
type. This file creates the type `mv_polynomial σ R`, which mathematicians
might denote `R[X_i : i ∈ σ]`. It is the type of multivariate
(a.k.a. multivariable) polynomials, with variables
corresponding to the terms in `σ`, and coefficients in `R`.

### Notation

In the definitions below, we use the following notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[comm_semiring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ R`

### Definitions

* `mv_polynomial σ R` : the type of polynomials with variables of type `σ` and coefficients
  in the commutative semiring `R`

* `monomial s a` : the monomial which mathematically would be denoted `a * X^s`

* `C a` : the constant polynomial with value `a`

* `X i` : the degree one monomial corresponding to i; mathematically this might be denoted `Xᵢ`.

* `coeff s p` : the coefficient of `s` in `p`.

* `eval₂ (f : R → S) (g : σ → S) p` : given a semiring homomorphism from `R` to another
  semiring `S`, and a map `σ → S`, evaluates `p` at this valuation, returning a term of type `S`.
  Note that `eval₂` can be made using `eval` and `map` (see below), and it has been suggested
  that sticking to `eval` and `map` might make the code less brittle.

* `eval (g : σ → R) p` : given a map `σ → R`, evaluates `p` at this valuation,
  returning a term of type `R`

* `map (f : R → S) p` : returns the multivariate polynomial obtained from `p` by the change of
  coefficient semiring corresponding to `f`

* `degrees p` : the multiset of variables representing the union of the multisets corresponding
  to each non-zero monomial in `p`. For example if `7 ≠ 0` in `R` and `p = x²y+7y³` then
  `degrees p = {x, x, y, y, y}`

* `vars p` : the finset of variables occurring in `p`. For example if `p = x⁴y+yz` then
  `vars p = {x, y, z}`

* `degree_of n p : ℕ` -- the total degree of `p` with respect to the variable `n`. For example
  if `p = x⁴y+yz` then `degree_of y p = 1`.

* `total_degree p : ℕ` -- the max of the sizes of the multisets `s` whose monomials `X^s` occur
  in `p`. For example if `p = x⁴y+yz` then `total_degree p = 5`.

* `pderivative i p` : the partial derivative of `p` with respect to `i`.

## Implementation notes

Recall that if `Y` has a zero, then `X →₀ Y` is the type of functions from `X` to `Y` with finite
support, i.e. such that only finitely many elements of `X` get sent to non-zero terms in `Y`.
The definition of `mv_polynomial σ α` is `(σ →₀ ℕ) →₀ α` ; here `σ →₀ ℕ` denotes the space of all
monomials in the variables, and the function to `α` sends a monomial to its coefficient in
the polynomial being represented.

## Tags

polynomial, multivariate polynomial, multivariable polynomial
-/

noncomputable theory

open_locale classical big_operators

open set function finsupp add_monoid_algebra
open_locale big_operators

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

/-- Multivariate polynomial, where `σ` is the index set of the variables and
  `α` is the coefficient ring -/
def mv_polynomial (σ : Type*) (α : Type*) [comm_semiring α] := add_monoid_algebra α (σ →₀ ℕ)

namespace mv_polynomial
variables {σ : Type*} {a a' a₁ a₂ : α} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section comm_semiring
variables [comm_semiring α] {p q : mv_polynomial σ α}

instance decidable_eq_mv_polynomial [decidable_eq σ] [decidable_eq α] :
  decidable_eq (mv_polynomial σ α) := finsupp.decidable_eq
instance : comm_semiring (mv_polynomial σ α) := add_monoid_algebra.comm_semiring
instance : inhabited (mv_polynomial σ α) := ⟨0⟩
instance : has_scalar α (mv_polynomial σ α) := add_monoid_algebra.has_scalar
instance : semimodule α (mv_polynomial σ α) := add_monoid_algebra.semimodule
instance : algebra α (mv_polynomial σ α) := add_monoid_algebra.algebra

/-- the coercion turning an `mv_polynomial` into the function which reports the coefficient of a given monomial -/
def coeff_coe_to_fun : has_coe_to_fun (mv_polynomial σ α) :=
finsupp.has_coe_to_fun

local attribute [instance] coeff_coe_to_fun

/-- `monomial s a` is the monomial `a * X^s` -/
def monomial (s : σ →₀ ℕ) (a : α) : mv_polynomial σ α := single s a

/-- `C a` is the constant polynomial with value `a` -/
def C : α →+* mv_polynomial σ α :=
{ to_fun := monomial 0,
  map_zero' := by simp [monomial],
  map_one' := rfl,
  map_add' := λ a a', single_add,
  map_mul' := λ a a', by simp [monomial, single_mul_single] }

/-- `X n` is the degree `1` monomial `1*n` -/
def X (n : σ) : mv_polynomial σ α := monomial (single n 1) 1

@[simp] lemma C_0 : C 0 = (0 : mv_polynomial σ α) := by simp [C, monomial]; refl

@[simp] lemma C_1 : C 1 = (1 : mv_polynomial σ α) := rfl

lemma C_mul_monomial : C a * monomial s a' = monomial s (a * a') :=
by simp [C, monomial, single_mul_single]

@[simp] lemma C_add : (C (a + a') : mv_polynomial σ α) = C a + C a' := single_add

@[simp] lemma C_mul : (C (a * a') : mv_polynomial σ α) = C a * C a' := C_mul_monomial.symm

@[simp] lemma C_pow (a : α) (n : ℕ) : (C (a^n) : mv_polynomial σ α) = (C a)^n :=
by induction n; simp [pow_succ, *]

lemma C_injective (σ : Type*) (R : Type*) [comm_ring R] :
  function.injective (C : R → mv_polynomial σ R) :=
finsupp.single_injective _

@[simp] lemma C_inj {σ : Type*} (R : Type*) [comm_ring R] (r s : R) :
  (C r : mv_polynomial σ R) = C s ↔ r = s :=
(C_injective σ R).eq_iff

lemma C_eq_coe_nat (n : ℕ) : (C ↑n : mv_polynomial σ α) = n :=
by induction n; simp [nat.succ_eq_add_one, *]

lemma X_pow_eq_single : X n ^ e = monomial (single n e) (1 : α) :=
begin
  induction e,
  { simp [X], refl },
  { simp [pow_succ, e_ih],
    simp [X, monomial, single_mul_single, nat.succ_eq_add_one, add_comm] }
end

lemma monomial_add_single : monomial (s + single n e) a = (monomial s a * X n ^ e) :=
by rw [X_pow_eq_single, monomial, monomial, monomial, single_mul_single]; simp

lemma monomial_single_add : monomial (single n e + s) a = (X n ^ e * monomial s a) :=
by rw [X_pow_eq_single, monomial, monomial, monomial, single_mul_single]; simp

lemma single_eq_C_mul_X {s : σ} {a : α} {n : ℕ} :
  monomial (single s n) a = C a * (X s)^n :=
by { rw [← zero_add (single s n), monomial_add_single, C], refl }

@[simp] lemma monomial_add {s : σ →₀ ℕ} {a b : α} :
  monomial s a + monomial s b = monomial s (a + b) :=
by simp [monomial]

@[simp] lemma monomial_mul {s s' : σ →₀ ℕ} {a b : α} :
  monomial s a * monomial s' b = monomial (s + s') (a * b) :=
by rw [monomial, monomial, monomial, add_monoid_algebra.single_mul_single]

@[simp] lemma monomial_zero {s : σ →₀ ℕ}: monomial s (0 : α) = 0 :=
by rw [monomial, single_zero]; refl

@[simp] lemma sum_monomial  {A : Type*} [add_comm_monoid A]
  {u : σ →₀ ℕ} {r : α} {b : (σ →₀ ℕ) → α → A} (w : b u 0 = 0) :
  sum (monomial u r) b = b u r :=
sum_single_index w

lemma monomial_eq : monomial s a = C a * (s.prod $ λn e, X n ^ e : mv_polynomial σ α) :=
begin
  apply @finsupp.induction σ ℕ _ _ s,
  { simp only [C, prod_zero_index]; exact (mul_one _).symm },
  { assume n e s hns he ih,
    rw [monomial_single_add, ih, prod_add_index, prod_single_index, mul_left_comm],
    { simp only [pow_zero], },
    { intro a, simp only [pow_zero], },
    { intros, rw pow_add, }, }
end

@[recursor 5]
lemma induction_on {M : mv_polynomial σ α → Prop} (p : mv_polynomial σ α)
  (h_C : ∀a, M (C a)) (h_add : ∀p q, M p → M q → M (p + q)) (h_X : ∀p n, M p → M (p * X n)) :
  M p :=
have ∀s a, M (monomial s a),
begin
  assume s a,
  apply @finsupp.induction σ ℕ _ _ s,
  { show M (monomial 0 a), from h_C a, },
  { assume n e p hpn he ih,
    have : ∀e:ℕ, M (monomial p a * X n ^ e),
    { intro e,
      induction e,
      { simp [ih] },
      { simp [ih, pow_succ', (mul_assoc _ _ _).symm, h_X, e_ih] } },
    simp [add_comm, monomial_add_single, this] }
end,
finsupp.induction p
  (by have : M (C 0) := h_C 0; rwa [C_0] at this)
  (assume s a p hsp ha hp, h_add _ _ (this s a) hp)

theorem induction_on' {P : mv_polynomial σ α → Prop} (p : mv_polynomial σ α)
    (h1 : ∀ (u : σ →₀ ℕ) (a : α), P (monomial u a))
    (h2 : ∀ (p q : mv_polynomial σ α), P p → P q → P (p + q)) : P p :=
finsupp.induction p (suffices P (monomial 0 0), by rwa monomial_zero at this,
                     show P (monomial 0 0), from h1 0 0)
                    (λ a b f ha hb hPf, h2 _ _ (h1 _ _) hPf)


lemma hom_eq_hom [semiring γ]
  (f g : mv_polynomial σ α → γ) (hf : is_semiring_hom f) (hg : is_semiring_hom g)
  (hC : ∀a:α, f (C a) = g (C a)) (hX : ∀n:σ, f (X n) = g (X n)) (p : mv_polynomial σ α) :
  f p = g p :=
mv_polynomial.induction_on p hC
  begin assume p q hp hq, rw [is_semiring_hom.map_add f, is_semiring_hom.map_add g, hp, hq] end
  begin assume p n hp, rw [is_semiring_hom.map_mul f, is_semiring_hom.map_mul g, hp, hX] end

lemma is_id (f : mv_polynomial σ α → mv_polynomial σ α) (hf : is_semiring_hom f)
  (hC : ∀a:α, f (C a) = (C a)) (hX : ∀n:σ, f (X n) = (X n)) (p : mv_polynomial σ α) :
  f p = p :=
hom_eq_hom f id hf is_semiring_hom.id hC hX p

section coeff

section
-- While setting up `coeff`, we make `mv_polynomial` reducible so we can treat it as a function.
local attribute [reducible] mv_polynomial

/-- The coefficient of the monomial `m` in the multi-variable polynomial `p`. -/
def coeff (m : σ →₀ ℕ) (p : mv_polynomial σ α) : α := p m
end

lemma ext (p q : mv_polynomial σ α) :
  (∀ m, coeff m p = coeff m q) → p = q := ext

lemma ext_iff (p q : mv_polynomial σ α) :
  p = q ↔ (∀ m, coeff m p = coeff m q) :=
⟨ λ h m, by rw h, ext p q⟩

@[simp] lemma coeff_add (m : σ →₀ ℕ) (p q : mv_polynomial σ α) :
  coeff m (p + q) = coeff m p + coeff m q := add_apply

@[simp] lemma coeff_zero (m : σ →₀ ℕ) :
  coeff m (0 : mv_polynomial σ α) = 0 := rfl

@[simp] lemma coeff_zero_X (i : σ) : coeff 0 (X i : mv_polynomial σ α) = 0 :=
single_eq_of_ne (λ h, by cases single_eq_zero.1 h)

instance coeff.is_add_monoid_hom (m : σ →₀ ℕ) :
  is_add_monoid_hom (coeff m : mv_polynomial σ α → α) :=
{ map_add := coeff_add m,
  map_zero := coeff_zero m }

lemma coeff_sum {X : Type*} (s : finset X) (f : X → mv_polynomial σ α) (m : σ →₀ ℕ) :
  coeff m (∑ x in s, f x) = ∑ x in s, coeff m (f x) :=
(s.sum_hom _).symm

lemma monic_monomial_eq (m) : monomial m (1:α) = (m.prod $ λn e, X n ^ e : mv_polynomial σ α) :=
by simp [monomial_eq]

@[simp] lemma coeff_monomial (m n) (a) :
  coeff m (monomial n a : mv_polynomial σ α) = if n = m then a else 0 :=
by convert single_apply

@[simp] lemma coeff_C (m) (a) :
  coeff m (C a : mv_polynomial σ α) = if 0 = m then a else 0 :=
by convert single_apply

lemma coeff_X_pow (i : σ) (m) (k : ℕ) :
  coeff m (X i ^ k : mv_polynomial σ α) = if single i k = m then 1 else 0 :=
begin
  have := coeff_monomial m (finsupp.single i k) (1:α),
  rwa [@monomial_eq _ _ (1:α) (finsupp.single i k) _,
    C_1, one_mul, finsupp.prod_single_index] at this,
  exact pow_zero _
end

lemma coeff_X' (i : σ) (m) :
  coeff m (X i : mv_polynomial σ α) = if single i 1 = m then 1 else 0 :=
by rw [← coeff_X_pow, pow_one]

@[simp] lemma coeff_X (i : σ) :
  coeff (single i 1) (X i : mv_polynomial σ α) = 1 :=
by rw [coeff_X', if_pos rfl]

@[simp] lemma coeff_C_mul (m) (a : α) (p : mv_polynomial σ α) : coeff m (C a * p) = a * coeff m p :=
begin
  rw [mul_def], simp only [C, monomial], dsimp, rw [monomial],
  rw sum_single_index,
  { simp only [zero_add],
    convert sum_apply,
    simp only [single_apply, finsupp.sum],
    rw finset.sum_eq_single m,
    { rw if_pos rfl, refl },
    { intros m' hm' H, apply if_neg, exact H },
    { intros hm, rw if_pos rfl, rw not_mem_support_iff at hm, simp [hm] } },
  simp only [zero_mul, single_zero, zero_add],
  exact sum_zero, -- TODO doesn't work if we put this inside the simp
end

lemma coeff_mul (p q : mv_polynomial σ α) (n : σ →₀ ℕ) :
  coeff n (p * q) = ∑ x in (antidiagonal n).support, coeff x.1 p * coeff x.2 q :=
begin
  rw mul_def,
  have := @finset.sum_sigma (σ →₀ ℕ) α _ _ p.support (λ _, q.support)
    (λ x, if (x.1 + x.2 = n) then coeff x.1 p * coeff x.2 q else 0),
  convert this.symm using 1; clear this,
  { rw [coeff],
    repeat {rw sum_apply, apply finset.sum_congr rfl, intros, dsimp only},
    convert single_apply },
  { have : (antidiagonal n).support.filter (λ x, x.1 ∈ p.support ∧ x.2 ∈ q.support) ⊆
           (antidiagonal n).support := finset.filter_subset _,
    rw [← finset.sum_sdiff this, finset.sum_eq_zero, zero_add], swap,
    { intros x hx,
      rw [finset.mem_sdiff, not_iff_not_of_iff (finset.mem_filter),
          not_and, not_and, not_mem_support_iff] at hx,
      by_cases H : x.1 ∈ p.support,
      { rw [coeff, coeff, hx.2 hx.1 H, mul_zero] },
      { rw not_mem_support_iff at H, rw [coeff, H, zero_mul] } },
    symmetry,
    rw [← finset.sum_sdiff (finset.filter_subset _), finset.sum_eq_zero, zero_add], swap,
    { intros x hx,
      rw [finset.mem_sdiff, not_iff_not_of_iff (finset.mem_filter), not_and] at hx,
      simp only [if_neg (hx.2 hx.1)] },
    { apply finset.sum_bij, swap 5,
      { intros x hx, exact (x.1, x.2) },
      { intros x hx, rw [finset.mem_filter, finset.mem_sigma] at hx,
        simpa [finset.mem_filter, mem_antidiagonal_support] using hx.symm },
      { intros x hx, rw finset.mem_filter at hx, simp only [if_pos hx.2], },
      { rintros ⟨i,j⟩ ⟨k,l⟩ hij hkl, simpa using and.intro },
      { rintros ⟨i,j⟩ hij, refine ⟨⟨i,j⟩, _, _⟩, { apply_instance },
        { rw [finset.mem_filter, mem_antidiagonal_support] at hij,
          simpa [finset.mem_filter, finset.mem_sigma] using hij.symm },
        { refl } } },
    all_goals { apply_instance } }
end

@[simp] lemma coeff_mul_X (m) (s : σ) (p : mv_polynomial σ α) :
  coeff (m + single s 1) (p * X s) = coeff m p :=
begin
  have : (m, single s 1) ∈ (m + single s 1).antidiagonal.support := mem_antidiagonal_support.2 rfl,
  rw [coeff_mul, ← finset.insert_erase this, finset.sum_insert (finset.not_mem_erase _ _),
      finset.sum_eq_zero, add_zero, coeff_X, mul_one],
  rintros ⟨i,j⟩ hij,
  rw [finset.mem_erase, mem_antidiagonal_support] at hij,
  by_cases H : single s 1 = j,
  { subst j, simpa using hij },
  { rw [coeff_X', if_neg H, mul_zero] },
end

lemma coeff_mul_X' (m) (s : σ) (p : mv_polynomial σ α) :
  coeff m (p * X s) = if s ∈ m.support then coeff (m - single s 1) p else 0 :=
begin
  split_ifs with h h,
  { conv_rhs {rw ← coeff_mul_X _ s},
    congr' 1, ext t,
    by_cases hj : s = t,
    { subst t, simp only [nat_sub_apply, add_apply, single_eq_same],
      refine (nat.sub_add_cancel $ nat.pos_of_ne_zero _).symm, rwa mem_support_iff at h },
    { simp [single_eq_of_ne hj] } },
  { delta coeff, rw ← not_mem_support_iff, intro hm, apply h,
    have H := support_mul _ _ hm, simp only [finset.mem_bind] at H,
    rcases H with ⟨j, hj, i', hi', H⟩,
    delta X monomial at hi', rw mem_support_single at hi', cases hi', subst i',
    erw finset.mem_singleton at H, subst m,
    rw [mem_support_iff, add_apply, single_apply, if_pos rfl],
    intro H, rw [_root_.add_eq_zero_iff] at H, exact one_ne_zero H.2 }
end

end coeff

section as_sum

@[simp]
lemma support_sum_monomial_coeff (p : mv_polynomial σ α) : ∑ v in p.support, monomial v (coeff v p) = p :=
finsupp.sum_single p

lemma as_sum (p : mv_polynomial σ α) : p = ∑ v in p.support, monomial v (coeff v p) :=
(support_sum_monomial_coeff p).symm

end as_sum

section eval₂
variables [comm_semiring β]
variables (f : α → β) (g : σ → β)

/-- Evaluate a polynomial `p` given a valuation `g` of all the variables
  and a ring hom `f` from the scalar ring to the target -/
def eval₂ (p : mv_polynomial σ α) : β :=
p.sum (λs a, f a * s.prod (λn e, g n ^ e))

lemma eval₂_eq (g : α →+* β) (x : σ → β) (f : mv_polynomial σ α) :
  f.eval₂ g x = ∑ d in f.support, g (f.coeff d) * ∏ i in d.support, x i ^ d i :=
rfl

lemma eval₂_eq' [fintype σ] (g : α →+* β) (x : σ → β) (f : mv_polynomial σ α) :
  f.eval₂ g x = ∑ d in f.support, g (f.coeff d) * ∏ i, x i ^ d i :=
by { simp only [eval₂_eq, ← finsupp.prod_pow], refl }

@[simp] lemma eval₂_zero : (0 : mv_polynomial σ α).eval₂ f g = 0 :=
finsupp.sum_zero_index

section
variables [is_semiring_hom f]

@[simp] lemma eval₂_add : (p + q).eval₂ f g = p.eval₂ f g + q.eval₂ f g :=
finsupp.sum_add_index
  (by simp [is_semiring_hom.map_zero f])
  (by simp [add_mul, is_semiring_hom.map_add f])

@[simp] lemma eval₂_monomial : (monomial s a).eval₂ f g = f a * s.prod (λn e, g n ^ e) :=
finsupp.sum_single_index (by simp [is_semiring_hom.map_zero f])

@[simp] lemma eval₂_C (a) : (C a).eval₂ f g = f a :=
by simp [eval₂_monomial, C, prod_zero_index]

@[simp] lemma eval₂_one : (1 : mv_polynomial σ α).eval₂ f g = 1 :=
(eval₂_C _ _ _).trans (is_semiring_hom.map_one f)

@[simp] lemma eval₂_X (n) : (X n).eval₂ f g = g n :=
by simp [eval₂_monomial,
  is_semiring_hom.map_one f, X, prod_single_index, pow_one]

lemma eval₂_mul_monomial :
  ∀{s a}, (p * monomial s a).eval₂ f g = p.eval₂ f g * f a * s.prod (λn e, g n ^ e) :=
begin
  apply mv_polynomial.induction_on p,
  { assume a' s a,
    simp [C_mul_monomial, eval₂_monomial, is_semiring_hom.map_mul f] },
  { assume p q ih_p ih_q, simp [add_mul, eval₂_add, ih_p, ih_q] },
  { assume p n ih s a,
    from calc (p * X n * monomial s a).eval₂ f g = (p * monomial (single n 1 + s) a).eval₂ f g :
        by simp [monomial_single_add, -add_comm, pow_one, mul_assoc]
      ... = (p * monomial (single n 1) 1).eval₂ f g * f a * s.prod (λn e, g n ^ e) :
        by simp [ih, prod_single_index, prod_add_index, pow_one, pow_add, mul_assoc, mul_left_comm,
          is_semiring_hom.map_one f, -add_comm] }
end

@[simp] lemma eval₂_mul : ∀{p}, (p * q).eval₂ f g = p.eval₂ f g * q.eval₂ f g :=
begin
  apply mv_polynomial.induction_on q,
  { simp [C, eval₂_monomial, eval₂_mul_monomial, prod_zero_index] },
  { simp [mul_add, eval₂_add] {contextual := tt} },
  { simp [X, eval₂_monomial, eval₂_mul_monomial, (mul_assoc _ _ _).symm] { contextual := tt} }
end

@[simp] lemma eval₂_pow {p:mv_polynomial σ α} : ∀{n:ℕ}, (p ^ n).eval₂ f g = (p.eval₂ f g)^n
| 0       := eval₂_one _ _
| (n + 1) := by rw [pow_add, pow_one, pow_add, pow_one, eval₂_mul, eval₂_pow]

instance eval₂.is_semiring_hom : is_semiring_hom (eval₂ f g) :=
{ map_zero := eval₂_zero _ _,
  map_one := eval₂_one _ _,
  map_add := λ p q, eval₂_add _ _,
  map_mul := λ p q, eval₂_mul _ _ }

/-- `mv_polynomial.eval₂` as a `ring_hom`. -/
def eval₂_hom (f : α →+* β) (g : σ → β) : mv_polynomial σ α →+* β := ring_hom.of (eval₂ f g)

@[simp] lemma coe_eval₂_hom (f : α →+* β) (g : σ → β) : ⇑(eval₂_hom f g) = eval₂ f g := rfl

end

section
local attribute [instance, priority 10] is_semiring_hom.comp
lemma eval₂_comp_left {γ} [comm_semiring γ]
  (k : β → γ) [is_semiring_hom k]
  (f : α → β) [is_semiring_hom f] (g : σ → β)
  (p) : k (eval₂ f g p) = eval₂ (k ∘ f) (k ∘ g) p :=
by apply mv_polynomial.induction_on p; simp [
  eval₂_add, is_semiring_hom.map_add k,
  eval₂_mul, is_semiring_hom.map_mul k] {contextual := tt}
end

@[simp] lemma eval₂_eta (p : mv_polynomial σ α) : eval₂ C X p = p :=
by apply mv_polynomial.induction_on p;
   simp [eval₂_add, eval₂_mul] {contextual := tt}

lemma eval₂_congr (g₁ g₂ : σ → β)
  (h : ∀ {i : σ} {c : σ →₀ ℕ}, i ∈ c.support → coeff c p ≠ 0 → g₁ i = g₂ i) :
  p.eval₂ f g₁ = p.eval₂ f g₂ :=
begin
  apply finset.sum_congr rfl,
  intros c hc, dsimp, congr' 1,
  apply finset.prod_congr rfl,
  intros i hi, dsimp, congr' 1,
  apply h hi,
  rwa finsupp.mem_support_iff at hc
end

variables [is_semiring_hom f]

@[simp] lemma eval₂_prod (s : finset γ) (p : γ → mv_polynomial σ α) :
  eval₂ f g (∏ x in s, p x) = ∏ x in s, eval₂ f g (p x) :=
(s.prod_hom _).symm

@[simp] lemma eval₂_sum (s : finset γ) (p : γ → mv_polynomial σ α) :
  eval₂ f g (∑ x in s, p x) = ∑ x in s, eval₂ f g (p x) :=
(s.sum_hom _).symm

attribute [to_additive] eval₂_prod

lemma eval₂_assoc (q : γ → mv_polynomial σ α) (p : mv_polynomial γ α) :
  eval₂ f (λ t, eval₂ f g (q t)) p = eval₂ f g (eval₂ C q p) :=
by { rw eval₂_comp_left (eval₂ f g), congr, funext, simp }

end eval₂

section eval
variables {f : σ → α}

/-- Evaluate a polynomial `p` given a valuation `f` of all the variables -/
def eval (f : σ → α) : mv_polynomial σ α → α := eval₂ id f

lemma eval_eq (x : σ → α) (f : mv_polynomial σ α) :
  f.eval x = ∑ d in f.support, f.coeff d * ∏ i in d.support, x i ^ d i :=
rfl

lemma eval_eq' [fintype σ] (x : σ → α) (f : mv_polynomial σ α) :
f.eval x = ∑ d in f.support, f.coeff d * ∏ i, x i ^ d i :=
eval₂_eq' (ring_hom.id α) x f

@[simp] lemma eval_zero : (0 : mv_polynomial σ α).eval f = 0 := eval₂_zero _ _

@[simp] lemma eval_one : (1 : mv_polynomial σ α).eval f = 1 := eval₂_one _ _

@[simp] lemma eval_add : (p + q).eval f = p.eval f + q.eval f := eval₂_add _ _

lemma eval_monomial : (monomial s a).eval f = a * s.prod (λn e, f n ^ e) :=
eval₂_monomial _ _

@[simp] lemma eval_C : ∀ a, (C a).eval f = a := eval₂_C _ _

@[simp] lemma eval_X : ∀ n, (X n).eval f = f n := eval₂_X _ _

@[simp] lemma eval_mul : (p * q).eval f = p.eval f * q.eval f := eval₂_mul _ _

@[simp] lemma eval_pow (n : ℕ) : (p ^ n).eval f = (p.eval f) ^ n := eval₂_pow _ _

instance eval.is_semiring_hom : is_semiring_hom (eval f) :=
eval₂.is_semiring_hom _ _

lemma eval_sum {ι : Type*} (s : finset ι) (f : ι → mv_polynomial σ α) (g : σ → α) :
  eval g (∑ i in s, f i) = ∑ i in s, eval g (f i) :=
eval₂_sum (ring_hom.id α) g s f

@[to_additive]
lemma eval_prod {ι : Type*} (s : finset ι) (f : ι → mv_polynomial σ α) (g : σ → α) :
  eval g (∏ i in s, f i) = ∏ i in s, eval g (f i) :=
eval₂_prod (ring_hom.id α) g s f

theorem eval_assoc {τ}
  (f : σ → mv_polynomial τ α) (g : τ → α)
  (p : mv_polynomial σ α) :
  p.eval (eval g ∘ f) = (eval₂ C f p).eval g :=
begin
  rw eval₂_comp_left (eval g),
  unfold eval, congr; funext a; simp
end

end eval

section map
variables [comm_semiring β]
variables (f : α → β)

/-- `map f p` maps a polynomial `p` across a ring hom `f` -/
def map : mv_polynomial σ α → mv_polynomial σ β := eval₂ (C ∘ f) X

variables [is_semiring_hom f]

instance is_semiring_hom_C_f :
  is_semiring_hom ((C : β → mv_polynomial σ β) ∘ f) :=
is_semiring_hom.comp _ _

@[simp] theorem map_monomial (s : σ →₀ ℕ) (a : α) : map f (monomial s a) = monomial s (f a) :=
(eval₂_monomial _ _).trans monomial_eq.symm

@[simp] theorem map_C : ∀ (a : α), map f (C a : mv_polynomial σ α) = C (f a) := map_monomial _ _

@[simp] theorem map_X : ∀ (n : σ), map f (X n : mv_polynomial σ α) = X n := eval₂_X _ _

@[simp] theorem map_one : map f (1 : mv_polynomial σ α) = 1 := eval₂_one _ _

@[simp] theorem map_add (p q : mv_polynomial σ α) :
  map f (p + q) = map f p + map f q := eval₂_add _ _

@[simp] theorem map_mul (p q : mv_polynomial σ α) :
  map f (p * q) = map f p * map f q := eval₂_mul _ _

@[simp] lemma map_pow (p : mv_polynomial σ α) (n : ℕ) :
  map f (p^n) = (map f p)^n := eval₂_pow _ _

instance map.is_semiring_hom :
  is_semiring_hom (map f : mv_polynomial σ α → mv_polynomial σ β) :=
eval₂.is_semiring_hom _ _

theorem map_id : ∀ (p : mv_polynomial σ α), map id p = p := eval₂_eta

theorem map_map [comm_semiring γ]
  (g : β → γ) [is_semiring_hom g]
  (p : mv_polynomial σ α) :
  map g (map f p) = map (g ∘ f) p :=
(eval₂_comp_left (map g) (C ∘ f) X p).trans $
by congr; funext a; simp

theorem eval₂_eq_eval_map (g : σ → β) (p : mv_polynomial σ α) :
  p.eval₂ f g = (map f p).eval g :=
begin
  unfold map eval,
  rw eval₂_comp_left (eval₂ id g),
  congr; funext a; simp
end

lemma eval₂_comp_right {γ} [comm_semiring γ]
  (k : β → γ) [is_semiring_hom k]
  (f : α → β) [is_semiring_hom f] (g : σ → β)
  (p) : k (eval₂ f g p) = eval₂ k (k ∘ g) (map f p) :=
begin
  apply mv_polynomial.induction_on p,
  { intro r, rw [eval₂_C, map_C, eval₂_C] },
  { intros p q hp hq, rw [eval₂_add, is_semiring_hom.map_add k, map_add, eval₂_add, hp, hq] },
  { intros p s hp,
    rw [eval₂_mul, is_semiring_hom.map_mul k, map_mul, eval₂_mul, map_X, hp, eval₂_X, eval₂_X] }
end

lemma map_eval₂ (f : α → β) [is_semiring_hom f] (g : γ → mv_polynomial δ α) (p : mv_polynomial γ α) :
  map f (eval₂ C g p) = eval₂ C (map f ∘ g) (map f p) :=
begin
  apply mv_polynomial.induction_on p,
  { intro r, rw [eval₂_C, map_C, map_C, eval₂_C] },
  { intros p q hp hq, rw [eval₂_add, map_add, hp, hq, map_add, eval₂_add] },
  { intros p s hp,
    rw [eval₂_mul, map_mul, hp, map_mul, map_X, eval₂_mul, eval₂_X, eval₂_X] }
end

lemma coeff_map (p : mv_polynomial σ α) : ∀ (m : σ →₀ ℕ), coeff m (p.map f) = f (coeff m p) :=
begin
  apply mv_polynomial.induction_on p; clear p,
  { intros r m, rw [map_C], simp only [coeff_C], split_ifs, {refl}, rw is_semiring_hom.map_zero f },
  { intros p q hp hq m, simp only [hp, hq, map_add, coeff_add], rw is_semiring_hom.map_add f },
  { intros p i hp m, simp only [hp, map_mul, map_X],
    simp only [hp, mem_support_iff, coeff_mul_X'],
    split_ifs, {refl},
    rw is_semiring_hom.map_zero f }
end

lemma map_injective (hf : function.injective f) :
  function.injective (map f : mv_polynomial σ α → mv_polynomial σ β) :=
begin
  intros p q h,
  simp only [ext_iff, coeff_map] at h ⊢,
  intro m,
  exact hf (h m),
end

end map

section degrees

section comm_semiring

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

end comm_semiring

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

@[simp] lemma total_degree_X {α} [comm_semiring α] [nonzero α] (s : σ) :
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

end total_degree

end comm_semiring

section comm_ring
variable [comm_ring α]
variables {p q : mv_polynomial σ α}

instance : comm_ring (mv_polynomial σ α) := add_monoid_algebra.comm_ring

instance C.is_ring_hom : is_ring_hom (C : α → mv_polynomial σ α) :=
by apply is_ring_hom.of_semiring

variables (σ a a')
@[simp] lemma C_sub : (C (a - a') : mv_polynomial σ α) = C a - C a' := is_ring_hom.map_sub _

@[simp] lemma C_neg : (C (-a) : mv_polynomial σ α) = -C a := is_ring_hom.map_neg _

@[simp] lemma coeff_neg (m : σ →₀ ℕ) (p : mv_polynomial σ α) :
  coeff m (-p) = -coeff m p := finsupp.neg_apply

@[simp] lemma coeff_sub (m : σ →₀ ℕ) (p q : mv_polynomial σ α) :
  coeff m (p - q) = coeff m p - coeff m q := finsupp.sub_apply

instance coeff.is_add_group_hom (m : σ →₀ ℕ) :
  is_add_group_hom (coeff m : mv_polynomial σ α → α) :=
{ map_add := coeff_add m }

variables {σ} (p)
theorem C_mul' : mv_polynomial.C a * p = a • p :=
begin
  apply finsupp.induction p,
  { exact (mul_zero $ mv_polynomial.C a).trans (@smul_zero α (mv_polynomial σ α) _ _ _ a).symm },
  intros p b f haf hb0 ih,
  rw [mul_add, ih, @smul_add α (mv_polynomial σ α) _ _ _ a], congr' 1,
  rw [add_monoid_algebra.mul_def, finsupp.smul_single],
  simp only [mv_polynomial.C],
  dsimp [mv_polynomial.monomial],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, zero_add],
  { rw [mul_zero, finsupp.single_zero] },
  { rw finsupp.sum_single_index,
    all_goals { rw [zero_mul, finsupp.single_zero] }, }
end

lemma smul_eq_C_mul (p : mv_polynomial σ α) (a : α) : a • p = C a * p :=
begin
  rw [← finsupp.sum_single p, @finsupp.smul_sum (σ →₀ ℕ) α α, finsupp.mul_sum],
  refine finset.sum_congr rfl (assume n _, _),
  simp only [finsupp.smul_single],
  exact C_mul_monomial.symm
end

@[simp] lemma smul_eval (x) (p : mv_polynomial σ α) (s) : (s • p).eval x = s * p.eval x :=
by rw [smul_eq_C_mul, eval_mul, eval_C]

section degrees

lemma degrees_neg (p : mv_polynomial σ α) : (- p).degrees = p.degrees :=
by rw [degrees, finsupp.support_neg]; refl

lemma degrees_sub (p q : mv_polynomial σ α) :
  (p - q).degrees ≤ p.degrees ⊔ q.degrees :=
le_trans (degrees_add p (-q)) $ by rw [degrees_neg]

end degrees

section eval₂

variables [comm_ring β]
variables (f : α → β) [is_ring_hom f] (g : σ → β)

instance eval₂.is_ring_hom : is_ring_hom (eval₂ f g) :=
by apply is_ring_hom.of_semiring

@[simp] lemma eval₂_sub : (p - q).eval₂ f g = p.eval₂ f g - q.eval₂ f g := is_ring_hom.map_sub _

@[simp] lemma eval₂_neg : (-p).eval₂ f g = -(p.eval₂ f g) := is_ring_hom.map_neg _

lemma hom_C (f : mv_polynomial σ ℤ → β) [is_ring_hom f] (n : ℤ) : f (C n) = (n : β) :=
((ring_hom.of f).comp (ring_hom.of C)).eq_int_cast n

/-- A ring homomorphism f : Z[X_1, X_2, ...] → R
is determined by the evaluations f(X_1), f(X_2), ... -/
@[simp] lemma eval₂_hom_X {α : Type u} (c : ℤ → β) [is_ring_hom c]
  (f : mv_polynomial α ℤ → β) [is_ring_hom f] (x : mv_polynomial α ℤ) :
  eval₂ c (f ∘ X) x = f x :=
mv_polynomial.induction_on x
(λ n, by { rw [hom_C f, eval₂_C], exact (ring_hom.of c).eq_int_cast n })
(λ p q hp hq, by { rw [eval₂_add, hp, hq], exact (is_ring_hom.map_add f).symm })
(λ p n hp, by { rw [eval₂_mul, eval₂_X, hp], exact (is_ring_hom.map_mul f).symm })

/-- Ring homomorphisms out of integer polynomials on a type `σ` are the same as
functions out of the type `σ`, -/
def hom_equiv : (mv_polynomial σ ℤ →+* β) ≃ (σ → β) :=
{ to_fun := λ f, ⇑f ∘ X,
  inv_fun := λ f, eval₂_hom (int.cast_ring_hom β) f,
  left_inv := λ f, ring_hom.ext  $ eval₂_hom_X _ _,
  right_inv := λ f, funext $ λ x, by simp only [coe_eval₂_hom, function.comp_app, eval₂_X] }

end eval₂

section eval

variables (f : σ → α)

instance eval.is_ring_hom : is_ring_hom (eval f) := eval₂.is_ring_hom _ _

@[simp] lemma eval_sub : (p - q).eval f = p.eval f - q.eval f := is_ring_hom.map_sub _

@[simp] lemma eval_neg : (-p).eval f = -(p.eval f) := is_ring_hom.map_neg _

end eval

section map

variables [comm_ring β]
variables (f : α → β) [is_ring_hom f]

instance is_ring_hom_C_f : is_ring_hom ((C : β → mv_polynomial σ β) ∘ f) :=
is_ring_hom.comp _ _

instance map.is_ring_hom : is_ring_hom (map f : mv_polynomial σ α → mv_polynomial σ β) :=
eval₂.is_ring_hom _ _

@[simp] lemma map_sub : (p - q).map f = p.map f - q.map f := is_ring_hom.map_sub _

@[simp] lemma map_neg : (-p).map f = -(p.map f) := is_ring_hom.map_neg _

end map

section total_degree

@[simp] lemma total_degree_neg (a : mv_polynomial σ α) :
  (-a).total_degree = a.total_degree :=
by simp only [total_degree, finsupp.support_neg]

lemma total_degree_sub (a b : mv_polynomial σ α) :
  (a - b).total_degree ≤ max a.total_degree b.total_degree :=
calc (a - b).total_degree = (a + -b).total_degree                : by rw sub_eq_add_neg
                      ... ≤ max a.total_degree (-b).total_degree : total_degree_add a (-b)
                      ... = max a.total_degree b.total_degree    : by rw total_degree_neg

end total_degree

section aeval

/-- The algebra of multivariate polynomials. -/

variables (R : Type u) (A : Type v) (f : σ → A)
variables [comm_ring R] [comm_ring A] [algebra R A]

/-- A map `σ → A` where `A` is an algebra over `R` generates an `R`-algebra homomorphism
from multivariate polynomials over `σ` to `A`. -/
def aeval : mv_polynomial σ R →ₐ[R] A :=
{ commutes' := λ r, eval₂_C _ _ _
  .. eval₂_hom (algebra_map R A) f }

theorem aeval_def (p : mv_polynomial σ R) : aeval R A f p = eval₂ (algebra_map R A) f p := rfl

@[simp] lemma aeval_X (s : σ) : aeval R A f (X s) = f s := eval₂_X _ _ _

@[simp] lemma aeval_C (r : R) : aeval R A f (C r) = algebra_map R A r := eval₂_C _ _ _

theorem eval_unique (φ : mv_polynomial σ R →ₐ[R] A) :
  φ = aeval R A (φ ∘ X) :=
begin
  ext p,
  apply mv_polynomial.induction_on p,
  { intro r, rw aeval_C, exact φ.commutes r },
  { intros f g ih1 ih2,
    rw [φ.map_add, ih1, ih2, alg_hom.map_add] },
  { intros p j ih,
    rw [φ.map_mul, alg_hom.map_mul, aeval_X, ih] }
end

end aeval

end comm_ring

section rename
variables {α} [comm_semiring α]

/-- Rename all the variables in a multivariable polynomial. -/
def rename (f : β → γ) : mv_polynomial β α → mv_polynomial γ α :=
eval₂ C (X ∘ f)

instance rename.is_semiring_hom (f : β → γ) :
  is_semiring_hom (rename f : mv_polynomial β α → mv_polynomial γ α) :=
by unfold rename; apply_instance

@[simp] lemma rename_C (f : β → γ) (a : α) : rename f (C a) = C a :=
eval₂_C _ _ _

@[simp] lemma rename_X (f : β → γ) (b : β) : rename f (X b : mv_polynomial β α) = X (f b) :=
eval₂_X _ _ _

@[simp] lemma rename_zero (f : β → γ) :
  rename f (0 : mv_polynomial β α) = 0 :=
eval₂_zero _ _

@[simp] lemma rename_one (f : β → γ) :
  rename f (1 : mv_polynomial β α) = 1 :=
eval₂_one _ _

@[simp] lemma rename_add (f : β → γ) (p q : mv_polynomial β α) :
  rename f (p + q) = rename f p + rename f q :=
eval₂_add _ _

@[simp] lemma rename_neg {α} [comm_ring α]
  (f : β → γ) (p : mv_polynomial β α) :
  rename f (-p) = -rename f p :=
eval₂_neg _ _ _

@[simp] lemma rename_sub {α} [comm_ring α]
  (f : β → γ) (p q : mv_polynomial β α) :
  rename f (p - q) = rename f p - rename f q :=
eval₂_sub _ _ _

@[simp] lemma rename_mul (f : β → γ) (p q : mv_polynomial β α) :
  rename f (p * q) = rename f p * rename f q :=
eval₂_mul _ _

@[simp] lemma rename_pow (f : β → γ) (p : mv_polynomial β α) (n : ℕ) :
  rename f (p^n) = (rename f p)^n :=
eval₂_pow _ _

lemma map_rename [comm_semiring β] (f : α → β) [is_semiring_hom f]
  (g : γ → δ) (p : mv_polynomial γ α) :
  map f (rename g p) = rename g (map f p) :=
mv_polynomial.induction_on p
  (λ a, by simp)
  (λ p q hp hq, by simp [hp, hq])
  (λ p n hp, by simp [hp])

@[simp] lemma rename_rename (f : β → γ) (g : γ → δ) (p : mv_polynomial β α) :
  rename g (rename f p) = rename (g ∘ f) p :=
show rename g (eval₂ C (X ∘ f) p) = _,
  by simp only [eval₂_comp_left (rename g) C (X ∘ f) p, (∘), rename_C, rename_X]; refl

@[simp] lemma rename_id (p : mv_polynomial β α) : rename id p = p :=
eval₂_eta p

lemma rename_monomial (f : β → γ) (p : β →₀ ℕ) (a : α) :
  rename f (monomial p a) = monomial (p.map_domain f) a :=
begin
  rw [rename, eval₂_monomial, monomial_eq, finsupp.prod_map_domain_index],
  { exact assume n, pow_zero _ },
  { exact assume n i₁ i₂, pow_add _ _ _ }
end

lemma rename_eq (f : β → γ) (p : mv_polynomial β α) :
  rename f p = finsupp.map_domain (finsupp.map_domain f) p :=
begin
  simp only [rename, eval₂, finsupp.map_domain],
  congr, ext s a : 2,
  rw [← monomial, monomial_eq, finsupp.prod_sum_index],
  congr, ext n i : 2,
  rw [finsupp.prod_single_index],
  exact pow_zero _,
  exact assume a, pow_zero _,
  exact assume a b c, pow_add _ _ _
end

lemma rename_injective (f : β → γ) (hf : function.injective f) :
  function.injective (rename f : mv_polynomial β α → mv_polynomial γ α) :=
have (rename f : mv_polynomial β α → mv_polynomial γ α) =
  finsupp.map_domain (finsupp.map_domain f) := funext (rename_eq f),
begin
  rw this,
  exact finsupp.map_domain_injective (finsupp.map_domain_injective hf)
end

lemma total_degree_rename_le (f : β → γ) (p : mv_polynomial β α) :
  (p.rename f).total_degree ≤ p.total_degree :=
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

section
variables [comm_semiring β] (f : α → β) [is_semiring_hom f]
variables (k : γ → δ) (g : δ → β) (p : mv_polynomial γ α)

lemma eval₂_rename : (p.rename k).eval₂ f g = p.eval₂ f (g ∘ k) :=
by apply mv_polynomial.induction_on p; { intros, simp [*] }

lemma rename_eval₂ (g : δ → mv_polynomial γ α) :
  (p.eval₂ C (g ∘ k)).rename k = (p.rename k).eval₂ C (rename k ∘ g) :=
by apply mv_polynomial.induction_on p; { intros, simp [*] }

lemma rename_prodmk_eval₂ (d : δ) (g : γ → mv_polynomial γ α) :
  (p.eval₂ C g).rename (prod.mk d) = p.eval₂ C (λ x, (g x).rename (prod.mk d)) :=
by apply mv_polynomial.induction_on p; { intros, simp [*] }

lemma eval₂_rename_prodmk (g : δ × γ → β) (d : δ) :
  (rename (prod.mk d) p).eval₂ f g = eval₂ f (λ i, g (d, i)) p :=
by apply mv_polynomial.induction_on p; { intros, simp [*] }

lemma eval_rename_prodmk (g : δ × γ → α) (d : δ) :
  (rename (prod.mk d) p).eval g = eval (λ i, g (d, i)) p :=
eval₂_rename_prodmk id _ _ _

end

/-- Every polynomial is a polynomial in finitely many variables. -/
theorem exists_finset_rename (p : mv_polynomial γ α) :
  ∃ (s : finset γ) (q : mv_polynomial {x // x ∈ s} α), p = q.rename coe :=
begin
  apply induction_on p,
  { intro r, exact ⟨∅, C r, by rw rename_C⟩ },
  { rintro p q ⟨s, p, rfl⟩ ⟨t, q, rfl⟩,
    refine ⟨s ∪ t, ⟨_, _⟩⟩,
    { exact rename (subtype.map id (finset.subset_union_left s t)) p +
            rename (subtype.map id (finset.subset_union_right s t)) q },
    { rw [rename_add, rename_rename, rename_rename], refl } },
  { rintro p n ⟨s, p, rfl⟩,
    refine ⟨insert n s, ⟨_, _⟩⟩,
  { exact rename (subtype.map id (finset.subset_insert n s)) p * X ⟨n, s.mem_insert_self n⟩ },
    { rw [rename_mul, rename_X, rename_rename], refl } }
end

/-- Every polynomial is a polynomial in finitely many variables. -/
theorem exists_fin_rename (p : mv_polynomial γ α) :
  ∃ (n : ℕ) (f : fin n → γ) (hf : injective f) (q : mv_polynomial (fin n) α), p = q.rename f :=
begin
  obtain ⟨s, q, rfl⟩ := exists_finset_rename p,
  obtain ⟨n, ⟨e⟩⟩ := fintype.exists_equiv_fin {x // x ∈ s},
  refine ⟨n, coe ∘ e.symm, subtype.val_injective.comp e.symm.injective, q.rename e, _⟩,
  rw [← rename_rename, rename_rename e],
  simp only [function.comp, equiv.symm_apply_apply, rename_rename]
end

end rename

lemma eval₂_cast_comp {β : Type u} {γ : Type v} (f : γ → β)
  {α : Type w} [comm_ring α] (c : ℤ → α) [is_ring_hom c] (g : β → α) (x : mv_polynomial γ ℤ) :
  eval₂ c (g ∘ f) x = eval₂ c g (rename f x) :=
mv_polynomial.induction_on x
(λ n, by simp only [eval₂_C, rename_C])
(λ p q hp hq, by simp only [hp, hq, rename, eval₂_add])
(λ p n hp, by simp only [hp, rename, eval₂_X, eval₂_mul])

instance rename.is_ring_hom
  {α} [comm_ring α] (f : β → γ) :
  is_ring_hom (rename f : mv_polynomial β α → mv_polynomial γ α) :=
@is_ring_hom.of_semiring (mv_polynomial β α) (mv_polynomial γ α) _ _ (rename f)
  (rename.is_semiring_hom f)

section equiv

variables (α) [comm_semiring α]

/-- The ring isomorphism between multivariable polynomials in no variables and the ground ring. -/
def pempty_ring_equiv : mv_polynomial pempty α ≃+* α :=
{ to_fun    := mv_polynomial.eval₂ id $ pempty.elim,
  inv_fun   := C,
  left_inv  := is_id _ (by apply_instance) (assume a, by rw [eval₂_C]; refl) (assume a, a.elim),
  right_inv := λ r, eval₂_C _ _ _,
  map_mul'  := λ _ _, eval₂_mul _ _,
  map_add'  := λ _ _, eval₂_add _ _ }

/--
The ring isomorphism between multivariable polynomials in a single variable and
polynomials over the ground ring.
-/
def punit_ring_equiv : mv_polynomial punit α ≃+* polynomial α :=
{ to_fun    := eval₂ polynomial.C (λu:punit, polynomial.X),
  inv_fun   := polynomial.eval₂ mv_polynomial.C (X punit.star),
  left_inv  :=
    begin
      refine is_id _ _ _ _,
      apply is_semiring_hom.comp (eval₂ polynomial.C (λu:punit, polynomial.X)) _; apply_instance,
      { assume a, rw [eval₂_C, polynomial.eval₂_C] },
      { rintros ⟨⟩, rw [eval₂_X, polynomial.eval₂_X] }
    end,
  right_inv := assume p, polynomial.induction_on p
    (assume a, by rw [polynomial.eval₂_C, mv_polynomial.eval₂_C])
    (assume p q hp hq, by rw [polynomial.eval₂_add, mv_polynomial.eval₂_add, hp, hq])
    (assume p n hp,
      by rw [polynomial.eval₂_mul, polynomial.eval₂_pow, polynomial.eval₂_X, polynomial.eval₂_C,
        eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]),
  map_mul'  := λ _ _, eval₂_mul _ _,
  map_add'  := λ _ _, eval₂_add _ _ }

/-- The ring isomorphism between multivariable polynomials induced by an equivalence of the variables.  -/
def ring_equiv_of_equiv (e : β ≃ γ) : mv_polynomial β α ≃+* mv_polynomial γ α :=
{ to_fun    := rename e,
  inv_fun   := rename e.symm,
  left_inv  := λ p, by simp only [rename_rename, (∘), e.symm_apply_apply]; exact rename_id p,
  right_inv := λ p, by simp only [rename_rename, (∘), e.apply_symm_apply]; exact rename_id p,
  map_mul'  := rename_mul e,
  map_add'  := rename_add e }

/-- The ring isomorphism between multivariable polynomials induced by a ring isomorphism of the ground ring. -/
def ring_equiv_congr [comm_semiring γ] (e : α ≃+* γ) : mv_polynomial β α ≃+* mv_polynomial β γ :=
{ to_fun    := map e,
  inv_fun   := map e.symm,
  left_inv  := assume p,
    have (e.symm ∘ e) = id,
    { ext a, exact e.symm_apply_apply a },
    by simp only [map_map, this, map_id],
  right_inv := assume p,
    have (e ∘ e.symm) = id,
    { ext a, exact e.apply_symm_apply a },
    by simp only [map_map, this, map_id],
  map_mul'  := map_mul _,
  map_add'  := map_add _ }

section
variables (β γ δ)

/--
The function from multivariable polynomials in a sum of two types,
to multivariable polynomials in one of the types,
with coefficents in multivariable polynomials in the other type.

See `sum_ring_equiv` for the ring isomorphism.
-/
def sum_to_iter : mv_polynomial (β ⊕ γ) α → mv_polynomial β (mv_polynomial γ α) :=
eval₂ (C ∘ C) (λbc, sum.rec_on bc X (C ∘ X))

instance is_semiring_hom_C_C :
  is_semiring_hom (C ∘ C : α → mv_polynomial β (mv_polynomial γ α)) :=
@is_semiring_hom.comp _ _ _ _ C _ _ _ C _

instance is_semiring_hom_sum_to_iter : is_semiring_hom (sum_to_iter α β γ) :=
eval₂.is_semiring_hom _ _

lemma sum_to_iter_C (a : α) : sum_to_iter α β γ (C a) = C (C a) :=
eval₂_C _ _ a

lemma sum_to_iter_Xl (b : β) : sum_to_iter α β γ (X (sum.inl b)) = X b :=
eval₂_X _ _ (sum.inl b)

lemma sum_to_iter_Xr (c : γ) : sum_to_iter α β γ (X (sum.inr c)) = C (X c) :=
eval₂_X _ _ (sum.inr c)

/--
The function from multivariable polynomials in one type,
with coefficents in multivariable polynomials in another type,
to multivariable polynomials in the sum of the two types.

See `sum_ring_equiv` for the ring isomorphism.
-/
def iter_to_sum : mv_polynomial β (mv_polynomial γ α) → mv_polynomial (β ⊕ γ) α :=
eval₂ (eval₂ C (X ∘ sum.inr)) (X ∘ sum.inl)

instance is_semiring_hom_iter_to_sum : is_semiring_hom (iter_to_sum α β γ) :=
eval₂.is_semiring_hom _ _

lemma iter_to_sum_C_C (a : α) : iter_to_sum α β γ (C (C a)) = C a :=
eq.trans (eval₂_C _ _ (C a)) (eval₂_C _ _ _)

lemma iter_to_sum_X (b : β) : iter_to_sum α β γ (X b) = X (sum.inl b) :=
eval₂_X _ _ _

lemma iter_to_sum_C_X (c : γ) : iter_to_sum α β γ (C (X c)) = X (sum.inr c) :=
eq.trans (eval₂_C _ _ (X c)) (eval₂_X _ _ _)

/-- A helper function for `sum_ring_equiv`. -/
def mv_polynomial_equiv_mv_polynomial [comm_semiring δ]
  (f : mv_polynomial β α → mv_polynomial γ δ) (hf : is_semiring_hom f)
  (g : mv_polynomial γ δ → mv_polynomial β α) (hg : is_semiring_hom g)
  (hfgC : ∀a, f (g (C a)) = C a)
  (hfgX : ∀n, f (g (X n)) = X n)
  (hgfC : ∀a, g (f (C a)) = C a)
  (hgfX : ∀n, g (f (X n)) = X n) :
  mv_polynomial β α ≃+* mv_polynomial γ δ :=
{ to_fun    := f, inv_fun := g,
  left_inv  := is_id _ (is_semiring_hom.comp _ _) hgfC hgfX,
  right_inv := is_id _ (is_semiring_hom.comp _ _) hfgC hfgX,
  map_mul'  := hf.map_mul,
  map_add'  := hf.map_add }

/--
The ring isomorphism between multivariable polynomials in a sum of two types,
and multivariable polynomials in one of the types,
with coefficents in multivariable polynomials in the other type.
-/
def sum_ring_equiv : mv_polynomial (β ⊕ γ) α ≃+* mv_polynomial β (mv_polynomial γ α) :=
begin
  apply @mv_polynomial_equiv_mv_polynomial α (β ⊕ γ) _ _ _ _
    (sum_to_iter α β γ) _ (iter_to_sum α β γ) _,
  { assume p,
    apply hom_eq_hom _ _ _ _ _ _ p,
    apply_instance,
    { apply @is_semiring_hom.comp _ _ _ _ _ _ _ _ _ _,
      apply_instance,
      apply @is_semiring_hom.comp _ _ _ _ _ _ _ _ _ _,
      apply_instance,
      { apply_instance, },
      { apply mv_polynomial.is_semiring_hom_iter_to_sum α β γ },
      { apply mv_polynomial.is_semiring_hom_sum_to_iter α β γ } },
    { apply_instance, },
    { assume a, rw [iter_to_sum_C_C α β γ, sum_to_iter_C α β γ] },
    { assume c, rw [iter_to_sum_C_X α β γ, sum_to_iter_Xr α β γ] } },
  { assume b, rw [iter_to_sum_X α β γ, sum_to_iter_Xl α β γ] },
  { assume a, rw [sum_to_iter_C α β γ, iter_to_sum_C_C α β γ] },
  { assume n, cases n with b c,
    { rw [sum_to_iter_Xl, iter_to_sum_X] },
    { rw [sum_to_iter_Xr, iter_to_sum_C_X] } },
  { apply mv_polynomial.is_semiring_hom_sum_to_iter α β γ },
  { apply mv_polynomial.is_semiring_hom_iter_to_sum α β γ }
end

/--
The ring isomorphism between multivariable polynomials in `option β` and
polynomials with coefficients in `mv_polynomial β α`.
-/
def option_equiv_left : mv_polynomial (option β) α ≃+* polynomial (mv_polynomial β α) :=
(ring_equiv_of_equiv α $ (equiv.option_equiv_sum_punit β).trans (equiv.sum_comm _ _)).trans $
(sum_ring_equiv α _ _).trans $
punit_ring_equiv _

/--
The ring isomorphism between multivariable polynomials in `option β` and
multivariable polynomials with coefficients in polynomials.
-/
def option_equiv_right : mv_polynomial (option β) α ≃+* mv_polynomial β (polynomial α) :=
(ring_equiv_of_equiv α $ equiv.option_equiv_sum_punit.{0} β).trans $
(sum_ring_equiv α β unit).trans $
ring_equiv_congr (mv_polynomial unit α) (punit_ring_equiv α)

/--
The ring isomorphism between multivariable polynomials in `fin (n + 1)` and
polynomials over multivariable polynomials in `fin n`.
-/
def fin_succ_equiv (n : ℕ) :
  mv_polynomial (fin (n + 1)) α ≃+* polynomial (mv_polynomial (fin n) α) :=
(ring_equiv_of_equiv α (fin_succ_equiv n)).trans
  (option_equiv_left α (fin n))

end

end equiv

/-!
## Partial derivatives
-/
section pderivative

variables {R : Type} [comm_ring R]
variable {S : Type}

/-- `pderivative v p` is the partial derivative of `p` with respect to `v` -/
def pderivative (v : S) (p : mv_polynomial S R) : mv_polynomial S R :=
p.sum (λ A B, monomial (A - single v 1) (B * (A v)))

@[simp]
lemma pderivative_add {v : S} {f g : mv_polynomial S R} :
  pderivative v (f + g) = pderivative v f + pderivative v g :=
begin
  refine sum_add_index _ _,
  { simp },
  simp [add_mul],
end

@[simp]
lemma pderivative_monomial {v : S} {u : S →₀ ℕ} {a : R} :
  pderivative v (monomial u a) = monomial (u - single v 1) (a * (u v)) :=
by simp [pderivative]

@[simp]
lemma pderivative_C {v : S} {a : R} : pderivative v (C a) = 0 :=
suffices pderivative v (monomial 0 a) = 0, by simpa,
by simp

@[simp]
lemma pderivative_zero {v : S} : pderivative v (0 : mv_polynomial S R) = 0 :=
suffices pderivative v (C 0 : mv_polynomial S R) = 0, by simpa,
show pderivative v (C 0 : mv_polynomial S R) = 0, from pderivative_C

section
variables (R)

/-- `pderivative : S → mv_polynomial S R → mv_polynomial S R` as an `add_monoid_hom`  -/
def pderivative.add_monoid_hom (v : S) : mv_polynomial S R →+ mv_polynomial S R :=
{ to_fun := pderivative v,
  map_zero' := pderivative_zero,
  map_add' := λ x y, pderivative_add, }

@[simp]
lemma pderivative.add_monoid_hom_apply (v : S) (p : mv_polynomial S R) :
  (pderivative.add_monoid_hom R v) p = pderivative v p :=
rfl
end

lemma pderivative_eq_zero_of_not_mem_vars {v : S} {f : mv_polynomial S R} (h : v ∉ f.vars) :
  pderivative v f = 0 :=
begin
  change (pderivative.add_monoid_hom R v) f = 0,
  rw [f.as_sum, add_monoid_hom.map_sum],
  apply finset.sum_eq_zero,
  intros,
  simp [mem_support_not_mem_vars_zero H h],
end

lemma pderivative_monomial_single {a : R} {v : S} {n : ℕ} :
  pderivative v (monomial (single v n) a) = monomial (single v (n-1)) (a * n) :=
by simp

private lemma monomial_sub_single_one_add {v : S} {u u' : S →₀ ℕ} {r r' : R} :
  monomial (u - single v 1 + u') (r * (u v) * r') =
    monomial (u + u' - single v 1) (r * (u v) * r') :=
by by_cases h : u v = 0; simp [h, sub_single_one_add]

private lemma monomial_add_sub_single_one {v : S} {u u' : S →₀ ℕ} {r r' : R} :
  monomial (u + (u' - single v 1)) (r * (r' * (u' v))) =
    monomial (u + u' - single v 1) (r * (r' * (u' v))) :=
by by_cases h : u' v = 0; simp [h, add_sub_single_one]

lemma pderivative_monomial_mul {v : S} {u u' : S →₀ ℕ} {r r' : R} :
  pderivative v (monomial u r * monomial u' r') =
    pderivative v (monomial u r) * monomial u' r' + monomial u r * pderivative v (monomial u' r') :=
begin
  simp [monomial_sub_single_one_add, monomial_add_sub_single_one],
  congr,
  ring,
end

@[simp]
lemma pderivative_mul {v : S} {f g : mv_polynomial S R} :
  pderivative v (f * g) = pderivative v f * g + f * pderivative v g :=
begin
  apply induction_on' f,
  { apply induction_on' g,
    { intros u r u' r', exact pderivative_monomial_mul },
    { intros p q hp hq u r,
      rw [mul_add, pderivative_add, hp, hq, mul_add, pderivative_add],
      ring } },
  { intros p q hp hq,
    simp [add_mul, hp, hq],
    ring, }
end

@[simp]
lemma pderivative_C_mul {a : R} {f : mv_polynomial S R} {v : S} :
  pderivative v (C a * f) = C a * pderivative v f :=
by rw [pderivative_mul, pderivative_C, zero_mul, zero_add]

end pderivative

end mv_polynomial
