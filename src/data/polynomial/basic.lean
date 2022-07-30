/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import algebra.monoid_algebra.basic

/-!
# Theory of univariate polynomials

This file defines `polynomial R`, the type of univariate polynomials over the semiring `R`, builds
a semiring structure on it, and gives basic definitions that are expanded in other files in this
directory.

## Main definitions

* `monomial n a` is the polynomial `a X^n`. Note that `monomial n` is defined as an `R`-linear map.
* `C a` is the constant polynomial `a`. Note that `C` is defined as a ring homomorphism.
* `X` is the polynomial `X`, i.e., `monomial 1 1`.
* `p.sum f` is `∑ n in p.support, f n (p.coeff n)`, i.e., one sums the values of functions applied
  to coefficients of the polynomial `p`.
* `p.erase n` is the polynomial `p` in which one removes the `c X^n` term.

There are often two natural variants of lemmas involving sums, depending on whether one acts on the
polynomials, or on the function. The naming convention is that one adds `index` when acting on
the polynomials. For instance,
* `sum_add_index` states that `(p + q).sum f = p.sum f + q.sum f`;
* `sum_add` states that `p.sum (λ n x, f n x + g n x) = p.sum f + p.sum g`.
* Notation to refer to `polynomial R`, as `R[X]` or `R[t]`.

## Implementation

Polynomials are defined using `add_monoid_algebra R ℕ`, where `R` is a semiring.
The variable `X` commutes with every polynomial `p`: lemma `X_mul` proves the identity
`X * p` = `p * X`.  The relationship to `add_monoid_algebra R ℕ` is through a structure
to make polynomials irreducible from the point of view of the kernel. Most operations
are irreducible since Lean can not compute anyway with `add_monoid_algebra`. There are two
exceptions that we make semireducible:
* The zero polynomial, so that its coefficients are definitionally equal to `0`.
* The scalar action, to permit typeclass search to unfold it to resolve potential instance
  diamonds.

The raw implementation of the equivalence between `polynomial R` and `add_monoid_algebra R ℕ` is
done through `of_finsupp` and `to_finsupp` (or, equivalently, `rcases p` when `p` is a polynomial
gives an element `q` of `add_monoid_algebra R ℕ`, and conversely `⟨q⟩` gives back `p`). The
equivalence is also registered as a ring equiv in `polynomial.to_finsupp_iso`. These should
in general not be used once the basic API for polynomials is constructed.
-/

noncomputable theory

/-- `polynomial R` is the type of univariate polynomials over `R`.

Polynomials should be seen as (semi-)rings with the additional constructor `X`.
The embedding from `R` is called `C`. -/
abbreviation polynomial (R : Type*) [semiring R] := add_monoid_algebra R ℕ

localized "notation R`[X]`:9000 := polynomial R" in polynomial
open finsupp add_monoid_algebra
open_locale big_operators polynomial

namespace polynomial
universes u
variables {R : Type u} {a b : R} {m n : ℕ}

section semiring
variables [semiring R] {p q : R[X]}

lemma _root_.is_smul_regular.polynomial {S : Type*} [monoid S] [distrib_mul_action S R] {a : S}
  (ha : is_smul_regular R a) : is_smul_regular R[X] a
| x y h := ha.finsupp h

/-- `monomial s a` is the monomial `a * X^s` -/
def monomial (n : ℕ) : R →ₗ[R] R[X] :=
{ to_fun := single n,
  map_add' := by simp,
  map_smul' := by simp }

lemma monomial_def (n : ℕ) (r : R) : monomial n r = single n r := rfl

@[simp]
lemma monomial_zero_right (n : ℕ) :
  monomial n (0 : R) = 0 :=
(monomial n).map_zero

-- This is not a `simp` lemma as `monomial_zero_left` is more general.
lemma monomial_zero_one : monomial 0 (1 : R) = 1 := rfl

-- TODO: can't we just delete this one?
lemma monomial_add (n : ℕ) (r s : R) :
  monomial n (r + s) = monomial n r + monomial n s :=
map_add _ _ _

lemma monomial_mul_monomial (n m : ℕ) (r s : R) :
  monomial n r * monomial m s = monomial (n + m) (r * s) :=
by simp only [monomial_def, single_mul_single]

@[simp]
lemma monomial_pow (n : ℕ) (r : R) (k : ℕ) :
  (monomial n r)^k = monomial (n*k) (r^k) :=
begin
  induction k with k ih,
  { simp [pow_zero, monomial_zero_one], },
  { rw [pow_succ, ih, monomial_mul_monomial, nat.mul_succ, pow_succ, add_comm], },
end

lemma smul_monomial {S} [monoid S] [distrib_mul_action S R] (a : S) (n : ℕ) (b : R) :
  a • monomial n b = monomial n (a • b) :=
smul_single a n b

lemma monomial_injective (n : ℕ) :
  function.injective (monomial n : R → R[X]) :=
single_injective n

@[simp] lemma monomial_eq_zero_iff (t : R) (n : ℕ) :
  monomial n t = 0 ↔ t = 0 :=
linear_map.map_eq_zero_iff _ (polynomial.monomial_injective n)

lemma support_add : (p + q).support ⊆ p.support ∪ q.support :=
finsupp.support_add

/--
`C a` is the constant polynomial `a`.
`C` is provided as a ring homomorphism.
-/
def C : R →+* R[X] :=
single_zero_ring_hom

@[simp] lemma monomial_zero_left (a : R) : monomial 0 a = C a := rfl

lemma C_0 : C (0 : R) = 0 := by simp

lemma C_1 : C (1 : R) = 1 := rfl

lemma C_mul : C (a * b) = C a * C b := C.map_mul a b

lemma C_add : C (a + b) = C a + C b := C.map_add a b

@[simp] lemma smul_C {S} [monoid S] [distrib_mul_action S R] (s : S) (r : R) :
  s • C r = C (s • r) :=
smul_monomial _ _ r

@[simp] lemma C_bit0 : C (bit0 a) = bit0 (C a) := C_add

@[simp] lemma C_bit1 : C (bit1 a) = bit1 (C a) := by simp [bit1, C_bit0]

lemma C_pow : C (a ^ n) = C a ^ n := map_pow _ _ _

@[simp]
lemma C_eq_nat_cast (n : ℕ) : C (n : R) = (n : R[X]) :=
map_nat_cast C n

@[simp] lemma C_mul_monomial : C a * monomial n b = monomial n (a * b) :=
by simp only [←monomial_zero_left, monomial_mul_monomial, zero_add]

@[simp] lemma monomial_mul_C : monomial n a * C b = monomial n (a * b) :=
by simp only [←monomial_zero_left, monomial_mul_monomial, add_zero]

/-- `X` is the polynomial variable (aka indeterminate). -/
def X : R[X] := monomial 1 1

lemma monomial_one_one_eq_X : monomial 1 (1 : R) = X := rfl

lemma monomial_one_right_eq_X_pow (n : ℕ) : monomial n (1 : R) = X^n :=
begin
  induction n with n ih,
  { simp [monomial_zero_one], },
  { rw [pow_succ, ←ih, ←monomial_one_one_eq_X, monomial_mul_monomial, add_comm, one_mul], }
end

/-- `X` commutes with everything, even when the coefficients are noncommutative. -/
lemma X_mul : X * p = p * X :=
begin
  simp only [X, linear_map.coe_mk],
  ext,
  simp [add_monoid_algebra.mul_apply, monomial_def, sum_single_index, add_comm],
end

lemma X_pow_mul {n : ℕ} : X^n * p = p * X^n :=
begin
  induction n with n ih,
  { simp, },
  { conv_lhs { rw pow_succ', },
    rw [mul_assoc, X_mul, ←mul_assoc, ih, mul_assoc, ←pow_succ'], }
end

/-- Prefer putting constants to the left of `X`.

This lemma is the loop-avoiding `simp` version of `polynomial.X_mul`. -/
@[simp] lemma X_mul_C (r : R) : X * C r = C r * X :=
X_mul

/-- Prefer putting constants to the left of `X ^ n`.

This lemma is the loop-avoiding `simp` version of `X_pow_mul`. -/
@[simp] lemma X_pow_mul_C (r : R) (n : ℕ) : X^n * C r = C r * X^n :=
X_pow_mul

lemma X_pow_mul_assoc {n : ℕ} : (p * X^n) * q = (p * q) * X^n :=
by rw [mul_assoc, X_pow_mul, ←mul_assoc]

/-- Prefer putting constants to the left of `X ^ n`.

This lemma is the loop-avoiding `simp` version of `X_pow_mul_assoc`. -/
@[simp] lemma X_pow_mul_assoc_C {n : ℕ} (r : R) : (p * X^n) * C r = p * C r * X^n :=
X_pow_mul_assoc

lemma commute_X (p : R[X]) : commute X p := X_mul

lemma commute_X_pow (p : R[X]) (n : ℕ) : commute (X ^ n) p := X_pow_mul

@[simp]
lemma monomial_mul_X (n : ℕ) (r : R) : monomial n r * X = monomial (n+1) r :=
by erw [monomial_mul_monomial, mul_one]

@[simp]
lemma monomial_mul_X_pow (n : ℕ) (r : R) (k : ℕ) : monomial n r * X^k = monomial (n+k) r :=
begin
  induction k with k ih,
  { simp, },
  { simp [ih, pow_succ', ←mul_assoc, add_assoc], },
end

@[simp]
lemma X_mul_monomial (n : ℕ) (r : R) : X * monomial n r = monomial (n+1) r :=
by rw [X_mul, monomial_mul_X]

@[simp]
lemma X_pow_mul_monomial (k n : ℕ) (r : R) : X^k * monomial n r = monomial (n+k) r :=
by rw [X_pow_mul, monomial_mul_X_pow]

/-- `coeff p n` (often denoted `p.coeff n`) is the coefficient of `X^n` in `p`. -/
def coeff : R[X] → ℕ → R
| p := p

lemma coeff_def : p.coeff = p := rfl

lemma coeff_monomial : coeff (monomial n a) m = if n = m then a else 0 :=
finsupp.single_apply

@[simp] lemma coeff_zero (n : ℕ) : coeff (0 : R[X]) n = 0 := rfl

@[simp] lemma coeff_one_zero : coeff (1 : R[X]) 0 = 1 :=
by { rw [← monomial_zero_one, coeff_monomial], simp }

@[simp] lemma coeff_X_one : coeff (X : R[X]) 1 = 1 := coeff_monomial

@[simp] lemma coeff_X_zero : coeff (X : R[X]) 0 = 0 := coeff_monomial

@[simp] lemma coeff_monomial_succ : coeff (monomial (n+1) a) 0 = 0 :=
by simp [coeff_monomial]

lemma coeff_X : coeff (X : R[X]) n = if 1 = n then 1 else 0 := coeff_monomial

lemma coeff_X_of_ne_one {n : ℕ} (hn : n ≠ 1) : coeff (X : R[X]) n = 0 :=
by rw [coeff_X, if_neg hn.symm]

@[simp] lemma mem_support_iff : n ∈ p.support ↔ p.coeff n ≠ 0 :=
by simp [coeff_def]

lemma not_mem_support_iff : n ∉ p.support ↔ p.coeff n = 0 :=
by simp

lemma coeff_C : coeff (C a) n = ite (n = 0) a 0 :=
by { convert coeff_monomial using 2, simp [eq_comm], }

@[simp] lemma coeff_C_zero : coeff (C a) 0 = a := coeff_monomial

lemma coeff_C_ne_zero (h : n ≠ 0) : (C a).coeff n = 0 :=
by rw [coeff_C, if_neg h]

theorem nontrivial.of_polynomial_ne (h : p ≠ q) : nontrivial R :=
nontrivial_of_ne 0 1 $ λ h01, h $
  by rw [← mul_one p, ← mul_one q, ← C_1, ← h01, C_0, mul_zero, mul_zero]

lemma monomial_eq_C_mul_X : ∀{n}, monomial n a = C a * X^n
| 0     := (mul_one _).symm
| (n+1) :=
  calc monomial (n + 1) a = monomial n a * X : by { rw [X, monomial_mul_monomial, mul_one], }
    ... = (C a * X^n) * X : by rw [monomial_eq_C_mul_X]
    ... = C a * X^(n+1) : by simp only [pow_add, mul_assoc, pow_one]

@[simp] lemma C_inj : C a = C b ↔ a = b :=
⟨λ h, coeff_C_zero.symm.trans (h.symm ▸ coeff_C_zero), congr_arg C⟩

@[simp] lemma C_eq_zero : C a = 0 ↔ a = 0 :=
calc C a = 0 ↔ C a = C 0 : by rw C_0
         ... ↔ a = 0 : C_inj

theorem ext_iff {p q : R[X]} : p = q ↔ ∀ n, coeff p n = coeff q n :=
finsupp.ext_iff

@[ext] lemma ext {p q : R[X]} : (∀ n, coeff p n = coeff q n) → p = q :=
ext_iff.2

/-- Monomials generate the additive monoid of polynomials. -/
lemma add_submonoid_closure_set_of_eq_monomial :
  add_submonoid.closure {p : R[X] | ∃ n a, p = monomial n a} = ⊤ :=
finsupp.add_closure_set_of_eq_single

lemma add_hom_ext {M : Type*} [add_monoid M] {f g : R[X] →+ M}
  (h : ∀ n a, f (monomial n a) = g (monomial n a)) :
  f = g :=
add_monoid_hom.eq_of_eq_on_mdense add_submonoid_closure_set_of_eq_monomial $
  by { rintro p ⟨n, a, rfl⟩, exact h n a }

@[ext] lemma add_hom_ext' {M : Type*} [add_monoid M] {f g : R[X] →+ M}
  (h : ∀ n, f.comp (monomial n).to_add_monoid_hom = g.comp (monomial n).to_add_monoid_hom) :
  f = g :=
add_hom_ext (λ n, add_monoid_hom.congr_fun (h n))

@[ext] lemma lhom_ext' {M : Type*} [add_comm_monoid M] [module R M] {f g : R[X] →ₗ[R] M}
  (h : ∀ n, f.comp (monomial n) = g.comp (monomial n)) :
  f = g :=
linear_map.to_add_monoid_hom_injective $ add_hom_ext $ λ n, linear_map.congr_fun (h n)

-- this has the same content as the subsingleton
lemma eq_zero_of_eq_zero (h : (0 : R) = (1 : R)) (p : R[X]) : p = 0 :=
by rw [←one_smul R p, ←h, zero_smul]

section fewnomials

lemma support_monomial (n) {a : R} (H : a ≠ 0) : (monomial n a).support = singleton n :=
finsupp.support_single_ne_zero _ H

lemma support_monomial' (n) (a : R) : (monomial n a).support ⊆ singleton n :=
finsupp.support_single_subset

lemma support_C_mul_X_pow (n : ℕ) {c : R} (h : c ≠ 0) : (C c * X ^ n).support = singleton n :=
by rw [←monomial_eq_C_mul_X, support_monomial n h]

lemma support_C_mul_X_pow' (n : ℕ) (c : R) : (C c * X ^ n).support ⊆ singleton n :=
begin
  rw ← monomial_eq_C_mul_X,
  exact support_monomial' n c,
end

open finset

lemma support_binomial' (k m : ℕ) (x y : R) : (C x * X ^ k + C y * X ^ m).support ⊆ {k, m} :=
support_add.trans (union_subset ((support_C_mul_X_pow' k x).trans
  (singleton_subset_iff.mpr (mem_insert_self k {m}))) ((support_C_mul_X_pow' m y).trans
  (singleton_subset_iff.mpr (mem_insert_of_mem (mem_singleton_self m)))))

lemma support_trinomial' (k m n : ℕ) (x y z : R) :
  (C x * X ^ k + C y * X ^ m + C z * X ^ n).support ⊆ {k, m, n} :=
support_add.trans (union_subset (support_add.trans (union_subset ((support_C_mul_X_pow' k x).trans
  (singleton_subset_iff.mpr (mem_insert_self k {m, n}))) ((support_C_mul_X_pow' m y).trans
  (singleton_subset_iff.mpr (mem_insert_of_mem (mem_insert_self m {n}))))))
  ((support_C_mul_X_pow' n z).trans (singleton_subset_iff.mpr
  (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self n))))))

end fewnomials

lemma X_pow_eq_monomial (n) : X ^ n = monomial n (1:R) :=
begin
  induction n with n hn,
  { rw [pow_zero, monomial_zero_one] },
  { rw [pow_succ', hn, X, monomial_mul_monomial, one_mul] },
end

lemma monomial_eq_smul_X {n} : monomial n (a : R) = a • X^n :=
calc monomial n a = monomial n (a * 1) : by simp
  ... = a • monomial n 1 : by rw [smul_monomial, smul_eq_mul]
  ... = a • X^n  : by rw X_pow_eq_monomial

lemma support_X_pow (H : ¬ (1:R) = 0) (n : ℕ) : (X^n : R[X]).support = singleton n :=
begin
  convert support_monomial n H,
  exact X_pow_eq_monomial n,
end

lemma support_X_empty (H : (1:R)=0) : (X : R[X]).support = ∅ :=
begin
  rw [X, H, monomial_zero_right, support_zero],
end

lemma support_X (H : ¬ (1 : R) = 0) : (X : R[X]).support = singleton 1 :=
begin
  rw [← pow_one X, support_X_pow H 1],
end

lemma monomial_left_inj {a : R} (ha : a ≠ 0) {i j : ℕ} : (monomial i a) = (monomial j a) ↔ i = j :=
finsupp.single_left_inj ha

lemma binomial_eq_binomial {k l m n : ℕ} {u v : R} (hu : u ≠ 0) (hv : v ≠ 0) :
  C u * X ^ k + C v * X ^ l = C u * X ^ m + C v * X ^ n ↔
  (k = m ∧ l = n) ∨ (u = v ∧ k = n ∧ l = m) ∨ (u + v = 0 ∧ k = l ∧ m = n) :=
begin
  simp_rw [←monomial_eq_C_mul_X],
  exact finsupp.single_add_single_eq_single_add_single hu hv,
end

lemma nat_cast_mul (n : ℕ) (p : R[X]) : (n : R[X]) * p = n • p :=
(nsmul_eq_mul _ _).symm

/-- Summing the values of a function applied to the coefficients of a polynomial -/
def sum {S : Type*} [add_comm_monoid S] (p : R[X]) (f : ℕ → R → S) : S :=
∑ n in p.support, f n (p.coeff n)

lemma sum_def {S : Type*} [add_comm_monoid S] (p : R[X]) (f : ℕ → R → S) :
  p.sum f = ∑ n in p.support, f n (p.coeff n) := rfl

lemma sum_eq_of_subset {S : Type*} [add_comm_monoid S] (p : R[X])
  (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0) (s : finset ℕ) (hs : p.support ⊆ s) :
  p.sum f = ∑ n in s, f n (p.coeff n) :=
begin
  apply finset.sum_subset hs (λ n hn h'n, _),
  rw not_mem_support_iff at h'n,
  simp [h'n, hf]
end

/-- Expressing the product of two polynomials as a double sum. -/
lemma mul_eq_sum_sum :
  p * q = ∑ i in p.support, q.sum (λ j a, (monomial (i + j)) (p.coeff i * a)) := rfl

@[simp] lemma sum_zero_index {S : Type*} [add_comm_monoid S] (f : ℕ → R → S) :
  (0 : R[X]).sum f = 0 :=
by simp [sum]

@[simp] lemma sum_monomial_index {S : Type*} [add_comm_monoid S]
  (n : ℕ) (a : R) (f : ℕ → R → S) (hf : f n 0 = 0) :
  (monomial n a : R[X]).sum f = f n a :=
begin
  by_cases h : a = 0,
  { simp [h, hf] },
  { simp [sum, support_monomial, h, coeff_monomial] }
end

@[simp] lemma sum_C_index {a} {β} [add_comm_monoid β] {f : ℕ → R → β} (h : f 0 0 = 0) :
  (C a).sum f = f 0 a :=
sum_monomial_index 0 a f h

-- the assumption `hf` is only necessary when the ring is trivial
@[simp] lemma sum_X_index {S : Type*} [add_comm_monoid S] {f : ℕ → R → S} (hf : f 1 0 = 0) :
  (X : R[X]).sum f = f 1 1 :=
sum_monomial_index 1 1 f hf

lemma sum_add_index {S : Type*} [add_comm_monoid S] (p q : R[X])
  (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0) (h_add : ∀a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂) :
  (p + q).sum f = p.sum f + q.sum f :=
finsupp.sum_add_index' hf h_add

lemma sum_add' {S : Type*} [add_comm_monoid S] (p : R[X]) (f g : ℕ → R → S) :
  p.sum (f + g) = p.sum f + p.sum g :=
finset.sum_add_distrib

lemma sum_add {S : Type*} [add_comm_monoid S] (p : R[X]) (f g : ℕ → R → S) :
  p.sum (λ n x, f n x + g n x) = p.sum f + p.sum g :=
sum_add' _ _ _

lemma sum_smul_index {S : Type*} [add_comm_monoid S] (p : R[X]) (b : R)
  (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0) : (b • p).sum f = p.sum (λ n a, f n (b * a)) :=
finsupp.sum_smul_index hf

/-- `erase p n` is the polynomial `p` in which the `X^n` term has been erased. -/
abbreviation erase : ℕ → R[X] → R[X] := finsupp.erase

@[simp] lemma support_erase (p : R[X]) (n : ℕ) :
  support (p.erase n) = (support p).erase n :=
support_erase

lemma monomial_add_erase (p : R[X]) (n : ℕ) : monomial n (coeff p n) + p.erase n = p :=
finsupp.single_add_erase _ _

lemma coeff_erase (p : R[X]) (n i : ℕ) :
  (p.erase n).coeff i = if i = n then 0 else p.coeff i :=
by convert rfl

@[simp] lemma erase_zero (n : ℕ) : (0 : R[X]).erase n = 0 :=
by simp !

@[simp] lemma erase_monomial {n : ℕ} {a : R} : erase n (monomial n a) = 0 :=
by simp ! [monomial_def]

@[simp] lemma erase_same (p : R[X]) (n : ℕ) : coeff (p.erase n) n = 0 :=
by simp [coeff_erase]

@[simp] lemma erase_ne (p : R[X]) (n i : ℕ) (h : i ≠ n) :
  coeff (p.erase n) i = coeff p i :=
by simp [coeff_erase, h]

section update

/-- Replace the coefficient of a `p : polynomial p` at a given degree `n : ℕ`
by a given value `a : R`. If `a = 0`, this is equal to `p.erase n`
If `p.nat_degree < n` and `a ≠ 0`, this increases the degree to `n`.  -/
abbreviation update (p : R[X]) (n : ℕ) (a : R) :
  R[X] :=
finsupp.update p n a

lemma coeff_update (p : R[X]) (n : ℕ) (a : R) :
  (p.update n a).coeff = function.update p.coeff n a :=
by simp [coeff_def]

lemma coeff_update_apply (p : R[X]) (n : ℕ) (a : R) (i : ℕ) :
  (p.update n a).coeff i = if (i = n) then a else p.coeff i :=
by rw [coeff_update, function.update_apply]

@[simp] lemma coeff_update_same (p : R[X]) (n : ℕ) (a : R) :
  (p.update n a).coeff n = a :=
by rw [p.coeff_update_apply, if_pos rfl]

lemma coeff_update_ne (p : R[X]) {n : ℕ} (a : R) {i : ℕ} (h : i ≠ n) :
  (p.update n a).coeff i = p.coeff i :=
by rw [p.coeff_update_apply, if_neg h]

@[simp] lemma update_zero_eq_erase (p : R[X]) (n : ℕ) :
  p.update n 0 = p.erase n :=
by { ext, rw [coeff_update_apply, coeff_erase] }

lemma support_update (p : R[X]) (n : ℕ) (a : R) [decidable (a = 0)] :
  support (p.update n a) = if a = 0 then p.support.erase n else insert n p.support :=
by { simp only [support_update], congr }

lemma support_update_zero (p : R[X]) (n : ℕ) :
  support (p.update n 0) = p.support.erase n :=
by rw [update_zero_eq_erase, support_erase]

lemma support_update_ne_zero (p : R[X]) (n : ℕ) {a : R} (ha : a ≠ 0) :
  support (p.update n a) = insert n p.support :=
by classical; rw [support_update, if_neg ha]

end update

end semiring

section ring
variables [ring R]

@[simp] lemma coeff_neg (p : R[X]) (n : ℕ) : coeff (-p) n = -coeff p n :=
finsupp.neg_apply _ _

@[simp]
lemma coeff_sub (p q : R[X]) (n : ℕ) : coeff (p - q) n = coeff p n - coeff q n :=
finsupp.sub_apply _ _ _

@[simp] lemma monomial_neg (n : ℕ) (a : R) : monomial n (-a) = -(monomial n a) :=
by rw [eq_neg_iff_add_eq_zero, ←monomial_add, neg_add_self, monomial_zero_right]

@[simp] lemma support_neg {p : R[X]} : (-p).support = p.support :=
finsupp.support_neg _

@[simp]
lemma C_eq_int_cast (n : ℤ) : C (n : R) = n :=
(C : R →+* _).map_int_cast n

end ring

section nonzero_semiring

variables [semiring R] [nontrivial R]

lemma X_ne_zero : (X : R[X]) ≠ 0 :=
mt (congr_arg (λ p, coeff p 1)) (by simp)

end nonzero_semiring

@[simp] lemma nontrivial_iff [semiring R] : nontrivial R[X] ↔ nontrivial R :=
⟨λ h, let ⟨r, s, hrs⟩ := @exists_pair_ne _ h in nontrivial.of_polynomial_ne hrs,
  by { introI h, apply_instance }⟩

section repr
variables [semiring R]
open_locale classical

instance [has_repr R] : has_repr R[X] :=
⟨λ p, if p = 0 then "0"
  else (p.support.sort (≤)).foldr
    (λ n a, a ++ (if a = "" then "" else " + ") ++
      if n = 0
        then "C (" ++ repr (coeff p n) ++ ")"
        else if n = 1
          then if (coeff p n) = 1 then "X" else "C (" ++ repr (coeff p n) ++ ") * X"
          else if (coeff p n) = 1 then "X ^ " ++ repr n
            else "C (" ++ repr (coeff p n) ++ ") * X ^ " ++ repr n) ""⟩

end repr

end polynomial
