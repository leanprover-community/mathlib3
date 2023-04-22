/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import algebra.monoid_algebra.basic
import data.finset.sort

/-!
# Theory of univariate polynomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
`X * p = p * X`.  The relationship to `add_monoid_algebra R ℕ` is through a structure
to make polynomials irreducible from the point of view of the kernel. Most operations
are irreducible since Lean can not compute anyway with `add_monoid_algebra`. There are two
exceptions that we make semireducible:
* The zero polynomial, so that its coefficients are definitionally equal to `0`.
* The scalar action, to permit typeclass search to unfold it to resolve potential instance
  diamonds.

The raw implementation of the equivalence between `R[X]` and `add_monoid_algebra R ℕ` is
done through `of_finsupp` and `to_finsupp` (or, equivalently, `rcases p` when `p` is a polynomial
gives an element `q` of `add_monoid_algebra R ℕ`, and conversely `⟨q⟩` gives back `p`). The
equivalence is also registered as a ring equiv in `polynomial.to_finsupp_iso`. These should
in general not be used once the basic API for polynomials is constructed.
-/

noncomputable theory

/-- `polynomial R` is the type of univariate polynomials over `R`.

Polynomials should be seen as (semi-)rings with the additional constructor `X`.
The embedding from `R` is called `C`. -/
structure polynomial (R : Type*) [semiring R] := of_finsupp ::
(to_finsupp : add_monoid_algebra R ℕ)

localized "notation (name := polynomial) R`[X]`:9000 := polynomial R" in polynomial

open add_monoid_algebra finsupp function
open_locale big_operators polynomial

namespace polynomial
universes u
variables {R : Type u} {a b : R} {m n : ℕ}

section semiring
variables [semiring R] {p q : R[X]}

lemma forall_iff_forall_finsupp (P : R[X] → Prop) :
  (∀ p, P p) ↔ ∀ (q : add_monoid_algebra R ℕ), P ⟨q⟩ :=
⟨λ h q, h ⟨q⟩, λ h ⟨p⟩, h p⟩

lemma exists_iff_exists_finsupp (P : R[X] → Prop) :
  (∃ p, P p) ↔ ∃ (q : add_monoid_algebra R ℕ), P ⟨q⟩ :=
⟨λ ⟨⟨p⟩, hp⟩, ⟨p, hp⟩, λ ⟨q, hq⟩, ⟨⟨q⟩, hq⟩ ⟩

@[simp] lemma eta (f : R[X]) : polynomial.of_finsupp f.to_finsupp = f := by cases f; refl

/-! ### Conversions to and from `add_monoid_algebra`

Since `R[X]` is not defeq to `add_monoid_algebra R ℕ`, but instead is a structure wrapping
it, we have to copy across all the arithmetic operators manually, along with the lemmas about how
they unfold around `polynomial.of_finsupp` and `polynomial.to_finsupp`.
-/
section add_monoid_algebra

@[irreducible] private def add : R[X] → R[X] → R[X]
| ⟨a⟩ ⟨b⟩ := ⟨a + b⟩
@[irreducible] private def neg {R : Type u} [ring R] : R[X] → R[X]
| ⟨a⟩ := ⟨-a⟩
@[irreducible] private def mul : R[X] → R[X] → R[X]
| ⟨a⟩ ⟨b⟩ := ⟨a * b⟩

instance : has_zero R[X] := ⟨⟨0⟩⟩
instance : has_one R[X] := ⟨⟨1⟩⟩
instance : has_add R[X] := ⟨add⟩
instance {R : Type u} [ring R] : has_neg R[X] := ⟨neg⟩
instance {R : Type u} [ring R] : has_sub R[X] := ⟨λ a b, a + -b⟩
instance : has_mul R[X] := ⟨mul⟩
instance {S : Type*} [smul_zero_class S R] : smul_zero_class S R[X] :=
{ smul := λ r p, ⟨r • p.to_finsupp⟩,
  smul_zero := λ a, congr_arg of_finsupp (smul_zero a) }
@[priority 1]  -- to avoid a bug in the `ring` tactic
instance has_pow : has_pow R[X] ℕ := { pow := λ p n, npow_rec n p }

@[simp] lemma of_finsupp_zero : (⟨0⟩ : R[X]) = 0 := rfl
@[simp] lemma of_finsupp_one : (⟨1⟩ : R[X]) = 1 := rfl

@[simp] lemma of_finsupp_add {a b} : (⟨a + b⟩ : R[X]) = ⟨a⟩ + ⟨b⟩ := show _ = add _ _, by rw add
@[simp] lemma of_finsupp_neg {R : Type u} [ring R] {a} : (⟨-a⟩ : R[X]) = -⟨a⟩ :=
show _ = neg _, by rw neg
@[simp] lemma of_finsupp_sub {R : Type u} [ring R] {a b} : (⟨a - b⟩ : R[X]) = ⟨a⟩ - ⟨b⟩ :=
by { rw [sub_eq_add_neg, of_finsupp_add, of_finsupp_neg], refl }
@[simp] lemma of_finsupp_mul (a b) : (⟨a * b⟩ : R[X]) = ⟨a⟩ * ⟨b⟩ := show _ = mul _ _, by rw mul
@[simp] lemma of_finsupp_smul {S : Type*} [smul_zero_class S R] (a : S) (b) :
  (⟨a • b⟩ : R[X]) = (a • ⟨b⟩ : R[X]) := rfl
@[simp] lemma of_finsupp_pow (a) (n : ℕ) : (⟨a ^ n⟩ : R[X]) = ⟨a⟩ ^ n :=
begin
  change _ = npow_rec n _,
  induction n,
  { simp [npow_rec], } ,
  { simp [npow_rec, n_ih, pow_succ] }
end


@[simp] lemma to_finsupp_zero : (0 : R[X]).to_finsupp = 0 :=
rfl

@[simp] lemma to_finsupp_one : (1 : R[X]).to_finsupp = 1 := rfl

@[simp] lemma to_finsupp_add (a b : R[X]) : (a + b).to_finsupp = a.to_finsupp + b.to_finsupp :=
by { cases a, cases b, rw ←of_finsupp_add }
@[simp] lemma to_finsupp_neg {R : Type u} [ring R] (a : R[X]) : (-a).to_finsupp = -a.to_finsupp :=
by { cases a, rw ←of_finsupp_neg }
@[simp] lemma to_finsupp_sub {R : Type u} [ring R] (a b : R[X]) :
  (a - b).to_finsupp = a.to_finsupp - b.to_finsupp :=
by { rw [sub_eq_add_neg, ←to_finsupp_neg, ←to_finsupp_add], refl }
@[simp] lemma to_finsupp_mul (a b : R[X]) : (a * b).to_finsupp = a.to_finsupp * b.to_finsupp :=
by { cases a, cases b, rw ←of_finsupp_mul }
@[simp] lemma to_finsupp_smul {S : Type*} [smul_zero_class S R] (a : S) (b : R[X]) :
  (a • b).to_finsupp = a • b.to_finsupp := rfl
@[simp] lemma to_finsupp_pow (a : R[X]) (n : ℕ) : (a ^ n).to_finsupp = a.to_finsupp ^ n :=
by { cases a, rw ←of_finsupp_pow }

lemma _root_.is_smul_regular.polynomial {S : Type*} [monoid S] [distrib_mul_action S R] {a : S}
  (ha : is_smul_regular R a) : is_smul_regular R[X] a
| ⟨x⟩ ⟨y⟩ h := congr_arg _ $ ha.finsupp (polynomial.of_finsupp.inj h)

lemma to_finsupp_injective : function.injective (to_finsupp : R[X] → add_monoid_algebra _ _) :=
λ ⟨x⟩ ⟨y⟩, congr_arg _

@[simp] lemma to_finsupp_inj {a b : R[X]} : a.to_finsupp = b.to_finsupp ↔ a = b :=
to_finsupp_injective.eq_iff

@[simp] lemma to_finsupp_eq_zero {a : R[X]} : a.to_finsupp = 0 ↔ a = 0 :=
by rw [←to_finsupp_zero, to_finsupp_inj]

@[simp] lemma to_finsupp_eq_one {a : R[X]} : a.to_finsupp = 1 ↔ a = 1 :=
by rw [←to_finsupp_one, to_finsupp_inj]

/-- A more convenient spelling of `polynomial.of_finsupp.inj_eq` in terms of `iff`. -/
lemma of_finsupp_inj {a b} : (⟨a⟩ : R[X]) = ⟨b⟩ ↔ a = b :=
iff_of_eq of_finsupp.inj_eq

@[simp] lemma of_finsupp_eq_zero {a} : (⟨a⟩ : R[X]) = 0 ↔ a = 0 :=
by rw [←of_finsupp_zero, of_finsupp_inj]

@[simp] lemma of_finsupp_eq_one {a} : (⟨a⟩ : R[X]) = 1 ↔ a = 1 :=
by rw [←of_finsupp_one, of_finsupp_inj]

instance : inhabited R[X] := ⟨0⟩

instance : has_nat_cast R[X] := ⟨λ n, polynomial.of_finsupp n⟩

instance : semiring R[X] :=
function.injective.semiring to_finsupp to_finsupp_injective
  to_finsupp_zero to_finsupp_one to_finsupp_add to_finsupp_mul
  (λ _ _, to_finsupp_smul _ _) to_finsupp_pow (λ _, rfl)

instance {S} [monoid S] [distrib_mul_action S R] : distrib_mul_action S R[X] :=
function.injective.distrib_mul_action
  ⟨to_finsupp, to_finsupp_zero, to_finsupp_add⟩ to_finsupp_injective to_finsupp_smul

instance {S} [monoid S] [distrib_mul_action S R] [has_faithful_smul S R] :
  has_faithful_smul S R[X] :=
{ eq_of_smul_eq_smul := λ s₁ s₂ h, eq_of_smul_eq_smul $ λ a : ℕ →₀ R, congr_arg to_finsupp (h ⟨a⟩) }

instance {S} [semiring S] [module S R] : module S R[X] :=
function.injective.module _
  ⟨to_finsupp, to_finsupp_zero, to_finsupp_add⟩ to_finsupp_injective to_finsupp_smul

instance {S₁ S₂} [monoid S₁] [monoid S₂] [distrib_mul_action S₁ R] [distrib_mul_action S₂ R]
  [smul_comm_class S₁ S₂ R] : smul_comm_class S₁ S₂ R[X] :=
⟨by { rintros _ _ ⟨⟩, simp_rw [←of_finsupp_smul, smul_comm] }⟩

instance {S₁ S₂} [has_smul S₁ S₂] [monoid S₁] [monoid S₂] [distrib_mul_action S₁ R]
  [distrib_mul_action S₂ R] [is_scalar_tower S₁ S₂ R] : is_scalar_tower S₁ S₂ R[X] :=
⟨by { rintros _ _ ⟨⟩, simp_rw [←of_finsupp_smul, smul_assoc] }⟩

instance is_scalar_tower_right {α K : Type*} [semiring K] [distrib_smul α K]
  [is_scalar_tower α K K] : is_scalar_tower α K[X] K[X] :=
⟨by rintros _ ⟨⟩ ⟨⟩;
  simp_rw [smul_eq_mul, ← of_finsupp_smul, ← of_finsupp_mul, ← of_finsupp_smul, smul_mul_assoc]⟩

instance {S} [monoid S] [distrib_mul_action S R] [distrib_mul_action Sᵐᵒᵖ R]
  [is_central_scalar S R] : is_central_scalar S R[X] :=
⟨by { rintros _ ⟨⟩, simp_rw [←of_finsupp_smul, op_smul_eq_smul] }⟩

instance [subsingleton R] : unique R[X] :=
{ uniq := by { rintros ⟨x⟩, refine congr_arg of_finsupp _, simp },
.. polynomial.inhabited }

variable (R)

/-- Ring isomorphism between `R[X]` and `add_monoid_algebra R ℕ`. This is just an
implementation detail, but it can be useful to transfer results from `finsupp` to polynomials. -/
@[simps apply symm_apply]
def to_finsupp_iso : R[X] ≃+* add_monoid_algebra R ℕ :=
{ to_fun := to_finsupp,
  inv_fun := of_finsupp,
  left_inv := λ ⟨p⟩, rfl,
  right_inv := λ p, rfl,
  map_mul' := to_finsupp_mul,
  map_add' := to_finsupp_add }

end add_monoid_algebra

variable {R}

lemma of_finsupp_sum {ι : Type*} (s : finset ι) (f : ι → add_monoid_algebra R ℕ) :
  (⟨∑ i in s, f i⟩ : R[X]) = ∑ i in s, ⟨f i⟩ :=
map_sum (to_finsupp_iso R).symm f s

lemma to_finsupp_sum {ι : Type*} (s : finset ι) (f : ι → R[X]) :
  (∑ i in s, f i : R[X]).to_finsupp = ∑ i in s, (f i).to_finsupp :=
map_sum (to_finsupp_iso R) f s

/--
The set of all `n` such that `X^n` has a non-zero coefficient.
-/
@[simp]
def support : R[X] → finset ℕ
| ⟨p⟩ := p.support

@[simp] lemma support_of_finsupp (p) : support (⟨p⟩ : R[X]) = p.support :=
by rw support

@[simp] lemma support_zero : (0 : R[X]).support = ∅ :=
rfl

@[simp] lemma support_eq_empty : p.support = ∅ ↔ p = 0 :=
by { rcases p, simp [support] }

lemma card_support_eq_zero : p.support.card = 0 ↔ p = 0 :=
by simp

/-- `monomial s a` is the monomial `a * X^s` -/
def monomial (n : ℕ) : R →ₗ[R] R[X] :=
{ to_fun := λ t, ⟨finsupp.single n t⟩,
  map_add' := by simp,
  map_smul' := by simp [←of_finsupp_smul] }

@[simp] lemma to_finsupp_monomial (n : ℕ) (r : R) :
  (monomial n r).to_finsupp = finsupp.single n r :=
by simp [monomial]

@[simp] lemma of_finsupp_single (n : ℕ) (r : R) :
  (⟨finsupp.single n r⟩ : R[X]) = monomial n r :=
by simp [monomial]

@[simp]
lemma monomial_zero_right (n : ℕ) :
  monomial n (0 : R) = 0 :=
(monomial n).map_zero

-- This is not a `simp` lemma as `monomial_zero_left` is more general.
lemma monomial_zero_one : monomial 0 (1 : R) = 1 := rfl

-- TODO: can't we just delete this one?
lemma monomial_add (n : ℕ) (r s : R) :
  monomial n (r + s) = monomial n r + monomial n s :=
(monomial n).map_add _ _

lemma monomial_mul_monomial (n m : ℕ) (r s : R) :
  monomial n r * monomial m s = monomial (n + m) (r * s) :=
to_finsupp_injective $
  by simp only [to_finsupp_monomial, to_finsupp_mul, add_monoid_algebra.single_mul_single]

@[simp]
lemma monomial_pow (n : ℕ) (r : R) (k : ℕ) :
  (monomial n r)^k = monomial (n*k) (r^k) :=
begin
  induction k with k ih,
  { simp [pow_zero, monomial_zero_one], },
  { simp [pow_succ, ih, monomial_mul_monomial, nat.succ_eq_add_one, mul_add, add_comm] },
end

lemma smul_monomial {S} [monoid S] [distrib_mul_action S R] (a : S) (n : ℕ) (b : R) :
  a • monomial n b = monomial n (a • b) :=
to_finsupp_injective $ by simp

lemma monomial_injective (n : ℕ) :
  function.injective (monomial n : R → R[X]) :=
(to_finsupp_iso R).symm.injective.comp (single_injective n)

@[simp] lemma monomial_eq_zero_iff (t : R) (n : ℕ) :
  monomial n t = 0 ↔ t = 0 :=
linear_map.map_eq_zero_iff _ (polynomial.monomial_injective n)

lemma support_add : (p + q).support ⊆ p.support ∪ q.support :=
begin
  rcases p, rcases q,
  simp only [←of_finsupp_add, support],
  exact support_add
end

/--
`C a` is the constant polynomial `a`.
`C` is provided as a ring homomorphism.
-/
def C : R →+* R[X] :=
{ map_one' := by simp [monomial_zero_one],
  map_mul' := by simp [monomial_mul_monomial],
  map_zero' := by simp,
  .. monomial 0 }

@[simp] lemma monomial_zero_left (a : R) : monomial 0 a = C a := rfl

@[simp] lemma to_finsupp_C (a : R) : (C a).to_finsupp = single 0 a := rfl

lemma C_0 : C (0 : R) = 0 := by simp

lemma C_1 : C (1 : R) = 1 := rfl

lemma C_mul : C (a * b) = C a * C b := C.map_mul a b

lemma C_add : C (a + b) = C a + C b := C.map_add a b

@[simp] lemma smul_C {S} [monoid S] [distrib_mul_action S R] (s : S) (r : R) :
  s • C r = C (s • r) :=
smul_monomial _ _ r

@[simp] lemma C_bit0 : C (bit0 a) = bit0 (C a) := C_add

@[simp] lemma C_bit1 : C (bit1 a) = bit1 (C a) := by simp [bit1, C_bit0]

lemma C_pow : C (a ^ n) = C a ^ n := C.map_pow a n

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

@[simp] lemma to_finsupp_X : X.to_finsupp = finsupp.single 1 (1 : R) := rfl

/-- `X` commutes with everything, even when the coefficients are noncommutative. -/
lemma X_mul : X * p = p * X :=
begin
  rcases p,
  simp only [X, ←of_finsupp_single, ←of_finsupp_mul, linear_map.coe_mk],
  ext,
  simp [add_monoid_algebra.mul_apply, sum_single_index, add_comm],
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
@[simp] def coeff : R[X] → ℕ → R
| ⟨p⟩ := p

lemma coeff_injective : injective (coeff : R[X] → ℕ → R) :=
by { rintro ⟨p⟩ ⟨q⟩, simp only [coeff, fun_like.coe_fn_eq, imp_self] }

@[simp] lemma coeff_inj : p.coeff = q.coeff ↔ p = q := coeff_injective.eq_iff

lemma to_finsupp_apply (f : R[X]) (i) : f.to_finsupp i = f.coeff i := by cases f; refl

lemma coeff_monomial : coeff (monomial n a) m = if n = m then a else 0 :=
by { simp only [←of_finsupp_single, coeff, linear_map.coe_mk], rw finsupp.single_apply }

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
by { rcases p, simp }

lemma not_mem_support_iff : n ∉ p.support ↔ p.coeff n = 0 :=
by simp

lemma coeff_C : coeff (C a) n = ite (n = 0) a 0 :=
by { convert coeff_monomial using 2, simp [eq_comm], }

@[simp] lemma coeff_C_zero : coeff (C a) 0 = a := coeff_monomial

lemma coeff_C_ne_zero (h : n ≠ 0) : (C a).coeff n = 0 :=
by rw [coeff_C, if_neg h]

lemma C_mul_X_pow_eq_monomial : ∀ {n : ℕ}, C a * X ^ n = monomial n a
| 0     := mul_one _
| (n+1) := by rw [pow_succ', ←mul_assoc, C_mul_X_pow_eq_monomial, X, monomial_mul_monomial, mul_one]

@[simp] lemma to_finsupp_C_mul_X_pow (a : R) (n : ℕ) :
  (C a * X ^ n).to_finsupp = finsupp.single n a :=
by rw [C_mul_X_pow_eq_monomial, to_finsupp_monomial]

lemma C_mul_X_eq_monomial : C a * X = monomial 1 a := by rw [← C_mul_X_pow_eq_monomial, pow_one]

@[simp] lemma to_finsupp_C_mul_X (a : R) : (C a * X).to_finsupp = finsupp.single 1 a :=
by rw [C_mul_X_eq_monomial, to_finsupp_monomial]

lemma C_injective : injective (C : R → R[X]) := monomial_injective 0

@[simp] lemma C_inj : C a = C b ↔ a = b := C_injective.eq_iff
@[simp] lemma C_eq_zero : C a = 0 ↔ a = 0 := C_injective.eq_iff' (map_zero C)

lemma C_ne_zero : C a ≠ 0 ↔ a ≠ 0 := C_eq_zero.not

lemma subsingleton_iff_subsingleton :
  subsingleton R[X] ↔ subsingleton R :=
⟨@injective.subsingleton _ _ _ C_injective, by { introI, apply_instance } ⟩

theorem nontrivial.of_polynomial_ne (h : p ≠ q) : nontrivial R :=
(subsingleton_or_nontrivial R).resolve_left $ λ hI, h $ by exactI subsingleton.elim _ _

lemma forall_eq_iff_forall_eq :
  (∀ f g : R[X], f = g) ↔ (∀ a b : R, a = b) :=
by simpa only [← subsingleton_iff] using subsingleton_iff_subsingleton

theorem ext_iff {p q : R[X]} : p = q ↔ ∀ n, coeff p n = coeff q n :=
by { rcases p, rcases q, simp [coeff, finsupp.ext_iff] }

@[ext] lemma ext {p q : R[X]} : (∀ n, coeff p n = coeff q n) → p = q :=
ext_iff.2

/-- Monomials generate the additive monoid of polynomials. -/
lemma add_submonoid_closure_set_of_eq_monomial :
  add_submonoid.closure {p : R[X] | ∃ n a, p = monomial n a} = ⊤ :=
begin
  apply top_unique,
  rw [← add_submonoid.map_equiv_top (to_finsupp_iso R).symm.to_add_equiv,
    ← finsupp.add_closure_set_of_eq_single, add_monoid_hom.map_mclosure],
  refine add_submonoid.closure_mono (set.image_subset_iff.2 _),
  rintro _ ⟨n, a, rfl⟩,
  exact ⟨n, a, polynomial.of_finsupp_single _ _⟩,
end

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
by rw [←of_finsupp_single, support, finsupp.support_single_ne_zero _ H]

lemma support_monomial' (n) (a : R) : (monomial n a).support ⊆ singleton n :=
by { rw [←of_finsupp_single, support], exact finsupp.support_single_subset }

lemma support_C_mul_X {c : R} (h : c ≠ 0) : (C c * X).support = singleton 1 :=
by rw [C_mul_X_eq_monomial, support_monomial 1 h]

lemma support_C_mul_X' (c : R) : (C c * X).support ⊆ singleton 1 :=
by simpa only [C_mul_X_eq_monomial] using support_monomial' 1 c

lemma support_C_mul_X_pow (n : ℕ) {c : R} (h : c ≠ 0) : (C c * X ^ n).support = singleton n :=
by rw [C_mul_X_pow_eq_monomial, support_monomial n h]

lemma support_C_mul_X_pow' (n : ℕ) (c : R) : (C c * X ^ n).support ⊆ singleton n :=
by simpa only [C_mul_X_pow_eq_monomial] using support_monomial' n c

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

lemma X_pow_eq_monomial (n) : X ^ n = monomial n (1 : R) :=
begin
  induction n with n hn,
  { rw [pow_zero, monomial_zero_one] },
  { rw [pow_succ', hn, X, monomial_mul_monomial, one_mul] },
end

@[simp] lemma to_finsupp_X_pow (n : ℕ) : (X ^ n).to_finsupp = finsupp.single n (1 : R) :=
by rw [X_pow_eq_monomial, to_finsupp_monomial]

lemma smul_X_eq_monomial {n} : a • X ^ n = monomial n (a : R) :=
by rw [X_pow_eq_monomial, smul_monomial, smul_eq_mul, mul_one]

lemma support_X_pow (H : ¬(1 : R) = 0) (n : ℕ) : (X ^ n : R[X]).support = singleton n :=
begin
  convert support_monomial n H,
  exact X_pow_eq_monomial n,
end

lemma support_X_empty (H : (1 : R) = 0) : (X : R[X]).support = ∅ :=
by rw [X, H, monomial_zero_right, support_zero]

lemma support_X (H : ¬(1 : R) = 0) : (X : R[X]).support = singleton 1 :=
by rw [← pow_one X, support_X_pow H 1]

lemma monomial_left_inj {a : R} (ha : a ≠ 0) {i j : ℕ} : (monomial i a) = (monomial j a) ↔ i = j :=
by simp_rw [←of_finsupp_single, finsupp.single_left_inj ha]

lemma binomial_eq_binomial {k l m n : ℕ} {u v : R} (hu : u ≠ 0) (hv : v ≠ 0) :
  C u * X ^ k + C v * X ^ l = C u * X ^ m + C v * X ^ n ↔
  (k = m ∧ l = n) ∨ (u = v ∧ k = n ∧ l = m) ∨ (u + v = 0 ∧ k = l ∧ m = n) :=
begin
  simp_rw [C_mul_X_pow_eq_monomial, ←to_finsupp_inj, to_finsupp_add, to_finsupp_monomial],
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
  p * q = ∑ i in p.support, q.sum (λ j a, (monomial (i + j)) (p.coeff i * a)) :=
begin
  apply to_finsupp_injective,
  rcases p, rcases q,
  simp [support, sum, coeff, to_finsupp_sum],
  refl
end

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
begin
  rcases p, rcases q,
  simp only [←of_finsupp_add, sum, support, coeff, pi.add_apply, coe_add],
  exact finsupp.sum_add_index' hf h_add,
end

lemma sum_add' {S : Type*} [add_comm_monoid S] (p : R[X]) (f g : ℕ → R → S) :
  p.sum (f + g) = p.sum f + p.sum g :=
by simp [sum_def, finset.sum_add_distrib]

lemma sum_add {S : Type*} [add_comm_monoid S] (p : R[X]) (f g : ℕ → R → S) :
  p.sum (λ n x, f n x + g n x) = p.sum f + p.sum g :=
sum_add' _ _ _

lemma sum_smul_index {S : Type*} [add_comm_monoid S] (p : R[X]) (b : R)
  (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0) : (b • p).sum f = p.sum (λ n a, f n (b * a)) :=
begin
  rcases p,
  simpa [sum, support, coeff] using finsupp.sum_smul_index hf,
end

lemma sum_monomial_eq : ∀ p : R[X], p.sum (λ n a, monomial n a) = p
| ⟨p⟩ := (of_finsupp_sum _ _).symm.trans (congr_arg _ $ finsupp.sum_single _)

lemma sum_C_mul_X_pow_eq (p : R[X]) : p.sum (λ n a, C a * X ^ n) = p :=
by simp_rw [C_mul_X_pow_eq_monomial, sum_monomial_eq]

/-- `erase p n` is the polynomial `p` in which the `X^n` term has been erased. -/
@[irreducible] definition erase (n : ℕ) : R[X] → R[X]
| ⟨p⟩ := ⟨p.erase n⟩

@[simp] lemma to_finsupp_erase (p : R[X]) (n : ℕ) :
  to_finsupp (p.erase n) = (p.to_finsupp).erase n :=
by { rcases p, simp only [erase] }

@[simp] lemma of_finsupp_erase (p : add_monoid_algebra R ℕ) (n : ℕ) :
  (⟨p.erase n⟩ : R[X]) = (⟨p⟩ : R[X]).erase n :=
by { rcases p, simp only [erase] }

@[simp] lemma support_erase (p : R[X]) (n : ℕ) :
  support (p.erase n) = (support p).erase n :=
by { rcases p, simp only [support, erase, support_erase] }

lemma monomial_add_erase (p : R[X]) (n : ℕ) : monomial n (coeff p n) + p.erase n = p :=
to_finsupp_injective $ begin
  rcases p,
  rw [to_finsupp_add, to_finsupp_monomial, to_finsupp_erase, coeff],
  exact finsupp.single_add_erase _ _,
end

lemma coeff_erase (p : R[X]) (n i : ℕ) :
  (p.erase n).coeff i = if i = n then 0 else p.coeff i :=
begin
  rcases p,
  simp only [erase, coeff],
  convert rfl
end

@[simp] lemma erase_zero (n : ℕ) : (0 : R[X]).erase n = 0 :=
to_finsupp_injective $ by simp

@[simp] lemma erase_monomial {n : ℕ} {a : R} : erase n (monomial n a) = 0 :=
to_finsupp_injective $ by simp

@[simp] lemma erase_same (p : R[X]) (n : ℕ) : coeff (p.erase n) n = 0 :=
by simp [coeff_erase]

@[simp] lemma erase_ne (p : R[X]) (n i : ℕ) (h : i ≠ n) :
  coeff (p.erase n) i = coeff p i :=
by simp [coeff_erase, h]

section update

/-- Replace the coefficient of a `p : R[X]` at a given degree `n : ℕ`
by a given value `a : R`. If `a = 0`, this is equal to `p.erase n`
If `p.nat_degree < n` and `a ≠ 0`, this increases the degree to `n`.  -/
def update (p : R[X]) (n : ℕ) (a : R) :
  R[X] :=
polynomial.of_finsupp (p.to_finsupp.update n a)

lemma coeff_update (p : R[X]) (n : ℕ) (a : R) :
  (p.update n a).coeff = function.update p.coeff n a :=
begin
  ext,
  cases p,
  simp only [coeff, update, function.update_apply, coe_update],
end

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
by { classical, cases p, simp only [support, update, support_update], congr }

lemma support_update_zero (p : R[X]) (n : ℕ) :
  support (p.update n 0) = p.support.erase n :=
by rw [update_zero_eq_erase, support_erase]

lemma support_update_ne_zero (p : R[X]) (n : ℕ) {a : R} (ha : a ≠ 0) :
  support (p.update n a) = insert n p.support :=
by classical; rw [support_update, if_neg ha]

end update

end semiring

section comm_semiring
variables [comm_semiring R]

instance : comm_semiring R[X] :=
function.injective.comm_semiring to_finsupp to_finsupp_injective
  to_finsupp_zero to_finsupp_one to_finsupp_add to_finsupp_mul
  (λ _ _, to_finsupp_smul _ _) to_finsupp_pow (λ _, rfl)

end comm_semiring

section ring
variables [ring R]

instance : has_int_cast R[X] := ⟨λ n, of_finsupp n⟩

instance : ring R[X] :=
function.injective.ring to_finsupp to_finsupp_injective
  to_finsupp_zero to_finsupp_one to_finsupp_add to_finsupp_mul to_finsupp_neg to_finsupp_sub
  (λ _ _, to_finsupp_smul _ _) (λ _ _, to_finsupp_smul _ _) to_finsupp_pow (λ _, rfl) (λ _, rfl)

@[simp] lemma coeff_neg (p : R[X]) (n : ℕ) : coeff (-p) n = -coeff p n :=
by { rcases p, rw [←of_finsupp_neg, coeff, coeff, finsupp.neg_apply] }

@[simp]
lemma coeff_sub (p q : R[X]) (n : ℕ) : coeff (p - q) n = coeff p n - coeff q n :=
by { rcases p, rcases q, rw [←of_finsupp_sub, coeff, coeff, coeff, finsupp.sub_apply] }

@[simp] lemma monomial_neg (n : ℕ) (a : R) : monomial n (-a) = -(monomial n a) :=
by rw [eq_neg_iff_add_eq_zero, ←monomial_add, neg_add_self, monomial_zero_right]

@[simp] lemma support_neg {p : R[X]} : (-p).support = p.support :=
by { rcases p, rw [←of_finsupp_neg, support, support, finsupp.support_neg] }

@[simp] lemma C_eq_int_cast (n : ℤ) : C (n : R) = n := map_int_cast C n

end ring

instance [comm_ring R] : comm_ring R[X] :=
function.injective.comm_ring to_finsupp to_finsupp_injective
  to_finsupp_zero to_finsupp_one to_finsupp_add to_finsupp_mul to_finsupp_neg to_finsupp_sub
  (λ _ _, to_finsupp_smul _ _) (λ _ _, to_finsupp_smul _ _) to_finsupp_pow (λ _, rfl) (λ _, rfl)

section nonzero_semiring

variables [semiring R] [nontrivial R]
instance : nontrivial R[X] :=
begin
  have h : nontrivial (add_monoid_algebra R ℕ) := by apply_instance,
  rcases h.exists_pair_ne with ⟨x, y, hxy⟩,
  refine ⟨⟨⟨x⟩, ⟨y⟩, _⟩⟩,
  simp [hxy],
end

lemma X_ne_zero : (X : R[X]) ≠ 0 :=
mt (congr_arg (λ p, coeff p 1)) (by simp)

end nonzero_semiring

@[simp] lemma nontrivial_iff [semiring R] : nontrivial R[X] ↔ nontrivial R :=
⟨λ h, let ⟨r, s, hrs⟩ := @exists_pair_ne _ h in nontrivial.of_polynomial_ne hrs,
  λ h, @polynomial.nontrivial _ _ h⟩

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
