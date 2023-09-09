/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import algebra.big_operators.ring
import algebra.module.big_operators
import number_theory.divisors
import data.nat.squarefree
import data.nat.gcd.big_operators
import algebra.invertible
import data.nat.factorization.basic

/-!
# Arithmetic Functions and Dirichlet Convolution

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines arithmetic functions, which are functions from `ℕ` to a specified type that map 0
to 0. In the literature, they are often instead defined as functions from `ℕ+`. These arithmetic
functions are endowed with a multiplication, given by Dirichlet convolution, and pointwise addition,
to form the Dirichlet ring.

## Main Definitions
 * `arithmetic_function R` consists of functions `f : ℕ → R` such that `f 0 = 0`.
 * An arithmetic function `f` `is_multiplicative` when `x.coprime y → f (x * y) = f x * f y`.
 * The pointwise operations `pmul` and `ppow` differ from the multiplication
  and power instances on `arithmetic_function R`, which use Dirichlet multiplication.
 * `ζ` is the arithmetic function such that `ζ x = 1` for `0 < x`.
 * `σ k` is the arithmetic function such that `σ k x = ∑ y in divisors x, y ^ k` for `0 < x`.
 * `pow k` is the arithmetic function such that `pow k x = x ^ k` for `0 < x`.
 * `id` is the identity arithmetic function on `ℕ`.
 * `ω n` is the number of distinct prime factors of `n`.
 * `Ω n` is the number of prime factors of `n` counted with multiplicity.
 * `μ` is the Möbius function (spelled `moebius` in code).

## Main Results
 * Several forms of Möbius inversion:
 * `sum_eq_iff_sum_mul_moebius_eq` for functions to a `comm_ring`
 * `sum_eq_iff_sum_smul_moebius_eq` for functions to an `add_comm_group`
 * `prod_eq_iff_prod_pow_moebius_eq` for functions to a `comm_group`
 * `prod_eq_iff_prod_pow_moebius_eq_of_nonzero` for functions to a `comm_group_with_zero`

## Notation
The arithmetic functions `ζ` and `σ` have Greek letter names, which are localized notation in
the namespace `arithmetic_function`.

## Tags
arithmetic functions, dirichlet convolution, divisors

-/

open finset
open_locale big_operators

namespace nat
variable (R : Type*)

/-- An arithmetic function is a function from `ℕ` that maps 0 to 0. In the literature, they are
  often instead defined as functions from `ℕ+`. Multiplication on `arithmetic_functions` is by
  Dirichlet convolution. -/
@[derive [has_zero, inhabited]]
def arithmetic_function [has_zero R] := zero_hom ℕ R

variable {R}

namespace arithmetic_function

section has_zero
variable [has_zero R]

instance : has_coe_to_fun (arithmetic_function R) (λ _, ℕ → R) := zero_hom.has_coe_to_fun

@[simp] lemma to_fun_eq (f : arithmetic_function R) : f.to_fun = f := rfl

@[simp]
lemma map_zero {f : arithmetic_function R} : f 0 = 0 :=
zero_hom.map_zero' f

theorem coe_inj {f g : arithmetic_function R} : (f : ℕ → R) = g ↔ f = g :=
⟨λ h, zero_hom.coe_inj h, λ h, h ▸ rfl⟩

@[simp]
lemma zero_apply {x : ℕ} : (0 : arithmetic_function R) x = 0 :=
zero_hom.zero_apply x

@[ext] theorem ext ⦃f g : arithmetic_function R⦄ (h : ∀ x, f x = g x) : f = g :=
zero_hom.ext h

theorem ext_iff {f g : arithmetic_function R} : f = g ↔ ∀ x, f x = g x :=
zero_hom.ext_iff

section has_one
variable [has_one R]

instance : has_one (arithmetic_function R) := ⟨⟨λ x, ite (x = 1) 1 0, rfl⟩⟩

lemma one_apply {x : ℕ} : (1 : arithmetic_function R) x = ite (x = 1) 1 0 := rfl

@[simp] lemma one_one : (1 : arithmetic_function R) 1 = 1 := rfl

@[simp] lemma one_apply_ne {x : ℕ} (h : x ≠ 1) : (1 : arithmetic_function R) x = 0 := if_neg h

end has_one
end has_zero

instance nat_coe [add_monoid_with_one R] :
  has_coe (arithmetic_function ℕ) (arithmetic_function R) :=
⟨λ f, ⟨↑(f : ℕ → ℕ), by { transitivity ↑(f 0), refl, simp }⟩⟩

@[simp]
lemma nat_coe_nat (f : arithmetic_function ℕ) :
  (↑f : arithmetic_function ℕ) = f :=
ext $ λ _, cast_id _

@[simp]
lemma nat_coe_apply [add_monoid_with_one R] {f : arithmetic_function ℕ} {x : ℕ} :
  (f : arithmetic_function R) x = f x := rfl

instance int_coe [add_group_with_one R] :
  has_coe (arithmetic_function ℤ) (arithmetic_function R) :=
⟨λ f, ⟨↑(f : ℕ → ℤ), by { transitivity ↑(f 0), refl, simp }⟩⟩

@[simp]
lemma int_coe_int (f : arithmetic_function ℤ) :
  (↑f : arithmetic_function ℤ) = f :=
ext $ λ _, int.cast_id _

@[simp]
lemma int_coe_apply [add_group_with_one R]
  {f : arithmetic_function ℤ} {x : ℕ} :
  (f : arithmetic_function R) x = f x := rfl

@[simp]
lemma coe_coe [add_group_with_one R] {f : arithmetic_function ℕ} :
  ((f : arithmetic_function ℤ) : arithmetic_function R) = f :=
by { ext, simp, }

@[simp] lemma nat_coe_one [add_monoid_with_one R] :
  ((1 : arithmetic_function ℕ) : arithmetic_function R) = 1 :=
by { ext n, simp [one_apply] }

@[simp] lemma int_coe_one [add_group_with_one R] :
  ((1 : arithmetic_function ℤ) : arithmetic_function R) = 1 :=
by { ext n, simp [one_apply] }

section add_monoid

variable [add_monoid R]

instance : has_add (arithmetic_function R) := ⟨λ f g, ⟨λ n, f n + g n, by simp⟩⟩

@[simp]
lemma add_apply {f g : arithmetic_function R} {n : ℕ} : (f + g) n = f n + g n := rfl

instance : add_monoid (arithmetic_function R) :=
{ add_assoc := λ _ _ _, ext (λ _, add_assoc _ _ _),
  zero_add := λ _, ext (λ _, zero_add _),
  add_zero := λ _, ext (λ _, add_zero _),
  .. arithmetic_function.has_zero R,
  .. arithmetic_function.has_add }

end add_monoid

instance [add_monoid_with_one R] : add_monoid_with_one (arithmetic_function R) :=
{ nat_cast := λ n, ⟨λ x, if x = 1 then (n : R) else 0, by simp⟩,
  nat_cast_zero := by ext; simp [nat.cast],
  nat_cast_succ := λ _, by ext; by_cases x = 1; simp [nat.cast, *],
  .. arithmetic_function.add_monoid, .. arithmetic_function.has_one }

instance [add_comm_monoid R] : add_comm_monoid (arithmetic_function R) :=
{ add_comm := λ _ _, ext (λ _, add_comm _ _),
  .. arithmetic_function.add_monoid }

instance [add_group R] : add_group (arithmetic_function R) :=
{ neg := λ f, ⟨λ n, - f n, by simp⟩,
  add_left_neg := λ _, ext (λ _, add_left_neg _),
  .. arithmetic_function.add_monoid }

instance [add_comm_group R] : add_comm_group (arithmetic_function R) :=
{ .. arithmetic_function.add_comm_monoid,
  .. arithmetic_function.add_group }

section has_smul
variables {M : Type*} [has_zero R] [add_comm_monoid M] [has_smul R M]

/-- The Dirichlet convolution of two arithmetic functions `f` and `g` is another arithmetic function
  such that `(f * g) n` is the sum of `f x * g y` over all `(x,y)` such that `x * y = n`. -/
instance : has_smul (arithmetic_function R) (arithmetic_function M) :=
⟨λ f g, ⟨λ n, ∑ x in divisors_antidiagonal n, f x.fst • g x.snd, by simp⟩⟩

@[simp]
lemma smul_apply {f : arithmetic_function R} {g : arithmetic_function M} {n : ℕ} :
  (f • g) n = ∑ x in divisors_antidiagonal n, f x.fst • g x.snd := rfl

end has_smul

/-- The Dirichlet convolution of two arithmetic functions `f` and `g` is another arithmetic function
  such that `(f * g) n` is the sum of `f x * g y` over all `(x,y)` such that `x * y = n`. -/
instance [semiring R] : has_mul (arithmetic_function R) := ⟨(•)⟩

@[simp]
lemma mul_apply [semiring R] {f g : arithmetic_function R} {n : ℕ} :
  (f * g) n = ∑ x in divisors_antidiagonal n, f x.fst * g x.snd := rfl

lemma mul_apply_one [semiring R] {f g : arithmetic_function R} :
  (f * g) 1 = f 1 * g 1 :=
by simp

@[simp, norm_cast] lemma nat_coe_mul [semiring R] {f g : arithmetic_function ℕ} :
  (↑(f * g) : arithmetic_function R) = f * g :=
by { ext n, simp }

@[simp, norm_cast] lemma int_coe_mul [ring R] {f g : arithmetic_function ℤ} :
  (↑(f * g) : arithmetic_function R) = f * g :=
by { ext n, simp }

section module
variables {M : Type*} [semiring R] [add_comm_monoid M] [module R M]

lemma mul_smul' (f g : arithmetic_function R) (h : arithmetic_function M) :
  (f * g) • h = f • g • h :=
begin
  ext n,
  simp only [mul_apply, smul_apply, sum_smul, mul_smul, smul_sum, finset.sum_sigma'],
  apply finset.sum_bij,
  swap 5,
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, exact ⟨(k, l*j), (l, j)⟩ },
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H,
    simp only [finset.mem_sigma, mem_divisors_antidiagonal] at H ⊢,
    rcases H with ⟨⟨rfl, n0⟩, rfl, i0⟩,
    refine ⟨⟨(mul_assoc _ _ _).symm, n0⟩, rfl, _⟩,
    rw mul_ne_zero_iff at *,
    exact ⟨i0.2, n0.2⟩, },
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, simp only [mul_assoc] },
  { rintros ⟨⟨a,b⟩, ⟨c,d⟩⟩ ⟨⟨i,j⟩, ⟨k,l⟩⟩ H₁ H₂,
    simp only [finset.mem_sigma, mem_divisors_antidiagonal,
      and_imp, prod.mk.inj_iff, add_comm, heq_iff_eq] at H₁ H₂ ⊢,
    rintros rfl h2 rfl rfl,
    exact ⟨⟨eq.trans H₁.2.1.symm H₂.2.1, rfl⟩, rfl, rfl⟩ },
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, refine ⟨⟨(i*k, l), (i, k)⟩, _, _⟩,
    { simp only [finset.mem_sigma, mem_divisors_antidiagonal] at H ⊢,
      rcases H with ⟨⟨rfl, n0⟩, rfl, j0⟩,
      refine ⟨⟨mul_assoc _ _ _, n0⟩, rfl, _⟩,
      rw mul_ne_zero_iff at *,
      exact ⟨n0.1, j0.1⟩ },
    { simp only [true_and, mem_divisors_antidiagonal, and_true, prod.mk.inj_iff, eq_self_iff_true,
        ne.def, mem_sigma, heq_iff_eq] at H ⊢,
      rw H.2.1 } }
end

lemma one_smul' (b : arithmetic_function M) :
  (1 : arithmetic_function R) • b = b :=
begin
  ext,
  rw smul_apply,
  by_cases x0 : x = 0, {simp [x0]},
  have h : {(1,x)} ⊆ divisors_antidiagonal x := by simp [x0],
  rw ← sum_subset h, {simp},
  intros y ymem ynmem,
  have y1ne : y.fst ≠ 1,
  { intro con,
    simp only [con, mem_divisors_antidiagonal, one_mul, ne.def] at ymem,
    simp only [mem_singleton, prod.ext_iff] at ynmem,
    tauto },
  simp [y1ne],
end

end module

section semiring
variable [semiring R]

instance : monoid (arithmetic_function R) :=
{ one_mul := one_smul',
  mul_one := λ f,
  begin
    ext,
    rw mul_apply,
    by_cases x0 : x = 0, {simp [x0]},
    have h : {(x,1)} ⊆ divisors_antidiagonal x := by simp [x0],
    rw ← sum_subset h, {simp},
    intros y ymem ynmem,
    have y2ne : y.snd ≠ 1,
    { intro con,
      simp only [con, mem_divisors_antidiagonal, mul_one, ne.def] at ymem,
      simp only [mem_singleton, prod.ext_iff] at ynmem,
      tauto },
    simp [y2ne],
  end,
  mul_assoc := mul_smul',
  .. arithmetic_function.has_one,
  .. arithmetic_function.has_mul }

instance : semiring (arithmetic_function R) :=
{ zero_mul := λ f, by { ext, simp only [mul_apply, zero_mul, sum_const_zero, zero_apply] },
  mul_zero := λ f, by { ext, simp only [mul_apply, sum_const_zero, mul_zero, zero_apply] },
  left_distrib := λ a b c, by { ext, simp only [←sum_add_distrib, mul_add, mul_apply, add_apply] },
  right_distrib := λ a b c, by { ext, simp only [←sum_add_distrib, add_mul, mul_apply, add_apply] },
  .. arithmetic_function.has_zero R,
  .. arithmetic_function.has_mul,
  .. arithmetic_function.has_add,
  .. arithmetic_function.add_comm_monoid,
  .. arithmetic_function.add_monoid_with_one,
  .. arithmetic_function.monoid }

end semiring

instance [comm_semiring R] : comm_semiring (arithmetic_function R) :=
{ mul_comm := λ f g, by { ext,
    rw [mul_apply, ← map_swap_divisors_antidiagonal, sum_map],
    simp [mul_comm] },
  .. arithmetic_function.semiring }

instance [comm_ring R] : comm_ring (arithmetic_function R) :=
{ .. arithmetic_function.add_comm_group,
  .. arithmetic_function.comm_semiring }

instance {M : Type*} [semiring R] [add_comm_monoid M] [module R M] :
  module (arithmetic_function R) (arithmetic_function M) :=
{ one_smul := one_smul',
  mul_smul := mul_smul',
  smul_add := λ r x y, by { ext, simp only [sum_add_distrib, smul_add, smul_apply, add_apply] },
  smul_zero := λ r, by { ext, simp only [smul_apply, sum_const_zero, smul_zero, zero_apply] },
  add_smul := λ r s x, by { ext, simp only [add_smul, sum_add_distrib, smul_apply, add_apply] },
  zero_smul := λ r, by { ext, simp only [smul_apply, sum_const_zero, zero_smul, zero_apply] }, }

section zeta

/-- `ζ 0 = 0`, otherwise `ζ x = 1`. The Dirichlet Series is the Riemann ζ.  -/
def zeta : arithmetic_function ℕ :=
⟨λ x, ite (x = 0) 0 1, rfl⟩

localized "notation (name := arithmetic_function.zeta)
  `ζ` := nat.arithmetic_function.zeta" in arithmetic_function

@[simp]
lemma zeta_apply {x : ℕ} : ζ x = if (x = 0) then 0 else 1 := rfl

lemma zeta_apply_ne {x : ℕ} (h : x ≠ 0) : ζ x = 1 := if_neg h

@[simp] theorem coe_zeta_smul_apply {M} [semiring R] [add_comm_monoid M] [module R M]
  {f : arithmetic_function M} {x : ℕ} :
  ((↑ζ : arithmetic_function R) • f) x = ∑ i in divisors x, f i :=
begin
  rw smul_apply,
  transitivity ∑ i in divisors_antidiagonal x, f i.snd,
  { refine sum_congr rfl (λ i hi, _),
    rcases mem_divisors_antidiagonal.1 hi with ⟨rfl, h⟩,
    rw [nat_coe_apply, zeta_apply_ne (left_ne_zero_of_mul h), cast_one, one_smul] },
  { rw [← map_div_left_divisors, sum_map, function.embedding.coe_fn_mk] }
end

@[simp]
theorem coe_zeta_mul_apply [semiring R] {f : arithmetic_function R} {x : ℕ} :
  (↑ζ * f) x = ∑ i in divisors x, f i :=
coe_zeta_smul_apply

@[simp]
theorem coe_mul_zeta_apply [semiring R] {f : arithmetic_function R} {x : ℕ} :
  (f * ζ) x = ∑ i in divisors x, f i :=
begin
  rw mul_apply,
  transitivity ∑ i in divisors_antidiagonal x, f i.1,
  { refine sum_congr rfl (λ i hi, _),
    rcases mem_divisors_antidiagonal.1 hi with ⟨rfl, h⟩,
    rw [nat_coe_apply, zeta_apply_ne (right_ne_zero_of_mul h), cast_one, mul_one] },
  { rw [← map_div_right_divisors, sum_map, function.embedding.coe_fn_mk] }
end

theorem zeta_mul_apply {f : arithmetic_function ℕ} {x : ℕ} :
  (ζ * f) x = ∑ i in divisors x, f i :=
by rw [← nat_coe_nat ζ, coe_zeta_mul_apply]

theorem mul_zeta_apply {f : arithmetic_function ℕ} {x : ℕ} :
  (f * ζ) x = ∑ i in divisors x, f i :=
by rw [← nat_coe_nat ζ, coe_mul_zeta_apply]

end zeta

open_locale arithmetic_function

section pmul

/-- This is the pointwise product of `arithmetic_function`s. -/
def pmul [mul_zero_class R] (f g : arithmetic_function R) :
  arithmetic_function R :=
⟨λ x, f x * g x, by simp⟩

@[simp]
lemma pmul_apply [mul_zero_class R] {f g : arithmetic_function R} {x : ℕ} :
  f.pmul g x = f x * g x := rfl

lemma pmul_comm [comm_monoid_with_zero R] (f g : arithmetic_function R) :
  f.pmul g = g.pmul f :=
by { ext, simp [mul_comm] }

section non_assoc_semiring
variable [non_assoc_semiring R]

@[simp]
lemma pmul_zeta (f : arithmetic_function R) : f.pmul ↑ζ = f :=
begin
  ext x,
  cases x;
  simp [nat.succ_ne_zero],
end

@[simp]
lemma zeta_pmul (f : arithmetic_function R) : (ζ : arithmetic_function R).pmul f = f :=
begin
  ext x,
  cases x;
  simp [nat.succ_ne_zero],
end

end non_assoc_semiring

variables [semiring R]

/-- This is the pointwise power of `arithmetic_function`s. -/
def ppow (f : arithmetic_function R) (k : ℕ) :
  arithmetic_function R :=
if h0 : k = 0 then ζ else ⟨λ x, (f x) ^ k,
  by { rw [map_zero], exact zero_pow (nat.pos_of_ne_zero h0) }⟩

@[simp]
lemma ppow_zero {f : arithmetic_function R} : f.ppow 0 = ζ :=
by rw [ppow, dif_pos rfl]

@[simp]
lemma ppow_apply {f : arithmetic_function R} {k x : ℕ} (kpos : 0 < k) :
  f.ppow k x = (f x) ^ k :=
by { rw [ppow, dif_neg (ne_of_gt kpos)], refl }

lemma ppow_succ {f : arithmetic_function R} {k : ℕ} :
  f.ppow (k + 1) = f.pmul (f.ppow k) :=
begin
  ext x,
  rw [ppow_apply (nat.succ_pos k), pow_succ],
  induction k; simp,
end

lemma ppow_succ' {f : arithmetic_function R} {k : ℕ} {kpos : 0 < k} :
  f.ppow (k + 1) = (f.ppow k).pmul f :=
begin
  ext x,
  rw [ppow_apply (nat.succ_pos k), pow_succ'],
  induction k; simp,
end

end pmul

/-- Multiplicative functions -/
def is_multiplicative [monoid_with_zero R] (f : arithmetic_function R) : Prop :=
f 1 = 1 ∧ (∀ {m n : ℕ}, m.coprime n → f (m * n) = f m * f n)

namespace is_multiplicative

section monoid_with_zero
variable [monoid_with_zero R]

@[simp]
lemma map_one {f : arithmetic_function R} (h : f.is_multiplicative) : f 1 = 1 :=
h.1

@[simp]
lemma map_mul_of_coprime {f : arithmetic_function R} (hf : f.is_multiplicative)
  {m n : ℕ} (h : m.coprime n) : f (m * n) = f m * f n :=
hf.2 h

end monoid_with_zero

lemma map_prod {ι : Type*} [comm_monoid_with_zero R] (g : ι → ℕ) {f : nat.arithmetic_function R}
  (hf : f.is_multiplicative) (s : finset ι) (hs : (s : set ι).pairwise (coprime on g)):
  f (∏ i in s, g i) = ∏ i in s, f (g i) :=
begin
  classical,
  induction s using finset.induction_on with a s has ih hs,
  { simp [hf] },
  rw [coe_insert, set.pairwise_insert_of_symmetric (coprime.symmetric.comap g)] at hs,
  rw [prod_insert has, prod_insert has, hf.map_mul_of_coprime, ih hs.1],
  exact nat.coprime_prod_right (λ i hi, hs.2 _ hi (hi.ne_of_not_mem has).symm),
end

lemma nat_cast {f : arithmetic_function ℕ} [semiring R] (h : f.is_multiplicative) :
  is_multiplicative (f : arithmetic_function R) :=
⟨by simp [h], λ m n cop, by simp [cop, h]⟩

lemma int_cast {f : arithmetic_function ℤ} [ring R] (h : f.is_multiplicative) :
  is_multiplicative (f : arithmetic_function R) :=
⟨by simp [h], λ m n cop, by simp [cop, h]⟩

lemma mul [comm_semiring R] {f g : arithmetic_function R}
  (hf : f.is_multiplicative) (hg : g.is_multiplicative) :
  is_multiplicative (f * g) :=
⟨by { simp [hf, hg], }, begin
  simp only [mul_apply],
  intros m n cop,
  rw sum_mul_sum,
  symmetry,
  apply sum_bij (λ (x : (ℕ × ℕ) × ℕ × ℕ) h, (x.1.1 * x.2.1, x.1.2 * x.2.2)),
  { rintros ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ h,
    simp only [mem_divisors_antidiagonal, ne.def, mem_product] at h,
    rcases h with ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩,
    simp only [mem_divisors_antidiagonal, nat.mul_eq_zero, ne.def],
    split, {ring},
    rw nat.mul_eq_zero at *,
    apply not_or ha hb },
  { rintros ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ h,
    simp only [mem_divisors_antidiagonal, ne.def, mem_product] at h,
    rcases h with ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩,
    dsimp only,
    rw [hf.map_mul_of_coprime cop.coprime_mul_right.coprime_mul_right_right,
        hg.map_mul_of_coprime cop.coprime_mul_left.coprime_mul_left_right],
    ring, },
  { rintros ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ ⟨⟨c1, c2⟩, ⟨d1, d2⟩⟩ hab hcd h,
    simp only [mem_divisors_antidiagonal, ne.def, mem_product] at hab,
    rcases hab with ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩,
    simp only [mem_divisors_antidiagonal, ne.def, mem_product] at hcd,
    simp only [prod.mk.inj_iff] at h,
    ext; dsimp only,
    { transitivity nat.gcd (a1 * a2) (a1 * b1),
      { rw [nat.gcd_mul_left, cop.coprime_mul_left.coprime_mul_right_right.gcd_eq_one, mul_one] },
      { rw [← hcd.1.1, ← hcd.2.1] at cop,
        rw [← hcd.1.1, h.1, nat.gcd_mul_left,
            cop.coprime_mul_left.coprime_mul_right_right.gcd_eq_one, mul_one] } },
    { transitivity nat.gcd (a1 * a2) (a2 * b2),
      { rw [mul_comm, nat.gcd_mul_left, cop.coprime_mul_right.coprime_mul_left_right.gcd_eq_one,
            mul_one] },
      { rw [← hcd.1.1, ← hcd.2.1] at cop,
        rw [← hcd.1.1, h.2, mul_comm, nat.gcd_mul_left,
            cop.coprime_mul_right.coprime_mul_left_right.gcd_eq_one, mul_one] } },
    { transitivity nat.gcd (b1 * b2) (a1 * b1),
      { rw [mul_comm, nat.gcd_mul_right,
           cop.coprime_mul_right.coprime_mul_left_right.symm.gcd_eq_one, one_mul] },
      { rw [← hcd.1.1, ← hcd.2.1] at cop,
        rw [← hcd.2.1, h.1, mul_comm c1 d1, nat.gcd_mul_left,
            cop.coprime_mul_right.coprime_mul_left_right.symm.gcd_eq_one, mul_one] } },
    { transitivity nat.gcd (b1 * b2) (a2 * b2),
      { rw [nat.gcd_mul_right,
           cop.coprime_mul_left.coprime_mul_right_right.symm.gcd_eq_one, one_mul] },
      { rw [← hcd.1.1, ← hcd.2.1] at cop,
        rw [← hcd.2.1, h.2, nat.gcd_mul_right,
            cop.coprime_mul_left.coprime_mul_right_right.symm.gcd_eq_one, one_mul] } } },
  { rintros ⟨b1, b2⟩ h,
    simp only [mem_divisors_antidiagonal, ne.def, mem_product] at h,
    use ((b1.gcd m, b2.gcd m), (b1.gcd n, b2.gcd n)),
    simp only [exists_prop, prod.mk.inj_iff, ne.def, mem_product, mem_divisors_antidiagonal],
    rw [← cop.gcd_mul _, ← cop.gcd_mul _, ← h.1, nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul cop h.1,
        nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul cop.symm _],
    { rw [nat.mul_eq_zero, decidable.not_or_iff_and_not] at h, simp [h.2.1, h.2.2] },
    rw [mul_comm n m, h.1] }
end⟩

lemma pmul [comm_semiring R] {f g : arithmetic_function R}
  (hf : f.is_multiplicative) (hg : g.is_multiplicative) :
  is_multiplicative (f.pmul g) :=
⟨by { simp [hf, hg], }, λ m n cop, begin
  simp only [pmul_apply, hf.map_mul_of_coprime cop, hg.map_mul_of_coprime cop],
  ring,
end⟩

/-- For any multiplicative function `f` and any `n > 0`,
we can evaluate `f n` by evaluating `f` at `p ^ k` over the factorization of `n` -/
lemma multiplicative_factorization [comm_monoid_with_zero R] (f : arithmetic_function R)
  (hf : f.is_multiplicative) {n : ℕ} (hn : n ≠ 0) : f n = n.factorization.prod (λ p k, f (p ^ k)) :=
multiplicative_factorization f (λ _ _, hf.2) hf.1 hn

/-- A recapitulation of the definition of multiplicative that is simpler for proofs -/
lemma iff_ne_zero [monoid_with_zero R] {f : arithmetic_function R} :
  is_multiplicative f ↔
    f 1 = 1 ∧ (∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.coprime n → f (m * n) = f m * f n) :=
begin
  refine and_congr_right' (forall₂_congr (λ m n, ⟨λ h _ _, h, λ h hmn, _⟩)),
  rcases eq_or_ne m 0 with rfl | hm,
  { simp },
  rcases eq_or_ne n 0 with rfl | hn,
  { simp },
  exact h hm hn hmn,
end

/-- Two multiplicative functions `f` and `g` are equal if and only if
they agree on prime powers -/
lemma eq_iff_eq_on_prime_powers [comm_monoid_with_zero R]
  (f : arithmetic_function R) (hf : f.is_multiplicative)
  (g : arithmetic_function R) (hg : g.is_multiplicative) :
  f = g ↔ ∀ (p i : ℕ), nat.prime p → f (p ^ i) = g (p ^ i) :=
begin
  split,
  { intros h p i _, rw [h] },
  intros h,
  ext n,
  by_cases hn : n = 0,
  { rw [hn, arithmetic_function.map_zero, arithmetic_function.map_zero] },
  rw [multiplicative_factorization f hf hn, multiplicative_factorization g hg hn],
  refine finset.prod_congr rfl _,
  simp only [support_factorization, list.mem_to_finset],
  intros p hp,
  exact h p _ (nat.prime_of_mem_factors hp),
end

end is_multiplicative

section special_functions

/-- The identity on `ℕ` as an `arithmetic_function`.  -/
def id : arithmetic_function ℕ := ⟨id, rfl⟩

@[simp]
lemma id_apply {x : ℕ} : id x = x := rfl

/-- `pow k n = n ^ k`, except `pow 0 0 = 0`. -/
def pow (k : ℕ) : arithmetic_function ℕ := id.ppow k

@[simp]
lemma pow_apply {k n : ℕ} : pow k n = if (k = 0 ∧ n = 0) then 0 else n ^ k :=
begin
  cases k,
  { simp [pow] },
  simp [pow, (ne_of_lt (nat.succ_pos k)).symm],
end

lemma pow_zero_eq_zeta : pow 0 = ζ := by { ext n, simp }

/-- `σ k n` is the sum of the `k`th powers of the divisors of `n` -/
def sigma (k : ℕ) : arithmetic_function ℕ :=
⟨λ n, ∑ d in divisors n, d ^ k, by simp⟩

localized "notation (name := arithmetic_function.sigma)
  `σ` := nat.arithmetic_function.sigma" in arithmetic_function

lemma sigma_apply {k n : ℕ} : σ k n = ∑ d in divisors n, d ^ k := rfl

lemma sigma_one_apply (n : ℕ) : σ 1 n = ∑ d in divisors n, d := by simp [sigma_apply]

lemma sigma_zero_apply (n : ℕ) : σ 0 n = (divisors n).card := by simp [sigma_apply]

lemma sigma_zero_apply_prime_pow {p i : ℕ} (hp : p.prime) :
  σ 0 (p ^ i) = i + 1 :=
by rw [sigma_zero_apply, divisors_prime_pow hp, card_map, card_range]

lemma zeta_mul_pow_eq_sigma {k : ℕ} : ζ * pow k = σ k :=
begin
  ext,
  rw [sigma, zeta_mul_apply],
  apply sum_congr rfl,
  intros x hx,
  rw [pow_apply, if_neg (not_and_of_not_right _ _)],
  contrapose! hx,
  simp [hx],
end

lemma is_multiplicative_one [monoid_with_zero R] : is_multiplicative (1 : arithmetic_function R) :=
is_multiplicative.iff_ne_zero.2 ⟨by simp,
begin
  intros m n hm hn hmn,
  rcases eq_or_ne m 1 with rfl | hm',
  { simp },
  rw [one_apply_ne, one_apply_ne hm', zero_mul],
  rw [ne.def, mul_eq_one, not_and_distrib],
  exact or.inl hm'
end⟩

lemma is_multiplicative_zeta : is_multiplicative ζ :=
is_multiplicative.iff_ne_zero.2 ⟨by simp, by simp {contextual := tt}⟩

lemma is_multiplicative_id : is_multiplicative arithmetic_function.id :=
⟨rfl, λ _ _ _, rfl⟩

lemma is_multiplicative.ppow [comm_semiring R] {f : arithmetic_function R}
  (hf : f.is_multiplicative) {k : ℕ} :
  is_multiplicative (f.ppow k) :=
begin
  induction k with k hi,
  { exact is_multiplicative_zeta.nat_cast },
  { rw ppow_succ,
    apply hf.pmul hi },
end

lemma is_multiplicative_pow {k : ℕ} : is_multiplicative (pow k) :=
is_multiplicative_id.ppow

lemma is_multiplicative_sigma {k : ℕ} :
  is_multiplicative (σ k) :=
begin
  rw [← zeta_mul_pow_eq_sigma],
  apply ((is_multiplicative_zeta).mul is_multiplicative_pow)
end

/-- `Ω n` is the number of prime factors of `n`. -/
def card_factors : arithmetic_function ℕ :=
⟨λ n, n.factors.length, by simp⟩

localized "notation (name := card_factors)
  `Ω` := nat.arithmetic_function.card_factors" in arithmetic_function

lemma card_factors_apply {n : ℕ} :
  Ω n = n.factors.length := rfl

@[simp]
lemma card_factors_one : Ω 1 = 0 := by simp [card_factors]

lemma card_factors_eq_one_iff_prime {n : ℕ} :
  Ω n = 1 ↔ n.prime :=
begin
  refine ⟨λ h, _, λ h, list.length_eq_one.2 ⟨n, factors_prime h⟩⟩,
  cases n,
  { contrapose! h,
    simp },
  rcases list.length_eq_one.1 h with ⟨x, hx⟩,
  rw [← prod_factors n.succ_ne_zero, hx, list.prod_singleton],
  apply prime_of_mem_factors,
  rw [hx, list.mem_singleton]
end

lemma card_factors_mul {m n : ℕ} (m0 : m ≠ 0) (n0 : n ≠ 0) :
  Ω (m * n) = Ω m + Ω n :=
by rw [card_factors_apply, card_factors_apply, card_factors_apply, ← multiset.coe_card,
  ← factors_eq, unique_factorization_monoid.normalized_factors_mul m0 n0, factors_eq, factors_eq,
  multiset.card_add, multiset.coe_card, multiset.coe_card]

lemma card_factors_multiset_prod {s : multiset ℕ} (h0 : s.prod ≠ 0) :
  Ω s.prod = (multiset.map Ω s).sum :=
begin
  revert h0,
  apply s.induction_on, by simp,
  intros a t h h0,
  rw [multiset.prod_cons, mul_ne_zero_iff] at h0,
  simp [h0, card_factors_mul, h],
end

@[simp] lemma card_factors_apply_prime {p : ℕ} (hp : p.prime) : Ω p = 1 :=
card_factors_eq_one_iff_prime.2 hp

@[simp] lemma card_factors_apply_prime_pow {p k : ℕ} (hp : p.prime) : Ω (p ^ k) = k :=
by rw [card_factors_apply, hp.factors_pow, list.length_replicate]

/-- `ω n` is the number of distinct prime factors of `n`. -/
def card_distinct_factors : arithmetic_function ℕ :=
⟨λ n, n.factors.dedup.length, by simp⟩

localized "notation (name := card_distinct_factors)
  `ω` := nat.arithmetic_function.card_distinct_factors" in arithmetic_function

lemma card_distinct_factors_zero : ω 0 = 0 := by simp

@[simp] lemma card_distinct_factors_one : ω 1 = 0 := by simp [card_distinct_factors]

lemma card_distinct_factors_apply {n : ℕ} :
  ω n = n.factors.dedup.length := rfl

lemma card_distinct_factors_eq_card_factors_iff_squarefree {n : ℕ} (h0 : n ≠ 0) :
  ω n = Ω n ↔ squarefree n :=
begin
  rw [squarefree_iff_nodup_factors h0, card_distinct_factors_apply],
  split; intro h,
  { rw ←n.factors.dedup_sublist.eq_of_length h,
    apply list.nodup_dedup },
  { rw h.dedup,
    refl }
end

@[simp] lemma card_distinct_factors_apply_prime_pow {p k : ℕ} (hp : p.prime) (hk : k ≠ 0) :
  ω (p ^ k) = 1 :=
by rw [card_distinct_factors_apply, hp.factors_pow, list.replicate_dedup hk, list.length_singleton]

@[simp] lemma card_distinct_factors_apply_prime {p : ℕ} (hp : p.prime) : ω p = 1 :=
by rw [←pow_one p, card_distinct_factors_apply_prime_pow hp one_ne_zero]

/-- `μ` is the Möbius function. If `n` is squarefree with an even number of distinct prime factors,
  `μ n = 1`. If `n` is squarefree with an odd number of distinct prime factors, `μ n = -1`.
  If `n` is not squarefree, `μ n = 0`. -/
def moebius : arithmetic_function ℤ :=
⟨λ n, if squarefree n then (-1) ^ (card_factors n) else 0, by simp⟩

localized "notation (name := moebius)
  `μ` := nat.arithmetic_function.moebius" in arithmetic_function

@[simp]
lemma moebius_apply_of_squarefree {n : ℕ} (h : squarefree n) : μ n = (-1) ^ card_factors n :=
if_pos h

@[simp] lemma moebius_eq_zero_of_not_squarefree {n : ℕ} (h : ¬ squarefree n) : μ n = 0 := if_neg h

lemma moebius_apply_one : μ 1 = 1 := by simp

lemma moebius_ne_zero_iff_squarefree {n : ℕ} : μ n ≠ 0 ↔ squarefree n :=
begin
  split; intro h,
  { contrapose! h,
    simp [h] },
  { simp [h, pow_ne_zero] }
end

lemma moebius_ne_zero_iff_eq_or {n : ℕ} : μ n ≠ 0 ↔ μ n = 1 ∨ μ n = -1 :=
begin
  split; intro h,
  { rw moebius_ne_zero_iff_squarefree at h,
    rw moebius_apply_of_squarefree h,
    apply neg_one_pow_eq_or },
  { rcases h with h | h; simp [h] }
end

lemma moebius_apply_prime {p : ℕ} (hp : p.prime) : μ p = -1 :=
by rw [moebius_apply_of_squarefree hp.squarefree, card_factors_apply_prime hp, pow_one]

lemma moebius_apply_prime_pow {p k : ℕ} (hp : p.prime) (hk : k ≠ 0) :
  μ (p ^ k) = if k = 1 then -1 else 0 :=
begin
  split_ifs,
  { rw [h, pow_one, moebius_apply_prime hp] },
  rw [moebius_eq_zero_of_not_squarefree],
  rw [squarefree_pow_iff hp.ne_one hk, not_and_distrib],
  exact or.inr h,
end

lemma moebius_apply_is_prime_pow_not_prime {n : ℕ} (hn : is_prime_pow n) (hn' : ¬ n.prime) :
  μ n = 0 :=
begin
  obtain ⟨p, k, hp, hk, rfl⟩ := (is_prime_pow_nat_iff _).1 hn,
  rw [moebius_apply_prime_pow hp hk.ne', if_neg],
  rintro rfl,
  exact hn' (by simpa),
end

lemma is_multiplicative_moebius : is_multiplicative μ :=
begin
  rw is_multiplicative.iff_ne_zero,
  refine ⟨by simp, λ n m hn hm hnm, _⟩,
  simp only [moebius, zero_hom.coe_mk, squarefree_mul hnm, ite_and, card_factors_mul hn hm],
  rw [pow_add, mul_comm, ite_mul_zero_left, ite_mul_zero_right, mul_comm],
end

open unique_factorization_monoid

@[simp] lemma moebius_mul_coe_zeta : (μ * ζ : arithmetic_function ℤ) = 1 :=
begin
  ext n,
  refine rec_on_pos_prime_pos_coprime _ _ _ _ n,
  { intros p n hp hn,
    rw [coe_mul_zeta_apply, sum_divisors_prime_pow hp, sum_range_succ'],
    simp_rw [function.embedding.coe_fn_mk, pow_zero, moebius_apply_one,
      moebius_apply_prime_pow hp (nat.succ_ne_zero _), nat.succ_inj', sum_ite_eq', mem_range,
      if_pos hn, add_left_neg],
    rw one_apply_ne,
    rw [ne.def, pow_eq_one_iff],
    { exact hp.ne_one },
    { exact hn.ne' } },
  { rw [zero_hom.map_zero, zero_hom.map_zero] },
  { simp },
  { intros a b ha hb hab ha' hb',
    rw [is_multiplicative.map_mul_of_coprime _ hab, ha', hb',
      is_multiplicative.map_mul_of_coprime is_multiplicative_one hab],
    exact is_multiplicative_moebius.mul is_multiplicative_zeta.nat_cast }
end

@[simp] lemma coe_zeta_mul_moebius : (ζ * μ : arithmetic_function ℤ) = 1 :=
by rw [mul_comm, moebius_mul_coe_zeta]

@[simp] lemma coe_moebius_mul_coe_zeta [ring R] : (μ * ζ : arithmetic_function R) = 1 :=
by rw [←coe_coe, ←int_coe_mul, moebius_mul_coe_zeta, int_coe_one]

@[simp] lemma coe_zeta_mul_coe_moebius [ring R] : (ζ * μ : arithmetic_function R) = 1 :=
by rw [←coe_coe, ←int_coe_mul, coe_zeta_mul_moebius, int_coe_one]

section comm_ring
variable [comm_ring R]

instance : invertible (ζ : arithmetic_function R) :=
{ inv_of := μ,
  inv_of_mul_self := coe_moebius_mul_coe_zeta,
  mul_inv_of_self := coe_zeta_mul_coe_moebius}

/-- A unit in `arithmetic_function R` that evaluates to `ζ`, with inverse `μ`. -/
def zeta_unit : (arithmetic_function R)ˣ :=
⟨ζ, μ, coe_zeta_mul_coe_moebius, coe_moebius_mul_coe_zeta⟩

@[simp]
lemma coe_zeta_unit :
  ((zeta_unit : (arithmetic_function R)ˣ) : arithmetic_function R) = ζ := rfl

@[simp]
lemma inv_zeta_unit :
  ((zeta_unit⁻¹ : (arithmetic_function R)ˣ) : arithmetic_function R) = μ := rfl

end comm_ring

/-- Möbius inversion for functions to an `add_comm_group`. -/
theorem sum_eq_iff_sum_smul_moebius_eq
  [add_comm_group R] {f g : ℕ → R} :
  (∀ (n : ℕ), 0 < n → ∑ i in (n.divisors), f i = g n) ↔
    ∀ (n : ℕ), 0 < n → ∑ (x : ℕ × ℕ) in n.divisors_antidiagonal, μ x.fst • g x.snd = f n :=
begin
  let f' : arithmetic_function R := ⟨λ x, if x = 0 then 0 else f x, if_pos rfl⟩,
  let g' : arithmetic_function R := ⟨λ x, if x = 0 then 0 else g x, if_pos rfl⟩,
  transitivity (ζ : arithmetic_function ℤ) • f' = g',
  { rw ext_iff,
    apply forall_congr,
    intro n,
    cases n, { simp },
    rw coe_zeta_smul_apply,
    simp only [n.succ_ne_zero, forall_prop_of_true, succ_pos', if_false, zero_hom.coe_mk],
    rw sum_congr rfl (λ x hx, _),
    rw (if_neg (ne_of_gt (nat.pos_of_mem_divisors hx))) },
  transitivity μ • g' = f',
  { split; intro h,
    { rw [← h, ← mul_smul, moebius_mul_coe_zeta, one_smul] },
    { rw [← h, ← mul_smul, coe_zeta_mul_moebius, one_smul] } },
  { rw ext_iff,
    apply forall_congr,
    intro n,
    cases n, { simp },
    simp only [n.succ_ne_zero, forall_prop_of_true, succ_pos', smul_apply,
      if_false, zero_hom.coe_mk],
    rw sum_congr rfl (λ x hx, _),
    rw (if_neg (ne_of_gt (nat.pos_of_mem_divisors (snd_mem_divisors_of_mem_antidiagonal hx)))) },
end

/-- Möbius inversion for functions to a `ring`. -/
theorem sum_eq_iff_sum_mul_moebius_eq [ring R] {f g : ℕ → R} :
  (∀ (n : ℕ), 0 < n → ∑ i in (n.divisors), f i = g n) ↔
    ∀ (n : ℕ), 0 < n → ∑ (x : ℕ × ℕ) in n.divisors_antidiagonal, (μ x.fst : R) * g x.snd = f n :=
begin
  rw sum_eq_iff_sum_smul_moebius_eq,
  apply forall_congr,
  refine λ a, imp_congr_right (λ _, (sum_congr rfl $ λ x hx, _).congr_left),
  rw [zsmul_eq_mul],
end

/-- Möbius inversion for functions to a `comm_group`. -/
theorem prod_eq_iff_prod_pow_moebius_eq [comm_group R] {f g : ℕ → R} :
  (∀ (n : ℕ), 0 < n → ∏ i in (n.divisors), f i = g n) ↔
    ∀ (n : ℕ), 0 < n → ∏ (x : ℕ × ℕ) in n.divisors_antidiagonal, g x.snd ^ (μ x.fst) = f n :=
@sum_eq_iff_sum_smul_moebius_eq (additive R) _ _ _

/-- Möbius inversion for functions to a `comm_group_with_zero`. -/
theorem prod_eq_iff_prod_pow_moebius_eq_of_nonzero [comm_group_with_zero R] {f g : ℕ → R}
  (hf : ∀ (n : ℕ), 0 < n → f n ≠ 0) (hg : ∀ (n : ℕ), 0 < n → g n ≠ 0) :
  (∀ (n : ℕ), 0 < n → ∏ i in (n.divisors), f i = g n) ↔
    ∀ (n : ℕ), 0 < n → ∏ (x : ℕ × ℕ) in n.divisors_antidiagonal, g x.snd ^ (μ x.fst) = f n :=
begin
  refine iff.trans (iff.trans (forall_congr (λ n, _)) (@prod_eq_iff_prod_pow_moebius_eq Rˣ _
    (λ n, if h : 0 < n then units.mk0 (f n) (hf n h) else 1)
    (λ n, if h : 0 < n then units.mk0 (g n) (hg n h) else 1))) (forall_congr (λ n, _));
  refine imp_congr_right (λ hn, _),
  { dsimp,
    rw [dif_pos hn, ← units.eq_iff, ← units.coe_hom_apply, monoid_hom.map_prod, units.coe_mk0,
      prod_congr rfl _],
    intros x hx,
    rw [dif_pos (nat.pos_of_mem_divisors hx), units.coe_hom_apply, units.coe_mk0] },
  { dsimp,
    rw [dif_pos hn, ← units.eq_iff, ← units.coe_hom_apply, monoid_hom.map_prod, units.coe_mk0,
      prod_congr rfl _],
    intros x hx,
    rw [dif_pos (nat.pos_of_mem_divisors (nat.snd_mem_divisors_of_mem_antidiagonal hx)),
      units.coe_hom_apply, units.coe_zpow, units.coe_mk0] }
end

end special_functions
end arithmetic_function
end nat
