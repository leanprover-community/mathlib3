/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/

import data.finsupp order.complete_lattice algebra.ordered_group data.mv_polynomial
import algebra.order_functions
import ring_theory.ideal_operations

/-!
# Formal power series

This file defines (multivariate) formal power series
and develops the basic properties of these objects.

A formal power series is to a polynomial like an infinite sum is to a finite sum.

We provide the natural inclusion from polynomials to formal power series.

## Generalities

The file starts with setting up the (semi)ring structure on multivariate power series.

`trunc n φ` truncates a formal power series to the polynomial
that has the same coefficients as φ, for all m ≤ n, and 0 otherwise.

If the constant coefficient of a formal power series is invertible,
then this formal power series is invertible.

Formal power series over a local ring form a local ring.

## Formal power series in one variable

We prove that if the ring of coefficients is an integral domain,
then formal power series in one variable form an integral domain.

The `order` of a formal power series `φ` is the multiplicity of the variable `X` in `φ`.

If the coefficients form an integral domain, then `order` is a valuation
(`order_mul`, `order_add_ge`).

## Implementation notes

In this file we define multivariate formal power series with
variables indexed by `σ` and coefficients in `α` as
mv_power_series σ α := (σ →₀ ℕ) → α.
Unfortunately there is not yet enough API to show that they are the completion
of the ring of multivariate polynomials. However, we provide most of the infrastructure
that is needed to do this. Once I-adic completion (topological or algebraic) is available
it should not be hard to fill in the details.

Formal power series in one variable are defined as
power_series α := mv_power_series unit α.

This allows us to port a lot of proofs and properties
from the multivariate case to the single variable case.
However, it means that formal power series are indexed by (unit →₀ ℕ),
which is of course canonically isomorphic to ℕ.
We then build some glue to treat formal power series as if they are indexed by ℕ.
Occasionally this leads to proofs that are uglier than expected.

-/

noncomputable theory
local attribute [instance, priority 100] classical.prop_decidable

/-- Multivariate formal power series, where `σ` is the index set of the variables
and `α` is the coefficient ring.-/
def mv_power_series (σ : Type*) (α : Type*) := (σ →₀ ℕ) → α

namespace mv_power_series
open finsupp
variables {σ : Type*} {α : Type*}

/-- The `n`th coefficient of a multivariate formal power series.-/
def coeff (n : σ →₀ ℕ) (φ : mv_power_series σ α) := φ n

/-- Two multivariate formal power series are equal if all their coefficients are equal.-/
@[extensionality] lemma ext {φ ψ : mv_power_series σ α} (h : ∀ n, coeff n φ = coeff n ψ) :
  φ = ψ :=
funext h

/-- Two multivariate formal power series are equal
 if and only if all their coefficients are equal.-/
lemma ext_iff {φ ψ : mv_power_series σ α} :
  φ = ψ ↔ (∀ n, coeff n φ = coeff n ψ) :=
⟨λ h n, congr_arg (coeff n) h, ext⟩

section semiring
variables [semiring α]

/-- The `n`th monimial with coefficient `a` as multivariate formal power series.-/
def monomial (n : σ →₀ ℕ) (a : α) : mv_power_series σ α :=
λ m, if m = n then a else 0

lemma coeff_monomial (m n : σ →₀ ℕ) (a : α) :
  coeff m (monomial n a) = if m = n then a else 0 := rfl

@[simp] lemma coeff_monomial' (n : σ →₀ ℕ) (a : α) :
  coeff n (monomial n a) = a := if_pos rfl

/-- The constant multivariate formal power series.-/
def C (a : α) : mv_power_series σ α := monomial 0 a

lemma coeff_C (n : σ →₀ ℕ) (a : α) :
  coeff n (C a : mv_power_series σ α) = if n = 0 then a else 0 := rfl

@[simp] lemma coeff_C_zero (a : α) : coeff 0 (C a : mv_power_series σ α) = a :=
coeff_monomial' 0 a

@[simp] lemma monomial_index_zero (a : α) : (monomial 0 a : mv_power_series σ α) = C a := rfl

lemma C_eq (a : α) : (C a : mv_power_series σ α) = monomial 0 a := rfl

/-- The variables of the multivariate formal power series ring.-/
def X (s : σ) : mv_power_series σ α := monomial (single s 1) 1

lemma coeff_X (n : σ →₀ ℕ) (s : σ) :
  coeff n (X s : mv_power_series σ α) = if n = (single s 1) then 1 else 0 := rfl

lemma coeff_X_index_single (s t : σ) :
  coeff (single t 1) (X s : mv_power_series σ α) = if t = s then 1 else 0 :=
by { simp only [coeff_X, single_right_inj one_ne_zero], split_ifs; refl }

@[simp] lemma coeff_X_index_single_self (s : σ) :
  coeff (single s 1) (X s : mv_power_series σ α) = 1 :=
by rw [coeff_X_index_single, if_pos rfl]

@[simp] lemma coeff_zero_X (s : σ) : coeff 0 (X s : mv_power_series σ α) = 0 :=
by { rw [coeff_X, if_neg], intro h, exact one_ne_zero (single_eq_zero.mp h.symm) }

lemma X_eq (s : σ) : X s = monomial (single s 1) 1 := rfl

section ring_structure
variables (σ) (α) (n : σ →₀ ℕ) (φ ψ : mv_power_series σ α)

protected def zero : mv_power_series σ α := λ n, 0

instance : has_zero (mv_power_series σ α) := ⟨mv_power_series.zero σ α⟩

@[simp] lemma coeff_zero : coeff n (0 : mv_power_series σ α) = 0 := rfl

@[simp] lemma C_zero : (C 0 : mv_power_series σ α) = 0 :=
ext $ λ n, if h : n = 0 then by simp [h] else by rw [coeff_C, if_neg h, coeff_zero]

protected def one : mv_power_series σ α := C 1

instance : has_one (mv_power_series σ α) := ⟨mv_power_series.one σ α⟩

@[simp] lemma coeff_one :
  coeff n (1 : mv_power_series σ α) = if n = 0 then 1 else 0 := rfl

@[simp] lemma coeff_one_zero : coeff 0 (1 : mv_power_series σ α) = 1 :=
coeff_C_zero 1

@[simp] lemma C_one : (C 1 : mv_power_series σ α) = 1 := rfl

protected def add (φ ψ : mv_power_series σ α) : mv_power_series σ α :=
λ n, coeff n φ + coeff n ψ

instance : has_add (mv_power_series σ α) := ⟨mv_power_series.add σ α⟩

variables {σ α}

@[simp] lemma monomial_coeff_zero (n : σ →₀ ℕ) :
  (monomial n 0 : mv_power_series σ α) = 0 :=
ext $ λ m, by { rw coeff_monomial, split_ifs; refl }

@[simp] lemma coeff_add : coeff n (φ + ψ) = coeff n φ + coeff n ψ := rfl

protected lemma zero_add : (0 : mv_power_series σ α) + φ = φ := ext $ λ n, zero_add _

protected lemma add_zero : φ + 0 = φ := ext $ λ n, add_zero _

protected lemma add_comm : φ + ψ = ψ + φ := ext $ λ n, add_comm _ _

protected lemma add_assoc (φ₁ φ₂ φ₃ : mv_power_series σ α) :
  (φ₁ + φ₂) + φ₃ = φ₁ + (φ₂ + φ₃) := ext $ λ n, add_assoc _ _ _

@[simp] lemma monomial_add (n : σ →₀ ℕ) (a b : α) :
  (monomial n (a + b) : mv_power_series σ α) = monomial n a + monomial n b :=
ext $ λ m, if h : m = n then by simp [h] else by simp [coeff_monomial, if_neg h]

@[simp] lemma C_add (a b : α) : (C (a + b) : mv_power_series σ α) = C a + C b :=
monomial_add 0 a b

variables (σ α)

protected def mul (φ ψ : mv_power_series σ α) : mv_power_series σ α :=
λ n, (finsupp.antidiagonal n).support.sum (λ p, coeff p.1 φ * coeff p.2 ψ)

instance : has_mul (mv_power_series σ α) := ⟨mv_power_series.mul σ α⟩

variables {σ α}

lemma coeff_mul :
  coeff n (φ * ψ) = (finsupp.antidiagonal n).support.sum (λ p, coeff p.1 φ * coeff p.2 ψ) := rfl

@[simp] lemma C_mul (a b : α) : (C (a * b) : mv_power_series σ α) = C a * C b :=
ext $ λ n,
begin
  rw [coeff_C, coeff_mul],
  split_ifs,
  { subst n, erw [antidiagonal_zero, support_single_ne_zero, finset.sum_singleton, coeff_C_zero, coeff_C_zero], simp, },
  { rw finset.sum_eq_zero,
    rintros ⟨i,j⟩ hij,
    rw mem_antidiagonal_support at hij, rw [coeff_C, coeff_C],
    split_ifs; simp * at * }
end

protected lemma zero_mul : (0 : mv_power_series σ α) * φ = 0 :=
ext $ λ n, by simp [coeff_mul]

protected lemma mul_zero : φ * 0 = 0 :=
ext $ λ n, by simp [coeff_mul]

protected lemma one_mul : (1 : mv_power_series σ α) * φ = φ :=
ext $ λ n,
begin
  rw [coeff_mul, finset.sum_eq_single ((0 : σ →₀ ℕ), n)],
  { rw [coeff_one_zero, one_mul] },
  { rintros ⟨i,j⟩ hij h,
    suffices : i ≠ 0,
    { rw [coeff_one, if_neg this, zero_mul] },
    rw [mem_antidiagonal_support] at hij,
    rw [ne.def, prod.mk.inj_iff, not_and] at h,
    intro H, apply h H, rw [← hij, H, zero_add] },
  { intro H, exfalso, apply H,
    rw [mem_antidiagonal_support, zero_add] }
end

protected lemma mul_one : φ * 1 = φ :=
ext $ λ n,
begin
  rw [coeff_mul, finset.sum_eq_single (n, (0 : σ →₀ ℕ))],
  { rw [coeff_one_zero, mul_one] },
  { rintros ⟨i,j⟩ hij h,
    suffices : j ≠ 0,
    { rw [coeff_one, if_neg this, mul_zero] },
    rw [mem_antidiagonal_support] at hij,
    rw [ne.def, prod.mk.inj_iff, not_and] at h,
    intro H, apply h _ H, rw [← hij, H, add_zero] },
  { intro H, exfalso, apply H,
    rw [mem_antidiagonal_support, add_zero] }
end

protected lemma mul_add (φ₁ φ₂ φ₃ : mv_power_series σ α) :
  φ₁ * (φ₂ + φ₃) = φ₁ * φ₂ + φ₁ * φ₃ :=
ext $ λ n, by simp only [coeff_mul, coeff_add, mul_add, finset.sum_add_distrib]

protected lemma add_mul (φ₁ φ₂ φ₃ : mv_power_series σ α) :
  (φ₁ + φ₂) * φ₃ = φ₁ * φ₃ + φ₂ * φ₃ :=
ext $ λ n, by simp only [coeff_mul, coeff_add, add_mul, finset.sum_add_distrib]

protected lemma mul_assoc (φ₁ φ₂ φ₃ : mv_power_series σ α) :
  (φ₁ * φ₂) * φ₃ = φ₁ * (φ₂ * φ₃) :=
ext $ λ n,
begin
  simp only [coeff_mul],
  have := @finset.sum_sigma ((σ →₀ ℕ) × (σ →₀ ℕ)) α _ _ (antidiagonal n).support
    (λ p, (antidiagonal (p.1)).support) (λ x, coeff x.2.1 φ₁ * coeff x.2.2 φ₂ * coeff x.1.2 φ₃),
  convert this.symm using 1; clear this,
  { apply finset.sum_congr rfl,
    intros p hp, exact finset.sum_mul },
  have := @finset.sum_sigma ((σ →₀ ℕ) × (σ →₀ ℕ)) α _ _ (antidiagonal n).support
    (λ p, (antidiagonal (p.2)).support) (λ x, coeff x.1.1 φ₁ * (coeff x.2.1 φ₂ * coeff x.2.2 φ₃)),
  convert this.symm using 1; clear this,
  { apply finset.sum_congr rfl, intros p hp, rw finset.mul_sum },
  apply finset.sum_bij,
  swap 5,
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, exact ⟨(k, l+j), (l, j)⟩ },
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H,
    simp only [finset.mem_sigma, mem_antidiagonal_support] at H ⊢, finish },
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, rw mul_assoc },
  { rintros ⟨⟨a,b⟩, ⟨c,d⟩⟩ ⟨⟨i,j⟩, ⟨k,l⟩⟩ H₁ H₂,
    simp only [finset.mem_sigma, mem_antidiagonal_support,
      and_imp, prod.mk.inj_iff, add_comm, heq_iff_eq] at H₁ H₂ ⊢,
    finish },
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, refine ⟨⟨(i+k, l), (i, k)⟩, _, _⟩;
    { simp only [finset.mem_sigma, mem_antidiagonal_support] at H ⊢, finish } }
end

instance : semiring (mv_power_series σ α) :=
{ mul_one := mv_power_series.mul_one,
  one_mul := mv_power_series.one_mul,
  add_assoc := mv_power_series.add_assoc,
  zero_add := mv_power_series.zero_add,
  add_zero := mv_power_series.add_zero,
  add_comm := mv_power_series.add_comm,
  mul_assoc := mv_power_series.mul_assoc,
  mul_zero := mv_power_series.mul_zero,
  zero_mul := mv_power_series.zero_mul,
  left_distrib := mv_power_series.mul_add,
  right_distrib := mv_power_series.add_mul,
  .. mv_power_series.has_zero σ α,
  .. mv_power_series.has_one σ α,
  .. mv_power_series.has_add σ α,
  .. mv_power_series.has_mul σ α }

end ring_structure

instance C.is_semiring_hom : is_semiring_hom (C : α → mv_power_series σ α) :=
{ map_zero := C_zero _ _,
  map_one := C_one _ _,
  map_add := C_add,
  map_mul := C_mul }

instance coeff.is_add_monoid_hom (n : σ →₀ ℕ) :
  is_add_monoid_hom (coeff n : mv_power_series σ α → α) :=
{ map_zero := coeff_zero _ _ _,
  map_add := coeff_add n }

instance coeff_zero.is_semiring_hom :
  is_semiring_hom (coeff 0 : mv_power_series σ α → α) :=
{ map_one := coeff_one_zero _ _,
  map_mul := λ φ ψ, by simp [coeff_mul, support_single_ne_zero],
  .. coeff.is_add_monoid_hom 0 }

/-- If a multivariate formal power series is invertible,
 then so is its constant coefficient.-/
lemma is_unit_coeff_zero (φ : mv_power_series σ α) (h : is_unit φ) :
  is_unit (coeff 0 φ) :=
h.map' (coeff 0)

instance : semimodule α (mv_power_series σ α) :=
{ smul := λ a φ, C a * φ,
  one_smul := λ φ, one_mul _,
  mul_smul := λ a b φ, by simp only [C_mul, mul_assoc],
  smul_add := λ a φ ψ, mul_add _ _ _,
  smul_zero := λ a, mul_zero _,
  add_smul := λ a b φ, by simp only [C_add, add_mul],
  zero_smul := λ φ, by simp only [zero_mul, C_zero] }

lemma monomial_mul_monomial (m n : σ →₀ ℕ) (a b : α) :
  monomial m a * monomial n b = monomial (m + n) (a * b) :=
begin
  ext k, rw [coeff_mul, coeff_monomial], split_ifs with h,
  { rw [h, finset.sum_eq_single (m,n)],
    { rw [coeff_monomial', coeff_monomial'] },
    { rintros ⟨i,j⟩ hij hne,
      rw [ne.def, prod.mk.inj_iff, not_and] at hne,
      by_cases H : i = m,
      { rw [coeff_monomial j n b, if_neg (hne H), mul_zero] },
      { rw [coeff_monomial, if_neg H, zero_mul] } },
    { intro H, rw finsupp.mem_antidiagonal_support at H,
      exfalso, exact H rfl } },
  { rw [finset.sum_eq_zero], rintros ⟨i,j⟩ hij,
    rw finsupp.mem_antidiagonal_support at hij,
    by_cases H : i = m,
    { subst i, have : j ≠ n, { rintro rfl, exact h hij.symm },
      { rw [coeff_monomial j n b, if_neg this, mul_zero] } },
    { rw [coeff_monomial, if_neg H, zero_mul] } }
end

lemma X_pow_eq (s : σ) (n : ℕ) :
  (X s : mv_power_series σ α)^n = monomial (single s n) 1 :=
begin
  induction n with n ih,
  { rw [pow_zero, finsupp.single_zero], refl },
  { rw [pow_succ', ih, nat.succ_eq_add_one, finsupp.single_add, X, monomial_mul_monomial, one_mul] }
end

lemma coeff_X_pow (m) (s : σ) (n : ℕ) :
  coeff m ((X s : mv_power_series σ α)^n) = if m = single s n then 1 else 0 :=
by rw [X_pow_eq s n, coeff_monomial]

section map
variables {β : Type*} {γ : Type*} [semiring β] [semiring γ]
variables (f : α → β) (g : β → γ)

/-- The map between multivariate formal power series induced by a map on the coefficients.-/
def map : mv_power_series σ α → mv_power_series σ β :=
λ φ n, f $ coeff n φ

@[simp] lemma map_id : (map (id : α → α) :
  mv_power_series σ α → mv_power_series σ α) = id := rfl

lemma map_comp : (map (g ∘ f) :
  mv_power_series σ α → mv_power_series σ γ) = map g ∘ map f := rfl

@[simp] lemma coeff_map (n) (φ : mv_power_series σ α) :
  coeff n (map f φ) = f (coeff n φ) := rfl

variables [is_semiring_hom f] [is_semiring_hom g]

@[simp] lemma map_zero : map f (0 : mv_power_series σ α) = 0 :=
ext $ λ n, is_semiring_hom.map_zero f

@[simp] lemma map_one : map f (1 : mv_power_series σ α) = 1 :=
ext $ λ n, if h : n = 0
then by rw [coeff_map, h, coeff_one_zero, is_semiring_hom.map_one f, coeff_one_zero]
else by rw [coeff_map, coeff_one, if_neg h, is_semiring_hom.map_zero f, coeff_one, if_neg h]

@[simp] lemma map_add (φ ψ : mv_power_series σ α) : map f (φ + ψ) = map f φ + map f ψ :=
ext $ λ n, by rw [coeff_map, coeff_add, is_semiring_hom.map_add f, coeff_add, coeff_map, coeff_map]

@[simp] lemma map_mul (φ ψ : mv_power_series σ α) : map f (φ * ψ) = map f φ * map f ψ :=
ext $ λ n,
begin
  rw [coeff_map, coeff_mul, ← finset.sum_hom f, coeff_mul, finset.sum_congr rfl],
  rintros ⟨i,j⟩ hij, rw [is_semiring_hom.map_mul f, coeff_map, coeff_map]
end

instance map.is_semiring_hom :
  is_semiring_hom (map f : mv_power_series σ α → mv_power_series σ β) :=
{ map_zero := map_zero f,
  map_one := map_one f,
  map_add := map_add f,
  map_mul := map_mul f }

end map

end semiring

section comm_semiring
variables [comm_semiring α]
variables (φ ψ : mv_power_series σ α)

protected lemma mul_comm : φ * ψ = ψ * φ :=
ext $ λ n, finset.sum_bij (λ p hp, p.swap)
  (λ p hp, swap_mem_antidiagonal_support hp)
  (λ p hp, mul_comm _ _)
  (λ p q hp hq H, by simpa using congr_arg prod.swap H)
  (λ p hp, ⟨p.swap, swap_mem_antidiagonal_support hp, p.swap_swap.symm⟩)

instance : comm_semiring (mv_power_series σ α) :=
{ mul_comm := mv_power_series.mul_comm,
  .. mv_power_series.semiring }

section trunc
variables (n : σ →₀ ℕ)

/-- The `n`th truncation of a multivariate formal power series to a multivariate polynomial -/
def trunc (φ : mv_power_series σ α) : mv_polynomial σ α :=
{ support := (n.antidiagonal.support.image prod.fst).filter (λ m, coeff m φ ≠ 0),
  to_fun := λ m, if m ≤ n then coeff m φ else 0,
  mem_support_to_fun := λ m,
  begin
    suffices : m ∈ finset.image prod.fst ((antidiagonal n).support) ↔ m ≤ n,
    { rw [finset.mem_filter, this], split,
      { intro h, rw [if_pos h.1], exact h.2 },
      { intro h, split_ifs at h with H H,
        { exact ⟨H, h⟩ },
        { exfalso, exact h rfl } } },
    rw finset.mem_image, split,
    { rintros ⟨⟨i,j⟩, h, rfl⟩ s,
      rw finsupp.mem_antidiagonal_support at h,
      rw ← h, exact nat.le_add_right _ _ },
    { intro h, refine ⟨(m, n-m), _, rfl⟩,
      rw finsupp.mem_antidiagonal_support, ext s, exact nat.add_sub_of_le (h s) }
  end }

lemma coeff_trunc (m) (φ : mv_power_series σ α) :
  mv_polynomial.coeff m (trunc n φ) =
  if m ≤ n then coeff m φ else 0 := rfl

@[simp] lemma trunc_zero : trunc n (0 : mv_power_series σ α) = 0 :=
mv_polynomial.ext _ _ $ λ m,
begin
  rw [coeff_trunc, coeff_zero, mv_polynomial.coeff_zero],
  split_ifs; refl
end

@[simp] lemma trunc_one : trunc n (1 : mv_power_series σ α) = 1 :=
mv_polynomial.ext _ _ $ λ m,
begin
  rw [coeff_trunc, coeff_one],
  split_ifs with H H' H',
  { subst m, erw mv_polynomial.coeff_C 0, simp },
  { symmetry, erw mv_polynomial.coeff_monomial, convert if_neg (ne.elim (ne.symm H')), },
  { symmetry, erw mv_polynomial.coeff_monomial, convert if_neg _,
    intro H', apply H, subst m, intro s, exact nat.zero_le _ }
end

@[simp] lemma trunc_C (a : α) : trunc n (C a) = mv_polynomial.C a :=
mv_polynomial.ext _ _ $ λ m,
begin
  rw [coeff_trunc, coeff_C, mv_polynomial.coeff_C],
  split_ifs with H; refl <|> try {simp * at *},
  exfalso, apply H, subst m, intro s, exact nat.zero_le _
end

@[simp] lemma trunc_add (φ ψ : mv_power_series σ α) :
  trunc n (φ + ψ) = trunc n φ + trunc n ψ :=
mv_polynomial.ext _ _ $ λ m,
begin
  simp only [coeff_trunc, coeff_add, mv_polynomial.coeff_add],
  split_ifs with H, {refl}, {rw [zero_add]}
end

end trunc

lemma X_pow_dvd_iff {s : σ} {n : ℕ} {φ : mv_power_series σ α} :
  (X s : mv_power_series σ α)^n ∣ φ ↔ ∀ m : σ →₀ ℕ, m s < n → coeff m φ = 0 :=
begin
  split,
  { rintros ⟨φ, rfl⟩ m h,
    rw [coeff_mul, finset.sum_eq_zero],
    rintros ⟨i,j⟩ hij, rw [coeff_X_pow, if_neg, zero_mul],
    contrapose! h, subst i, rw finsupp.mem_antidiagonal_support at hij,
    rw [← hij, finsupp.add_apply, finsupp.single_eq_same], exact nat.le_add_right n _ },
  { intro h, refine ⟨λ m, coeff (m + (single s n)) φ, _⟩,
    ext m, by_cases H : m - single s n + single s n = m,
    { rw [coeff_mul, finset.sum_eq_single (single s n, m - single s n)],
      { rw [coeff_X_pow, if_pos rfl, one_mul], simp only [coeff, H] },
      { rintros ⟨i,j⟩ hij hne, rw finsupp.mem_antidiagonal_support at hij,
        rw coeff_X_pow, split_ifs with hi,
        { exfalso, apply hne, rw [← hij, ← hi, prod.mk.inj_iff], refine ⟨rfl, _⟩,
          ext t, simp only [nat.add_sub_cancel_left, finsupp.add_apply, finsupp.nat_sub_apply] },
        { exact zero_mul _ } },
        { intro hni, exfalso, apply hni, rwa [finsupp.mem_antidiagonal_support, add_comm] } },
    { rw [h, coeff_mul, finset.sum_eq_zero],
      { rintros ⟨i,j⟩ hij, rw finsupp.mem_antidiagonal_support at hij,
        rw coeff_X_pow, split_ifs with hi,
        { exfalso, apply H, rw [← hij, hi], ext t,
          simp only [nat.add_sub_cancel_left, add_comm,
            finsupp.add_apply, add_right_inj, finsupp.nat_sub_apply] },
        { exact zero_mul _ } },
      { classical, contrapose! H, ext t,
        by_cases hst : s = t,
        { subst t, simpa using nat.add_sub_cancel' H },
        { simp [finsupp.single_apply, hst] } } } }
end

lemma X_dvd_iff {s : σ} {φ : mv_power_series σ α} :
  (X s : mv_power_series σ α) ∣ φ ↔ ∀ m : σ →₀ ℕ, m s = 0 → coeff m φ = 0 :=
begin
  rw [← pow_one (X s : mv_power_series σ α), X_pow_dvd_iff],
  split; intros h m hm,
  { exact h m (hm.symm ▸ zero_lt_one) },
  { exact h m (nat.eq_zero_of_le_zero $ nat.le_of_succ_le_succ hm) }
end

end comm_semiring

section ring
variables [ring α]

protected def neg (φ : mv_power_series σ α) :
  mv_power_series σ α := λ n, - coeff n φ

instance : has_neg (mv_power_series σ α) := ⟨mv_power_series.neg⟩

@[simp] lemma coeff_neg (φ : mv_power_series σ α) (n) : coeff n (- φ) = - coeff n φ := rfl

protected lemma add_left_neg (φ : mv_power_series σ α) : (-φ) + φ = 0 :=
ext $ λ n, by rw [coeff_add, coeff_zero, coeff_neg, add_left_neg]

instance : ring (mv_power_series σ α) :=
{ add_left_neg := mv_power_series.add_left_neg,
  .. mv_power_series.has_neg, .. mv_power_series.semiring }

instance C.is_ring_hom : is_ring_hom (C : α → mv_power_series σ α) :=
{ map_one := C_one _ _,
  map_add := C_add,
  map_mul := C_mul }

instance coeff.is_add_group_hom (n : σ →₀ ℕ) :
  is_add_group_hom (coeff n : mv_power_series σ α → α) :=
{ map_add := coeff_add n }

instance coeff_zero.is_ring_hom :
  is_ring_hom (coeff 0 : mv_power_series σ α → α) :=
{ .. coeff_zero.is_semiring_hom }

instance map.is_ring_hom {β : Type*} [comm_ring β] (f : α → β) [is_ring_hom f] :
  is_ring_hom (map f : mv_power_series σ α → mv_power_series σ β) :=
{ .. map.is_semiring_hom f }

instance : module α (mv_power_series σ α) :=
{ ..mv_power_series.semimodule }

/-
The inverse of a multivariate formal power series is defined by
well-founded recursion on the coeffients of the inverse.
-/

/-- Auxiliary definition that unifies
 the totalised inverse formal power series `(_)⁻¹` and
 the inverse formal power series that depends on
 an inverse of the constant coefficient `inv_of_unit`.-/
protected noncomputable def inv.aux (a : α) (φ : mv_power_series σ α) : mv_power_series σ α
| n := if n = 0 then a else
- a * n.antidiagonal.support.sum (λ (x : (σ →₀ ℕ) × (σ →₀ ℕ)),
    if h : x.2 < n then coeff x.1 φ * inv.aux x.2 else 0)
using_well_founded
{ rel_tac := λ _ _, `[exact ⟨_, finsupp.lt_wf σ⟩],
  dec_tac := tactic.assumption }

lemma coeff_inv_aux (n : σ →₀ ℕ) (a : α) (φ : mv_power_series σ α) :
  coeff n (inv.aux a φ) = if n = 0 then a else
  - a * n.antidiagonal.support.sum (λ (x : (σ →₀ ℕ) × (σ →₀ ℕ)),
    if x.2 < n then coeff x.1 φ * coeff x.2 (inv.aux a φ) else 0) :=
by rw [coeff, inv.aux]; refl

/-- A multivariate formal power series is invertible if the constant coefficient is invertible.-/
def inv_of_unit (φ : mv_power_series σ α) (u : units α) : mv_power_series σ α :=
inv.aux (↑u⁻¹) φ

lemma coeff_inv_of_unit (n : σ →₀ ℕ) (φ : mv_power_series σ α) (u : units α) :
  coeff n (inv_of_unit φ u) = if n = 0 then ↑u⁻¹ else
  - ↑u⁻¹ * n.antidiagonal.support.sum (λ (x : (σ →₀ ℕ) × (σ →₀ ℕ)),
    if x.2 < n then coeff x.1 φ * coeff x.2 (inv_of_unit φ u) else 0) :=
coeff_inv_aux n (↑u⁻¹) φ

@[simp] lemma coeff_zero_inv_of_unit (φ : mv_power_series σ α) (u : units α) :
  coeff (0 : σ →₀ ℕ) (inv_of_unit φ u) = ↑u⁻¹ :=
by rw [coeff_inv_of_unit, if_pos rfl]

lemma mul_inv_of_unit (φ : mv_power_series σ α) (u : units α) (h : coeff 0 φ = u) :
  φ * inv_of_unit φ u = 1 :=
ext $ λ n,
if H : n = 0 then
begin
  erw [H, coeff_mul, coeff_one_zero, finsupp.antidiagonal_zero,
          support_single_ne_zero, finset.sum_singleton, coeff_zero_inv_of_unit, h, units.mul_inv],
  simp
end
else
begin
  have : ((0 : σ →₀ ℕ), n) ∈ n.antidiagonal.support,
  { rw [finsupp.mem_antidiagonal_support, zero_add] },
  rw [coeff_one, if_neg H, coeff_mul,
    ← finset.insert_erase this, finset.sum_insert (finset.not_mem_erase _ _),
    h, coeff_inv_of_unit, if_neg H,
    neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm, units.mul_inv_cancel_left,
    ← finset.insert_erase this, finset.sum_insert (finset.not_mem_erase _ _),
    finset.insert_erase this, if_neg (not_lt_of_ge $ le_refl _), zero_add, add_comm,
    ← sub_eq_add_neg, sub_eq_zero, finset.sum_congr rfl],
  rintros ⟨i,j⟩ hij, rw [finset.mem_erase, finsupp.mem_antidiagonal_support] at hij,
  cases hij with h₁ h₂,
  subst n, rw if_pos,
  suffices : (0 : _) + j < i + j, {simpa},
  apply add_lt_add_right,
  split,
  { intro s, exact nat.zero_le _ },
  { intro H, apply h₁,
    suffices : i = 0, {simp [this]},
    ext1 s, exact nat.eq_zero_of_le_zero (H s) }
end

end ring

section comm_ring
variables [comm_ring α]

instance : comm_ring (mv_power_series σ α) :=
{ .. mv_power_series.comm_semiring, .. mv_power_series.ring }

instance : algebra α (mv_power_series σ α) :=
{ to_fun := C,
  commutes' := λ _ _, mul_comm _ _,
  smul_def' := λ c p, rfl,
  .. mv_power_series.module }

/-- Multivariate formal power series over a local ring form a local ring.-/
def is_local_ring (h : is_local_ring α) : is_local_ring (mv_power_series σ α) :=
begin
  split,
  { intro H, apply ‹is_local_ring α›.1, simpa using congr_arg (coeff 0) H },
  { intro φ, rcases ‹is_local_ring α›.2 (coeff 0 φ) with ⟨u,h⟩|⟨u,h⟩; [left, right];
    { refine is_unit_of_mul_one _ _ (mul_inv_of_unit _ u _),
      simpa using h } }
end

-- TODO(jmc): once adic topology lands, show that this is complete

end comm_ring

section nonzero_comm_ring
variables [nonzero_comm_ring α]

instance : nonzero_comm_ring (mv_power_series σ α) :=
{ zero_ne_one := λ h,
  begin
    replace h := congr_arg (coeff 0) h,
    rw [coeff_zero, coeff_one_zero] at h,
    exact zero_ne_one h
  end,
  .. mv_power_series.comm_ring }

lemma X_inj {s t : σ} : (X s : mv_power_series σ α) = X t ↔ s = t :=
⟨begin
  intro h, replace h := congr_arg (coeff (single s 1)) h, rw [coeff_X, if_pos rfl, coeff_X] at h,
  split_ifs at h with H,
  { rw finsupp.single_eq_single_iff at H,
    cases H, { exact H.1 }, { exfalso, exact one_ne_zero H.1 } },
  { exfalso, exact one_ne_zero h }
end, congr_arg X⟩

end nonzero_comm_ring

section local_ring
variables {β : Type*} (f : α → β)
variables [local_ring α] [local_ring β] [is_local_ring_hom f]

instance : local_ring (mv_power_series σ α) :=
local_of_is_local_ring $ is_local_ring ⟨zero_ne_one, local_ring.is_local⟩

instance map.is_local_ring_hom :
  is_local_ring_hom (map f : mv_power_series σ α → mv_power_series σ β) :=
{ map_nonunit :=
  begin
    rintros φ ⟨ψ, h⟩,
    replace h := congr_arg (coeff 0) h,
    rw coeff_map at h,
    have : is_unit (coeff 0 ↑ψ) := @is_unit_coeff_zero σ β _ (↑ψ) (is_unit_unit ψ),
    rw ← h at this,
    rcases is_unit_of_map_unit f _ this with ⟨c, hc⟩,
    exact is_unit_of_mul_one φ (inv_of_unit φ c) (mul_inv_of_unit φ c hc)
  end,
  .. map.is_ring_hom f }

end local_ring

section discrete_field
variables [discrete_field α]

protected def inv (φ : mv_power_series σ α) : mv_power_series σ α :=
inv.aux (coeff 0 φ)⁻¹ φ

instance : has_inv (mv_power_series σ α) := ⟨mv_power_series.inv⟩

lemma coeff_inv (n) (φ : mv_power_series σ α) :
  coeff n (φ⁻¹) = if n = 0 then (coeff 0 φ)⁻¹ else
  - (coeff 0 φ)⁻¹ * n.antidiagonal.support.sum (λ (x : (σ →₀ ℕ) × (σ →₀ ℕ)),
    if x.2 < n then coeff x.1 φ * coeff x.2 (φ⁻¹) else 0) :=
coeff_inv_aux n _ φ

@[simp] lemma coeff_zero_inv (φ : mv_power_series σ α) :
  coeff 0 (φ⁻¹) = (coeff 0 φ)⁻¹ :=
by rw [coeff_inv, if_pos rfl]

lemma inv_eq_zero {φ : mv_power_series σ α} :
  φ⁻¹ = 0 ↔ coeff 0 φ = 0 :=
⟨λ h, by simpa using congr_arg (coeff 0) h,
 λ h, ext $ λ n, by { rw coeff_inv, split_ifs;
 simp only [h, mv_power_series.coeff_zero, zero_mul, inv_zero, neg_zero] }⟩

@[simp] lemma inv_of_unit_eq (φ : mv_power_series σ α) (h : coeff 0 φ ≠ 0) :
  inv_of_unit φ (units.mk0 _ h) = φ⁻¹ := rfl

@[simp] lemma inv_of_unit_eq' (φ : mv_power_series σ α) (u : units α) (h : coeff 0 φ = u) :
  inv_of_unit φ u = φ⁻¹ :=
begin
  rw ← inv_of_unit_eq φ (h.symm ▸ u.ne_zero),
  congr' 1, rw [units.ext_iff], exact h.symm,
end

@[simp] protected lemma mul_inv (φ : mv_power_series σ α) (h : coeff 0 φ ≠ 0) :
  φ * φ⁻¹ = 1 :=
by rw [← inv_of_unit_eq φ h, mul_inv_of_unit φ (units.mk0 _ h) rfl]

@[simp] protected lemma inv_mul (φ : mv_power_series σ α) (h : coeff 0 φ ≠ 0) :
  φ⁻¹ * φ = 1 :=
by rw [mul_comm, φ.mul_inv h]

end discrete_field

end mv_power_series

namespace mv_polynomial
open finsupp
variables {σ : Type*} {α : Type*} [comm_semiring α]

/-- The natural inclusion from multivariate polynomials into multivariate formal power series.-/
instance coe_to_mv_power_series : has_coe (mv_polynomial σ α) (mv_power_series σ α) :=
⟨λ φ n, coeff n φ⟩

@[simp, elim_cast] lemma coeff_coe (φ : mv_polynomial σ α) (n) :
mv_power_series.coeff n ↑φ = coeff n φ := rfl

@[simp, elim_cast] lemma coe_monomial (n : σ →₀ ℕ) (a : α) :
  (monomial n a : mv_power_series σ α) = mv_power_series.monomial n a :=
mv_power_series.ext $ λ m,
begin
  rw [coeff_coe, coeff_monomial, mv_power_series.coeff_monomial],
  split_ifs with h₁ h₂; refl <|> subst m; contradiction
end

@[simp, elim_cast] lemma coe_zero : ((0 : mv_polynomial σ α) : mv_power_series σ α) = 0 := rfl

@[simp, elim_cast] lemma coe_one : ((1 : mv_polynomial σ α) : mv_power_series σ α) = 1 :=
coe_monomial _ _

@[simp, elim_cast] lemma coe_add (φ ψ : mv_polynomial σ α) :
  ((φ + ψ : mv_polynomial σ α) : mv_power_series σ α) = φ + ψ := rfl

@[simp, elim_cast] lemma coe_mul (φ ψ : mv_polynomial σ α) :
  ((φ * ψ : mv_polynomial σ α) : mv_power_series σ α) = φ * ψ :=
mv_power_series.ext $ λ n,
by simp only [coeff_coe, mv_power_series.coeff_mul, coeff_mul]

@[simp, elim_cast] lemma coe_C (a : α) :
  ((C a : mv_polynomial σ α) : mv_power_series σ α) = mv_power_series.C a :=
coe_monomial _ _

@[simp, elim_cast] lemma coe_X (s : σ) :
  ((X s : mv_polynomial σ α) : mv_power_series σ α) = mv_power_series.X s :=
coe_monomial _ _

namespace coe_to_mv_power_series

instance : is_semiring_hom (coe : mv_polynomial σ α → mv_power_series σ α) :=
{ map_zero := coe_zero,
  map_one := coe_one,
  map_add := coe_add,
  map_mul := coe_mul }

end coe_to_mv_power_series

end mv_polynomial

/-- Formal power series over the coefficient ring `α`.-/
def power_series (α : Type*) := mv_power_series unit α

namespace power_series
open finsupp (single)
variable {α : Type*}

/-- The `n`th coefficient of a formal power series.-/
def coeff (n : ℕ) : power_series α → α := mv_power_series.coeff (single () n)

/-- Two formal power series are equal if all their coefficients are equal.-/
@[extensionality] lemma ext {φ ψ : power_series α} (h : ∀ n, coeff n φ = coeff n ψ) :
  φ = ψ :=
mv_power_series.ext $ λ n,
have this : n = single () (n ()), from (finsupp.unique_single n),
by convert h (n ())

/-- Two formal power series are equal if all their coefficients are equal.-/
lemma ext_iff {φ ψ : power_series α} : φ = ψ ↔ (∀ n, coeff n φ = coeff n ψ) :=
⟨λ h n, congr_arg (coeff n) h, ext⟩

/-- Constructor for formal power series.-/
def mk (f : ℕ → α) : power_series α := λ s, f (s ())

@[simp] lemma coeff_mk (n : ℕ) (f : ℕ → α) : coeff n (mk f) = f n :=
congr_arg f finsupp.single_eq_same

instance [semiring α] :      semiring (power_series α) :=      by delta power_series; apply_instance
instance [comm_semiring α] : comm_semiring (power_series α) := by delta power_series; apply_instance
instance [ring α] :          ring (power_series α) :=          by delta power_series; apply_instance
instance [comm_ring α] :     comm_ring (power_series α) :=     by delta power_series; apply_instance
instance [nonzero_comm_ring α] : nonzero_comm_ring (power_series α) := by delta power_series; apply_instance

section semiring
variable [semiring α]

/-- The `n`th monimial with coefficient `a` as formal power series.-/
def monomial (n : ℕ) : α → power_series α := mv_power_series.monomial (single () n)

/-- The constant formal power series.-/
def C : α → power_series α := mv_power_series.C

/-- The variable of the formal power series ring.-/
def X : power_series α := mv_power_series.X ()

lemma coeff_monomial (m n : ℕ) (a : α) :
  coeff m (monomial n a) = if m = n then a else 0 :=
calc coeff m (monomial n a) = _ : mv_power_series.coeff_monomial _ _ _
    ... = if m = n then a else 0 :
by { simp only [finsupp.unique_single_eq_iff], split_ifs; refl }

lemma monomial_eq_mk (n : ℕ) (a : α) :
  monomial n a = mk (λ m, if m = n then a else 0) :=
ext $ λ m, by { rw [coeff_monomial, coeff_mk] }

@[simp] lemma coeff_monomial' (n : ℕ) (a : α) :
  coeff n (monomial n a) = a :=
by convert if_pos rfl

@[simp] lemma monomial_index_zero (a : α) : (monomial 0 a : power_series α) = C a := rfl

@[simp] lemma monomial_coeff_zero (n : ℕ) : (monomial n 0 : power_series α) = 0 :=
mv_power_series.monomial_coeff_zero _

lemma C_eq (a : α) : C a = monomial 0 a := rfl

lemma coeff_C (n : ℕ) (a : α) :
  coeff n (C a : power_series α) = if n = 0 then a else 0 :=
by rw [C_eq, coeff_monomial]

@[simp] lemma monomial_zero (a : α) : (monomial 0 a : power_series α) = C a :=
ext $ λ n, by rw [coeff_C, coeff_monomial]

lemma X_eq : (X : power_series α) = monomial 1 1 := rfl

@[simp] lemma coeff_C_zero (a : α) : coeff 0 (C a) = a :=
by rw [← monomial_zero, coeff_monomial' 0 a]

lemma coeff_X (n : ℕ) :
  coeff n (X : power_series α) = if n = 1 then 1 else 0 :=
by rw [X_eq, coeff_monomial]

@[simp] lemma coeff_zero_X : coeff 0 (X : power_series α) = 0 :=
mv_power_series.coeff_zero_X _

@[simp] lemma coeff_one_X : coeff 1 (X : power_series α) = 1 :=
by rw [coeff_X, if_pos rfl]

lemma X_pow_eq (n : ℕ) : (X : power_series α)^n = monomial n 1 :=
mv_power_series.X_pow_eq _ n

lemma coeff_X_pow (m n : ℕ) :
  coeff m ((X : power_series α)^n) = if m = n then 1 else 0 :=
by rw [X_pow_eq, coeff_monomial]

@[simp] lemma coeff_zero (n : ℕ) : coeff n (0 : power_series α) = 0 := rfl

@[simp] lemma C_zero : (C 0 : power_series α) = 0 := mv_power_series.C_zero _ _

@[simp] lemma coeff_one (n : ℕ) :
  coeff n (1 : power_series α) = if n = 0 then 1 else 0 :=
calc coeff n (1 : power_series α) = _ : mv_power_series.coeff_one _ _ _
    ... = if n = 0 then 1 else 0 :
by { simp only [finsupp.single_eq_zero], split_ifs; refl }

@[simp] lemma coeff_one_zero : coeff 0 (1 : power_series α) = 1 :=
coeff_C_zero 1

@[simp] lemma C_one : (C 1 : power_series α) = 1 := rfl

@[simp] lemma coeff_add (n : ℕ) (φ ψ : power_series α) :
  coeff n (φ + ψ) = coeff n φ + coeff n ψ := rfl

@[simp] lemma monomial_add (n : ℕ) (a b : α) :
  (monomial n (a + b) : power_series α) = monomial n a + monomial n b :=
mv_power_series.monomial_add _ _ _

@[simp] lemma C_add (a b : α) : (C (a + b) : power_series α) = C a + C b :=
by rw [← monomial_zero, ← monomial_zero, ← monomial_zero, monomial_add 0 a b]

lemma coeff_mul (n : ℕ) (φ ψ : power_series α) :
  coeff n (φ * ψ) = (finset.nat.antidiagonal n).sum (λ p, coeff p.1 φ * coeff p.2 ψ) :=
begin
  symmetry,
  apply finset.sum_bij (λ (p : ℕ × ℕ) h, (single () p.1, single () p.2)),
  { rintros ⟨i,j⟩ hij, rw finset.nat.mem_antidiagonal at hij,
    rw [finsupp.mem_antidiagonal_support, ← finsupp.single_add, hij] },
  { rintros ⟨i,j⟩ hij, refl },
  { rintros ⟨i,j⟩ ⟨k,l⟩ hij hkl,
    simpa only [prod.mk.inj_iff, finsupp.unique_single_eq_iff] using id },
  { rintros ⟨f,g⟩ hfg,
    refine ⟨(f (), g ()), _, _⟩,
    { rw finsupp.mem_antidiagonal_support at hfg,
      rw [finset.nat.mem_antidiagonal, ← finsupp.add_apply, hfg, finsupp.single_eq_same] },
    { rw prod.mk.inj_iff, dsimp,
      exact ⟨finsupp.unique_single f, finsupp.unique_single g⟩ } }
end

@[simp] lemma C_mul (a b : α) : (C (a * b) : power_series α) = C a * C b :=
mv_power_series.C_mul _ _

instance C.is_semiring_hom : is_semiring_hom (C : α → power_series α) :=
mv_power_series.C.is_semiring_hom

instance coeff.is_add_monoid_hom (n : ℕ) :
  is_add_monoid_hom (coeff n : power_series α → α) :=
{ map_zero := coeff_zero n,
  map_add := coeff_add n }

instance coeff_zero.is_semiring_hom :
  is_semiring_hom (coeff 0 : power_series α → α) :=
mv_power_series.coeff_zero.is_semiring_hom

instance : semimodule α (power_series α) :=
mv_power_series.semimodule

/-- If a formal power series is invertible, then so is its constant coefficient.-/
lemma is_unit_coeff_zero (φ : power_series α) (h : is_unit φ) :
  is_unit (coeff 0 φ) :=
mv_power_series.is_unit_coeff_zero φ h

section map
variables {β : Type*} {γ : Type*} [semiring β] [semiring γ]
variables (f : α → β) (g : β → γ)

/-- The map between formal power series induced by a map on the coefficients.-/
def map : power_series α → power_series β :=
mv_power_series.map f

@[simp] lemma map_id : (map (id : α → α) :
  power_series α → power_series α) = id := rfl

lemma map_comp : (map (g ∘ f) :
  power_series α → power_series γ) = map g ∘ map f := rfl

@[simp] lemma coeff_map (n : ℕ) (φ : power_series α) :
  coeff n (map f φ) = f (coeff n φ) := rfl

variables [is_semiring_hom f] [is_semiring_hom g]

@[simp] lemma map_zero : map f (0 : power_series α) = 0 :=
mv_power_series.map_zero f

@[simp] lemma map_one : map f (1 : power_series α) = 1 :=
mv_power_series.map_one f

@[simp] lemma map_add (φ ψ : power_series α) : map f (φ + ψ) = map f φ + map f ψ :=
mv_power_series.map_add f φ ψ

@[simp] lemma map_mul (φ ψ : power_series α) : map f (φ * ψ) = map f φ * map f ψ :=
mv_power_series.map_mul f φ ψ

instance map.is_semiring_hom :
  is_semiring_hom (map f : power_series α → power_series β) :=
mv_power_series.map.is_semiring_hom f

end map

end semiring

section comm_semiring
variables [comm_semiring α]

lemma X_pow_dvd_iff {n : ℕ} {φ : power_series α} :
  (X : power_series α)^n ∣ φ ↔ ∀ m, m < n → coeff m φ = 0 :=
begin
  convert @mv_power_series.X_pow_dvd_iff unit α _ _ () n φ, apply propext,
  classical, split; intros h m hm,
  { rw finsupp.unique_single m, convert h _ hm },
  { apply h, simpa only [finsupp.single_eq_same] using hm }
end

lemma X_dvd_iff {φ : power_series α} :
  (X : power_series α) ∣ φ ↔ coeff 0 φ = 0 :=
begin
  rw [← pow_one (X : power_series α), X_pow_dvd_iff],
  split; intro h,
  { exact h 0 zero_lt_one },
  { intros m hm, rwa nat.eq_zero_of_le_zero (nat.le_of_succ_le_succ hm) }
end

section trunc

/-- The `n`th truncation of a formal power series to a polynomial -/
def trunc (n : ℕ) (φ : power_series α) : polynomial α :=
{ support := ((finset.nat.antidiagonal n).image prod.fst).filter (λ m, coeff m φ ≠ 0),
  to_fun := λ m, if m ≤ n then coeff m φ else 0,
  mem_support_to_fun := λ m,
  begin
    suffices : m ∈ ((finset.nat.antidiagonal n).image prod.fst) ↔ m ≤ n,
    { rw [finset.mem_filter, this], split,
      { intro h, rw [if_pos h.1], exact h.2 },
      { intro h, split_ifs at h with H H,
        { exact ⟨H, h⟩ },
        { exfalso, exact h rfl } } },
    rw finset.mem_image, split,
    { rintros ⟨⟨i,j⟩, h, rfl⟩,
      rw finset.nat.mem_antidiagonal at h,
      rw ← h, exact nat.le_add_right _ _ },
    { intro h, refine ⟨(m, n-m), _, rfl⟩,
      rw finset.nat.mem_antidiagonal, exact nat.add_sub_of_le h }
  end }

lemma coeff_trunc (m) (n) (φ : power_series α) :
  polynomial.coeff (trunc n φ) m = if m ≤ n then coeff m φ else 0 := rfl

@[simp] lemma trunc_zero (n) : trunc n (0 : power_series α) = 0 :=
polynomial.ext.2 $ λ m,
begin
  rw [coeff_trunc, coeff_zero, polynomial.coeff_zero],
  split_ifs; refl
end

@[simp] lemma trunc_one (n) : trunc n (1 : power_series α) = 1 :=
polynomial.ext.2 $ λ m,
begin
  rw [coeff_trunc, coeff_one],
  split_ifs with H H' H'; rw [polynomial.coeff_one],
  { subst m, rw [if_pos rfl] },
  { symmetry, exact if_neg (ne.elim (ne.symm H')) },
  { symmetry, refine if_neg _,
    intro H', apply H, subst m, exact nat.zero_le _ }
end

@[simp] lemma trunc_C (n) (a : α) : trunc n (C a) = polynomial.C a :=
polynomial.ext.2 $ λ m,
begin
  rw [coeff_trunc, coeff_C, polynomial.coeff_C],
  split_ifs with H; refl <|> try {simp * at *}
end

@[simp] lemma trunc_add (n) (φ ψ : power_series α) :
  trunc n (φ + ψ) = trunc n φ + trunc n ψ :=
polynomial.ext.2 $ λ m,
begin
  simp only [coeff_trunc, coeff_add, polynomial.coeff_add],
  split_ifs with H, {refl}, {rw [zero_add]}
end

end trunc

end comm_semiring

section ring
variables [ring α]

instance C.is_ring_hom : is_ring_hom (C : α → power_series α) :=
mv_power_series.C.is_ring_hom

instance coeff_zero.is_ring_hom :
  is_ring_hom (coeff 0 : power_series α → α) :=
{ .. coeff_zero.is_semiring_hom }

instance map.is_ring_hom {β : Type*} [comm_ring β] (f : α → β) [is_ring_hom f] :
  is_ring_hom (map f : power_series α → power_series β) :=
{ .. map.is_semiring_hom f }

instance : module α (power_series α) :=
mv_power_series.module

protected def inv.aux : α → power_series α → power_series α :=
mv_power_series.inv.aux

lemma coeff_inv_aux (n : ℕ) (a : α) (φ : power_series α) :
  coeff n (inv.aux a φ) = if n = 0 then a else
  - a * (finset.nat.antidiagonal n).sum (λ (x : ℕ × ℕ),
    if x.2 < n then coeff x.1 φ * coeff x.2 (inv.aux a φ) else 0) :=
begin
  rw [coeff, inv.aux, mv_power_series.coeff_inv_aux],
  simp only [finsupp.single_eq_zero],
  split_ifs, {refl},
  congr' 1,
  symmetry,
  apply finset.sum_bij (λ (p : ℕ × ℕ) h, (single () p.1, single () p.2)),
  { rintros ⟨i,j⟩ hij, rw finset.nat.mem_antidiagonal at hij,
    rw [finsupp.mem_antidiagonal_support, ← finsupp.single_add, hij] },
  { rintros ⟨i,j⟩ hij,
    by_cases H : j < n,
    { rw [if_pos H, if_pos], {refl},
      split,
      { rintro ⟨⟩, simpa [finsupp.single_eq_same] using le_of_lt H },
      { intro hh, rw lt_iff_not_ge at H, apply H,
        simpa [finsupp.single_eq_same] using hh () } },
    { rw [if_neg H, if_neg], rintro ⟨h₁, h₂⟩, apply h₂, rintro ⟨⟩,
     simpa [finsupp.single_eq_same] using not_lt.1 H } },
  { rintros ⟨i,j⟩ ⟨k,l⟩ hij hkl,
    simpa only [prod.mk.inj_iff, finsupp.unique_single_eq_iff] using id },
  { rintros ⟨f,g⟩ hfg,
    refine ⟨(f (), g ()), _, _⟩,
    { rw finsupp.mem_antidiagonal_support at hfg,
      rw [finset.nat.mem_antidiagonal, ← finsupp.add_apply, hfg, finsupp.single_eq_same] },
    { rw prod.mk.inj_iff, dsimp,
      exact ⟨finsupp.unique_single f, finsupp.unique_single g⟩ } }
end

/-- A formal power series is invertible if the constant coefficient is invertible.-/
def inv_of_unit (φ : power_series α) (u : units α) : power_series α :=
mv_power_series.inv_of_unit φ u

lemma coeff_inv_of_unit (n : ℕ) (φ : power_series α) (u : units α) :
  coeff n (inv_of_unit φ u) = if n = 0 then ↑u⁻¹ else
  - ↑u⁻¹ * (finset.nat.antidiagonal n).sum (λ (x : ℕ × ℕ),
    if x.2 < n then coeff x.1 φ * coeff x.2 (inv_of_unit φ u) else 0) :=
coeff_inv_aux n ↑u⁻¹ φ

@[simp] lemma coeff_zero_inv_of_unit (φ : power_series α) (u : units α) :
  coeff (0 : ℕ) (inv_of_unit φ u) = ↑u⁻¹ :=
by rw [coeff_inv_of_unit, if_pos rfl]

lemma mul_inv_of_unit (φ : power_series α) (u : units α) (h : coeff 0 φ = u) :
  φ * inv_of_unit φ u = 1 :=
mv_power_series.mul_inv_of_unit φ u $
by { convert h, rw finsupp.single_zero }

end ring

instance [comm_ring α] : algebra α (power_series α) :=
mv_power_series.algebra

section integral_domain
variable [integral_domain α]

local attribute [instance, priority 1] classical.prop_decidable
noncomputable theory

instance : integral_domain (power_series α) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero :=
  begin
    intros φ ψ h, rw classical.or_iff_not_imp_left, intro H,
    have ex : ∃ m, coeff m φ ≠ 0, { contrapose! H, exact ext H },
    let P : ℕ → Prop := λ k, coeff k φ ≠ 0,
    let m := nat.find ex,
    have hm₁ : coeff m φ ≠ 0 := nat.find_spec ex,
    have hm₂ : ∀ k < m, ¬coeff k φ ≠ 0 := λ k, nat.find_min ex,
    ext n, rw coeff_zero, apply nat.strong_induction_on n,
    clear n, intros n ih,
    replace h := congr_arg (coeff (m + n)) h,
    rw [coeff_zero, coeff_mul, finset.sum_eq_single (m,n)] at h,
    { replace h := eq_zero_or_eq_zero_of_mul_eq_zero h,
      rw or_iff_not_imp_left at h, exact h hm₁ },
    { rintro ⟨i,j⟩ hij hne,
      by_cases hj : j < n, { rw [ih j hj, mul_zero] },
      by_cases hi : i < m,
      { specialize hm₂ _ hi, push_neg at hm₂, rw [hm₂, zero_mul] },
      rw finset.nat.mem_antidiagonal at hij,
      push_neg at hi hj,
      suffices : m < i,
      { have : m + n < i + j := add_lt_add_of_lt_of_le this hj,
        exfalso, exact ne_of_lt this hij.symm },
      contrapose! hne, have : i = m := le_antisymm hne hi, subst i, clear hi hne,
      simpa [ne.def, prod.mk.inj_iff] using (add_left_inj m).mp hij },
    { contrapose!, intro h, rw finset.nat.mem_antidiagonal }
  end,
  .. mv_power_series.nonzero_comm_ring, .. mv_power_series.comm_ring }

/-- The ideal spanned by the variable in the power series ring
 over an integral domain is a prime ideal.-/
lemma span_X_is_prime : (ideal.span ({X} : set (power_series α))).is_prime :=
begin
  suffices : ideal.span ({X} : set (power_series α)) = is_ring_hom.ker (coeff 0),
  { rw this, exact is_ring_hom.ker_is_prime _ },
  apply ideal.ext, intro φ,
  rw [is_ring_hom.mem_ker, ideal.mem_span_singleton, X_dvd_iff]
end

/-- The variable of the power series ring over an integral domain is prime.-/
lemma X_prime : prime (X : power_series α) :=
begin
  rw ← ideal.span_singleton_prime,
  { exact span_X_is_prime },
  { intro h, simpa only [coeff_one_X, one_ne_zero, coeff_zero] using congr_arg (coeff 1) h }
end

end integral_domain

section local_ring
variables [comm_ring α]

lemma is_local_ring (h : is_local_ring α) :
  is_local_ring (power_series α) :=
mv_power_series.is_local_ring h

end local_ring

section local_ring
variables {β : Type*} (f : α → β)
variables [local_ring α] [local_ring β] [is_local_ring_hom f]

instance : local_ring (power_series α) :=
mv_power_series.local_ring

instance map.is_local_ring_hom :
  is_local_ring_hom (map f : power_series α → power_series β) :=
mv_power_series.map.is_local_ring_hom f

end local_ring

section discrete_field
variables [discrete_field α]

protected def inv : power_series α → power_series α :=
mv_power_series.inv

instance : has_inv (power_series α) := ⟨power_series.inv⟩

lemma inv_eq_inv_aux (φ : power_series α) :
  φ⁻¹ = inv.aux (coeff 0 φ)⁻¹ φ :=
by { rw [coeff, finsupp.single_zero], refl }

lemma coeff_inv (n) (φ : power_series α) :
  coeff n (φ⁻¹) = if n = 0 then (coeff 0 φ)⁻¹ else
  - (coeff 0 φ)⁻¹ * (finset.nat.antidiagonal n).sum (λ (x : ℕ × ℕ),
    if x.2 < n then coeff x.1 φ * coeff x.2 (φ⁻¹) else 0) :=
by rw [inv_eq_inv_aux, coeff_inv_aux n (coeff 0 φ)⁻¹ φ]

@[simp] lemma coeff_zero_inv (φ : power_series α) :
  coeff 0 (φ⁻¹) = (coeff 0 φ)⁻¹ :=
by rw [coeff, finsupp.single_zero, mv_power_series.coeff_zero_inv φ]

lemma inv_eq_zero {φ : power_series α} :
  φ⁻¹ = 0 ↔ coeff 0 φ = 0 :=
by erw [coeff, finsupp.single_zero, mv_power_series.inv_eq_zero]

@[simp] lemma inv_of_unit_eq (φ : power_series α) (h : coeff 0 φ ≠ 0) :
  inv_of_unit φ (units.mk0 _ h) = φ⁻¹ :=
begin
  convert mv_power_series.inv_of_unit_eq φ _;
  rw [coeff,finsupp.single_zero] at *;
  assumption
end

@[simp] lemma inv_of_unit_eq' (φ : power_series α) (u : units α) (h : coeff 0 φ = u) :
  inv_of_unit φ u = φ⁻¹ :=
begin
  convert mv_power_series.inv_of_unit_eq' φ _ _,
  rwa [coeff,finsupp.single_zero] at h
end

@[simp] protected lemma mul_inv (φ : power_series α) (h : coeff 0 φ ≠ 0) :
  φ * φ⁻¹ = 1 :=
begin
  convert mv_power_series.mul_inv φ _,
  rwa [coeff,finsupp.single_zero] at h
end

@[simp] protected lemma inv_mul (φ : power_series α) (h : coeff 0 φ ≠ 0) :
  φ⁻¹ * φ = 1 :=
begin
  convert mv_power_series.inv_mul φ _,
  rwa [coeff,finsupp.single_zero] at h
end

end discrete_field

end power_series

namespace power_series
variable {α : Type*}

local attribute [instance, priority 1] classical.prop_decidable
noncomputable theory

section order_basic
open multiplicity
variables [comm_semiring α]

/-- The order of a formal power series `φ` is the smallest `n : enat`
such that `X^n` divides `φ`. The order is `⊤` if and only if `φ = 0`. -/
@[reducible] def order (φ : power_series α) : enat :=
multiplicity X φ

lemma order_finite_of_coeff_ne_zero (φ : power_series α) (h : ∃ n, coeff n φ ≠ 0) :
  (order φ).dom :=
begin
  cases h with n h, refine ⟨n, _⟩,
  rw X_pow_dvd_iff, push_neg, exact ⟨n, lt_add_one n, h⟩
end

/-- If the order of a formal power series is finite,
then the coefficient indexed by the order is nonzero.-/
lemma coeff_order (φ : power_series α) (h : (order φ).dom) :
  coeff (φ.order.get h) φ ≠ 0 :=
begin
  have H := nat.find_spec h, contrapose! H, rw X_pow_dvd_iff,
  intros m hm, by_cases Hm : m < nat.find h,
  { have := nat.find_min h Hm, push_neg at this,
    rw X_pow_dvd_iff at this, exact this m (lt_add_one m) },
  have : m = nat.find h, {linarith}, {rwa this}
end

/-- If the `n`th coefficient of a formal power series is nonzero,
then the order of the power series is less than or equal to `n`.-/
lemma order_le (φ : power_series α) (n : ℕ) (h : coeff n φ ≠ 0) :
  order φ ≤ n :=
begin
  have h : ¬ X^(n+1) ∣ φ,
  { rw X_pow_dvd_iff, push_neg, exact ⟨n, lt_add_one n, h⟩ },
  have : (order φ).dom := ⟨n, h⟩,
  rw [← enat.coe_get this, enat.coe_le_coe],
  refine nat.find_min' this h
end

/-- The `n`th coefficient of a formal power series is `0` if `n` is strictly
smaller than the order of the power series.-/
lemma coeff_of_lt_order (φ : power_series α) (n : ℕ) (h: ↑n < order φ) :
  coeff n φ = 0 :=
by { contrapose! h, exact order_le _ _ h }

/-- The `0` power series is the unique power series with infinite order.-/
lemma order_eq_top {φ : power_series α} :
  φ.order = ⊤ ↔ φ = 0 :=
begin
  rw eq_top_iff,
  split,
  { intro h, ext n, specialize h (n+1), rw X_pow_dvd_iff at h, exact h n (lt_add_one _) },
  { rintros rfl n, exact dvd_zero _ }
end

/-- The order of the `0` power series is infinite.-/
@[simp] lemma order_zero : order (0 : power_series α) = ⊤ :=
multiplicity.zero _

/-- The order of a formal power series is at least `n` if
the `i`th coefficient is `0` for all `i < n`.-/
lemma order_ge_nat (φ : power_series α) (n : ℕ) (h : ∀ i < n, coeff i φ = 0) :
  order φ ≥ n :=
begin
  by_contra H, rw not_le at H,
  have : (order φ).dom := enat.dom_of_le_some (le_of_lt H),
  rw [← enat.coe_get this, enat.coe_lt_coe] at H,
  exact coeff_order _ this (h _ H)
end

/-- The order of a formal power series is at least `n` if
the `i`th coefficient is `0` for all `i < n`.-/
lemma order_ge (φ : power_series α) (n : enat) (h : ∀ i : ℕ, ↑i < n → coeff i φ = 0) :
  order φ ≥ n :=
begin
  induction n using enat.cases_on,
  { show _ ≤ _, rw [lattice.top_le_iff, order_eq_top],
    ext i, exact h _ (enat.coe_lt_top i) },
  { apply order_ge_nat, simpa only [enat.coe_lt_coe] using h }
end

/-- The order of a formal power series is exactly `n` if the `n`th coefficient is nonzero,
and the `i`th coefficient is `0` for all `i < n`.-/
lemma order_eq_nat {φ : power_series α} {n : ℕ} :
  order φ = n ↔ (coeff n φ ≠ 0) ∧ (∀ i, i < n → coeff i φ = 0) :=
begin
  simp only [eq_some_iff, X_pow_dvd_iff], push_neg,
  split,
  { rintros ⟨h₁, m, hm₁, hm₂⟩, refine ⟨_, h₁⟩,
    suffices : n = m, { rwa this },
    suffices : m ≥ n, { linarith },
    contrapose! hm₂, exact h₁ _ hm₂ },
  { rintros ⟨h₁, h₂⟩, exact ⟨h₂, n, lt_add_one n, h₁⟩ }
end

/-- The order of a formal power series is exactly `n` if the `n`th coefficient is nonzero,
and the `i`th coefficient is `0` for all `i < n`.-/
lemma order_eq {φ : power_series α} {n : enat} :
  order φ = n ↔ (∀ i:ℕ, ↑i = n → coeff i φ ≠ 0) ∧ (∀ i:ℕ, ↑i < n → coeff i φ = 0) :=
begin
  induction n using enat.cases_on,
  { rw order_eq_top, split,
    { rintro rfl, split; intros,
      { exfalso, exact enat.coe_ne_top ‹_› ‹_› },
      { exact coeff_zero _ } },
    { rintro ⟨h₁, h₂⟩, ext i, exact h₂ i (enat.coe_lt_top i) } },
  { simpa [enat.coe_inj] using order_eq_nat }
end

/-- The order of the sum of two formal power series
 is at least the minimum of their orders.-/
lemma order_add_ge (φ ψ : power_series α) :
  order (φ + ψ) ≥ min (order φ) (order ψ) :=
multiplicity.min_le_multiplicity_add

private lemma order_add_of_order_eq.aux (φ ψ : power_series α)
  (h : order φ ≠ order ψ) (H : order φ < order ψ) :
  order (φ + ψ) ≤ order φ ⊓ order ψ :=
begin
  suffices : order (φ + ψ) = order φ,
  { rw [lattice.le_inf_iff, this], exact ⟨le_refl _, le_of_lt H⟩ },
  { rw order_eq, split,
    { intros i hi, rw [coeff_add, coeff_of_lt_order ψ i (hi.symm ▸ H), add_zero],
      exact (order_eq_nat.1 hi.symm).1 },
    { intros i hi,
      rw [coeff_add, coeff_of_lt_order φ i hi, coeff_of_lt_order ψ i (lt_trans hi H), zero_add] } }
end

/-- The order of the sum of two formal power series
 is the minimum of their orders if their orders differ.-/
lemma order_add_of_order_eq (φ ψ : power_series α) (h : order φ ≠ order ψ) :
  order (φ + ψ) = order φ ⊓ order ψ :=
begin
  refine le_antisymm _ (order_add_ge _ _),
  by_cases H₁ : order φ < order ψ,
  { apply order_add_of_order_eq.aux _ _ h H₁ },
  by_cases H₂ : order ψ < order φ,
  { simpa only [add_comm, lattice.inf_comm] using order_add_of_order_eq.aux _ _ h.symm H₂ },
  exfalso, exact h (le_antisymm (not_lt.1 H₂) (not_lt.1 H₁))
end

/-- The order of the product of two formal power series
 is at least the sum of their orders.-/
lemma order_mul_ge (φ ψ : power_series α) :
  order (φ * ψ) ≥ order φ + order ψ :=
begin
  apply order_ge,
  intros n hn, rw [coeff_mul, finset.sum_eq_zero],
  rintros ⟨i,j⟩ hij,
  by_cases hi : ↑i < order φ,
  { rw [coeff_of_lt_order φ i hi, zero_mul] },
  by_cases hj : ↑j < order ψ,
  { rw [coeff_of_lt_order ψ j hj, mul_zero] },
  rw not_lt at hi hj, rw finset.nat.mem_antidiagonal at hij,
  exfalso,
  apply ne_of_lt (lt_of_lt_of_le hn $ add_le_add' hi hj),
  rw [← enat.coe_add, hij]
end

/-- The order of the monomial `a*X^n` is infinite if `a = 0` and `n` otherwise.-/
lemma order_monomial (n : ℕ) (a : α) :
  order (monomial n a) = if a = 0 then ⊤ else n :=
begin
  split_ifs with h,
  { rw [h, order_eq_top, monomial_coeff_zero] },
  { rw [order_eq], split; intros i hi,
    { rw [enat.coe_inj] at hi, rwa [hi, coeff_monomial'] },
    { rw [enat.coe_lt_coe] at hi, rw [coeff_monomial, if_neg], exact ne_of_lt hi } }
end

/-- The order of the monomial `a*X^n` is `n` if `a ≠ 0`.-/
lemma order_monomial_of_ne_zero (n : ℕ) (a : α) (h : a ≠ 0) :
  order (monomial n a) = n :=
by rw [order_monomial, if_neg h]

end order_basic

section order_zero_ne_one
variables [nonzero_comm_ring α]

/-- The order of the formal power series `1` is `0`.-/
@[simp] lemma order_one : order (1 : power_series α) = 0 :=
order_monomial_of_ne_zero 0 (1:α) one_ne_zero

/-- The order of the formal power series `X` is `1`.-/
@[simp] lemma order_X : order (X : power_series α) = 1 :=
order_monomial_of_ne_zero 1 (1:α) one_ne_zero

/-- The order of the formal power series `X^n` is `n`.-/
@[simp] lemma order_X_pow (n : ℕ) : order ((X : power_series α)^n) = n :=
by { rw [X_pow_eq, order_monomial_of_ne_zero], exact one_ne_zero }

end order_zero_ne_one

section order_integral_domain
variables [integral_domain α]

/-- The order of the product of two formal power series over an integral domain
 is the sum of their orders.-/
lemma order_mul (φ ψ : power_series α) :
  order (φ * ψ) = order φ + order ψ :=
multiplicity.mul (X_prime)

end order_integral_domain

end power_series

namespace polynomial
open finsupp
variables {σ : Type*} {α : Type*} [comm_semiring α]

/-- The natural inclusion from polynomials into formal power series.-/
instance coe_to_power_series : has_coe (polynomial α) (power_series α) :=
⟨λ φ, power_series.mk $ λ n, coeff φ n⟩

@[simp, elim_cast] lemma coeff_coe (φ : polynomial α) (n) :
power_series.coeff n ↑φ = coeff φ n := rfl

@[reducible] def monomial (n : ℕ) (a : α) : polynomial α := single n a

@[simp, elim_cast] lemma coe_monomial (n : ℕ) (a : α) :
  (monomial n a : power_series α) = power_series.monomial n a :=
power_series.ext $ λ m,
begin
  rw [coeff_coe, power_series.coeff_monomial],
  calc coeff (monomial n a) m = if n = m then a else 0 : finsupp.single_apply
    ... = if m = n then a else 0 : by split_ifs with h₁ h₂; refl <|> subst m; contradiction
end

@[simp, elim_cast] lemma coe_zero : ((0 : polynomial α) : power_series α) = 0 := rfl

@[simp, elim_cast] lemma coe_one : ((1 : polynomial α) : power_series α) = 1 :=
coe_monomial _ _

@[simp, elim_cast] lemma coe_add (φ ψ : polynomial α) :
  ((φ + ψ : polynomial α) : power_series α) = φ + ψ := rfl

@[simp, elim_cast] lemma coe_mul (φ ψ : polynomial α) :
  ((φ * ψ : polynomial α) : power_series α) = φ * ψ :=
power_series.ext $ λ n,
by simp only [coeff_coe, power_series.coeff_mul, coeff_mul]

@[simp, elim_cast] lemma coe_C (a : α) :
  ((C a : polynomial α) : power_series α) = power_series.C a :=
coe_monomial _ _

@[simp, elim_cast] lemma coe_X :
  ((X : polynomial α) : power_series α) = power_series.X :=
coe_monomial _ _

namespace coe_to_mv_power_series

instance : is_semiring_hom (coe : polynomial α → power_series α) :=
{ map_zero := coe_zero,
  map_one := coe_one,
  map_add := coe_add,
  map_mul := coe_mul }

end coe_to_mv_power_series
end polynomial
