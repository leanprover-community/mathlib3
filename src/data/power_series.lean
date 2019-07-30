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

`trunc n φ` truncates a formal power series to the polynomial
that has the same coefficients as φ, for all m ≤ n, and 0 otherwise.

If the constant coefficient of a formal power series is invertible,
then this formal power series is invertible.

Formal power series over a local ring form a local ring.

## Implementation notes

In this file we define multivariate formal power series with coefficients in `α` as
mv_formal_power_series σ α := (σ →₀ ℕ) → α
Unfortunately there is not yet enough API to show that they are the completion
of the ring of multivariate polynomials. However, we provide most of the infrastructure
that is needed to do this. Once I-adic completion (topological or algebraic) is available
it should not be hard to fill in the details.

Formal power series in one variable are defined as
formal_power_series α := mv_formal_power_series unit α

This allows us to port a lot of proofs and properties
from the multivariate case to the single variable case.
However, it means that formal power series are indexed by (unit →₀ ℕ),
which is of course canonically isomorphic to ℕ.
We then build some glue to treat formal power series as if they are indexed by ℕ.
Occasionally this leads to proofs that are uglier than expected.

-/

/-- Multivariate formal power series, where `σ` is the index set of the variables
and `α` is the coefficient ring.-/
def mv_formal_power_series (σ : Type*) (α : Type*) := (σ →₀ ℕ) → α

namespace mv_formal_power_series
open finsupp
variables {σ : Type*} {α : Type*} [decidable_eq σ]

/-- The `n`th coefficient of a multivariate formal power series.-/
def coeff (n : σ →₀ ℕ) (φ : mv_formal_power_series σ α) := φ n

/-- Two multivariate formal power series are equal if all their coefficients are equal.-/
@[extensionality] lemma ext {φ ψ : mv_formal_power_series σ α} (h : ∀ n, coeff n φ = coeff n ψ) :
  φ = ψ :=
funext h

/-- Two multivariate formal power series are equal
 if and only if all their coefficients are equal.-/
lemma ext_iff {φ ψ : mv_formal_power_series σ α} :
  φ = ψ ↔ (∀ n, coeff n φ = coeff n ψ) :=
⟨λ h n, congr_arg (coeff n) h, ext⟩

section semiring
variables [semiring α]

/-- The `n`th monimial with coefficient `a` as multivariate formal power series.-/
def monomial (n : σ →₀ ℕ) (a : α) : mv_formal_power_series σ α :=
λ m, if m = n then a else 0

lemma coeff_monomial (m n : σ →₀ ℕ) (a : α) :
  coeff m (monomial n a) = if m = n then a else 0 := rfl

@[simp] lemma coeff_monomial' (n : σ →₀ ℕ) (a : α) :
  coeff n (monomial n a) = a := if_pos rfl

/-- The constant multivariate formal power series.-/
def C (a : α) : mv_formal_power_series σ α := monomial 0 a

lemma coeff_C (n : σ →₀ ℕ) (a : α) :
  coeff n (C a : mv_formal_power_series σ α) = if n = 0 then a else 0 := rfl

@[simp] lemma coeff_C_zero (a : α) : coeff 0 (C a : mv_formal_power_series σ α) = a :=
coeff_monomial' 0 a

@[simp] lemma monomial_zero (a : α) : (monomial 0 a : mv_formal_power_series σ α) = C a := rfl

/-- The variables of the multivariate formal power series ring.-/
def X (s : σ) : mv_formal_power_series σ α := monomial (single s 1) 1

lemma coeff_X (n : σ →₀ ℕ) (s : σ) :
  coeff n (X s : mv_formal_power_series σ α) = if n = (single s 1) then 1 else 0 := rfl

lemma coeff_X' (s t : σ) :
  coeff (single t 1) (X s : mv_formal_power_series σ α) = if t = s then 1 else 0 :=
by { simp only [coeff_X, single_right_inj one_ne_zero], split_ifs; refl }

@[simp] lemma coeff_X'' (s : σ) :
  coeff (single s 1) (X s : mv_formal_power_series σ α) = 1 :=
by rw [coeff_X', if_pos rfl]

section ring_structure
variables (σ) (α) (n : σ →₀ ℕ) (φ ψ : mv_formal_power_series σ α)

protected def zero : mv_formal_power_series σ α := λ n, 0

instance : has_zero (mv_formal_power_series σ α) := ⟨mv_formal_power_series.zero σ α⟩

@[simp] lemma coeff_zero : coeff n (0 : mv_formal_power_series σ α) = 0 := rfl

@[simp] lemma C_zero : (C 0 : mv_formal_power_series σ α) = 0 :=
ext $ λ n, if h : n = 0 then by simp [h] else by rw [coeff_C, if_neg h, coeff_zero]

protected def one : mv_formal_power_series σ α := C 1

instance : has_one (mv_formal_power_series σ α) := ⟨mv_formal_power_series.one σ α⟩

@[simp] lemma coeff_one :
  coeff n (1 : mv_formal_power_series σ α) = if n = 0 then 1 else 0 := rfl

@[simp] lemma coeff_one_zero : coeff 0 (1 : mv_formal_power_series σ α) = 1 :=
coeff_C_zero 1

@[simp] lemma C_one : (C 1 : mv_formal_power_series σ α) = 1 := rfl

protected def add (φ ψ : mv_formal_power_series σ α) : mv_formal_power_series σ α :=
λ n, coeff n φ + coeff n ψ

instance : has_add (mv_formal_power_series σ α) := ⟨mv_formal_power_series.add σ α⟩

variables {σ α}

@[simp] lemma coeff_add : coeff n (φ + ψ) = coeff n φ + coeff n ψ := rfl

protected lemma zero_add : (0 : mv_formal_power_series σ α) + φ = φ := ext $ λ n, zero_add _

protected lemma add_zero : φ + 0 = φ := ext $ λ n, add_zero _

protected lemma add_comm : φ + ψ = ψ + φ := ext $ λ n, add_comm _ _

protected lemma add_assoc (φ₁ φ₂ φ₃ : mv_formal_power_series σ α) :
  (φ₁ + φ₂) + φ₃ = φ₁ + (φ₂ + φ₃) := ext $ λ n, add_assoc _ _ _

@[simp] lemma monomial_add (n : σ →₀ ℕ) (a b : α) :
  (monomial n (a + b) : mv_formal_power_series σ α) = monomial n a + monomial n b :=
ext $ λ m, if h : m = n then by simp [h] else by simp [coeff_monomial, if_neg h]

@[simp] lemma C_add (a b : α) : (C (a + b) : mv_formal_power_series σ α) = C a + C b :=
monomial_add 0 a b

variables (σ α)

protected def mul (φ ψ : mv_formal_power_series σ α) : mv_formal_power_series σ α :=
λ n, (finsupp.antidiagonal n).support.sum (λ p, coeff p.1 φ * coeff p.2 ψ)

instance : has_mul (mv_formal_power_series σ α) := ⟨mv_formal_power_series.mul σ α⟩

variables {σ α}

lemma coeff_mul :
  coeff n (φ * ψ) = (finsupp.antidiagonal n).support.sum (λ p, coeff p.1 φ * coeff p.2 ψ) := rfl

@[simp] lemma C_mul (a b : α) : (C (a * b) : mv_formal_power_series σ α) = C a * C b :=
ext $ λ n,
begin
  rw [coeff_C, coeff_mul],
  split_ifs,
  { subst n, erw [antidiagonal_zero, finset.sum_singleton, coeff_C_zero, coeff_C_zero] },
  { rw finset.sum_eq_zero,
    rintros ⟨i,j⟩ hij,
    rw mem_antidiagonal_support at hij, rw [coeff_C, coeff_C],
    split_ifs; simp * at * }
end

protected lemma zero_mul : (0 : mv_formal_power_series σ α) * φ = 0 :=
ext $ λ n, by simp [coeff_mul]

protected lemma mul_zero : φ * 0 = 0 :=
ext $ λ n, by simp [coeff_mul]

protected lemma one_mul : (1 : mv_formal_power_series σ α) * φ = φ :=
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

protected lemma mul_add (φ₁ φ₂ φ₃ : mv_formal_power_series σ α) :
  φ₁ * (φ₂ + φ₃) = φ₁ * φ₂ + φ₁ * φ₃ :=
ext $ λ n, by simp only [coeff_mul, coeff_add, mul_add, finset.sum_add_distrib]

protected lemma add_mul (φ₁ φ₂ φ₃ : mv_formal_power_series σ α) :
  (φ₁ + φ₂) * φ₃ = φ₁ * φ₃ + φ₂ * φ₃ :=
ext $ λ n, by simp only [coeff_mul, coeff_add, add_mul, finset.sum_add_distrib]

protected lemma mul_assoc (φ₁ φ₂ φ₃ : mv_formal_power_series σ α) :
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

instance : semiring (mv_formal_power_series σ α) :=
{ mul_one := mv_formal_power_series.mul_one,
  one_mul := mv_formal_power_series.one_mul,
  add_assoc := mv_formal_power_series.add_assoc,
  zero_add := mv_formal_power_series.zero_add,
  add_zero := mv_formal_power_series.add_zero,
  add_comm := mv_formal_power_series.add_comm,
  mul_assoc := mv_formal_power_series.mul_assoc,
  mul_zero := mv_formal_power_series.mul_zero,
  zero_mul := mv_formal_power_series.zero_mul,
  left_distrib := mv_formal_power_series.mul_add,
  right_distrib := mv_formal_power_series.add_mul,
  .. mv_formal_power_series.has_zero σ α,
  .. mv_formal_power_series.has_one σ α,
  .. mv_formal_power_series.has_add σ α,
  .. mv_formal_power_series.has_mul σ α }

end ring_structure

instance C.is_semiring_hom : is_semiring_hom (C : α → mv_formal_power_series σ α) :=
{ map_zero := C_zero _ _,
  map_one := C_one _ _,
  map_add := C_add,
  map_mul := C_mul }

instance coeff.is_add_monoid_hom (n : σ →₀ ℕ) :
  is_add_monoid_hom (coeff n : mv_formal_power_series σ α → α) :=
{ map_zero := coeff_zero _ _ _,
  map_add := coeff_add n }

instance coeff_zero.is_semiring_hom :
  is_semiring_hom (coeff 0 : mv_formal_power_series σ α → α) :=
{ map_one := coeff_one_zero _ _,
  map_mul := λ φ ψ, by simp [coeff_mul, support_single_ne_zero],
  .. coeff.is_add_monoid_hom 0 }

/-- If a multivariate formal power series is invertible,
 then so is its constant coefficient.-/
lemma is_unit_coeff_zero (φ : mv_formal_power_series σ α) (h : is_unit φ) :
  is_unit (coeff 0 φ) :=
by { rcases h with ⟨φ, rfl⟩, exact ⟨units.map (coeff 0) φ, rfl⟩ }

instance : semimodule α (mv_formal_power_series σ α) :=
{ smul := λ a φ, C a * φ,
  one_smul := λ φ, one_mul _,
  mul_smul := λ a b φ, by simp only [C_mul, mul_assoc],
  smul_add := λ a φ ψ, mul_add _ _ _,
  smul_zero := λ a, mul_zero _,
  add_smul := λ a b φ, by simp only [C_add, add_mul],
  zero_smul := λ φ, by simp only [zero_mul, C_zero] }

section map
variables {β : Type*} {γ : Type*} [semiring β] [semiring γ]
variables (f : α → β) (g : β → γ)

/-- The map between multivariate formal power series induced by a map on the coefficients.-/
def map : mv_formal_power_series σ α → mv_formal_power_series σ β :=
λ φ n, f $ coeff n φ

@[simp] lemma map_id : (map (id : α → α) :
  mv_formal_power_series σ α → mv_formal_power_series σ α) = id := rfl

lemma map_comp : (map (g ∘ f) :
  mv_formal_power_series σ α → mv_formal_power_series σ γ) = map g ∘ map f := rfl

@[simp] lemma coeff_map (n) (φ : mv_formal_power_series σ α) :
  coeff n (map f φ) = f (coeff n φ) := rfl

variables [is_semiring_hom f] [is_semiring_hom g]

@[simp] lemma map_zero : map f (0 : mv_formal_power_series σ α) = 0 :=
ext $ λ n, is_semiring_hom.map_zero f

@[simp] lemma map_one : map f (1 : mv_formal_power_series σ α) = 1 :=
ext $ λ n, if h : n = 0
then by rw [coeff_map, h, coeff_one_zero, is_semiring_hom.map_one f, coeff_one_zero]
else by rw [coeff_map, coeff_one, if_neg h, is_semiring_hom.map_zero f, coeff_one, if_neg h]

@[simp] lemma map_add (φ ψ : mv_formal_power_series σ α) : map f (φ + ψ) = map f φ + map f ψ :=
ext $ λ n, by rw [coeff_map, coeff_add, is_semiring_hom.map_add f, coeff_add, coeff_map, coeff_map]

@[simp] lemma map_mul (φ ψ : mv_formal_power_series σ α) : map f (φ * ψ) = map f φ * map f ψ :=
ext $ λ n,
begin
  rw [coeff_map, coeff_mul, ← finset.sum_hom f, coeff_mul, finset.sum_congr rfl],
  rintros ⟨i,j⟩ hij, rw [is_semiring_hom.map_mul f, coeff_map, coeff_map]
end

instance map.is_semiring_hom :
  is_semiring_hom (map f : mv_formal_power_series σ α → mv_formal_power_series σ β) :=
{ map_zero := map_zero f,
  map_one := map_one f,
  map_add := map_add f,
  map_mul := map_mul f }

end map

end semiring

section comm_semiring
variables [comm_semiring α]
variables (φ ψ : mv_formal_power_series σ α)

protected lemma mul_comm : φ * ψ = ψ * φ :=
ext $ λ n, finset.sum_bij (λ p hp, p.swap)
  (λ p hp, swap_mem_antidiagonal_support hp)
  (λ p hp, mul_comm _ _)
  (λ p q hp hq H, by simpa using congr_arg prod.swap H)
  (λ p hp, ⟨p.swap, swap_mem_antidiagonal_support hp, p.swap_swap.symm⟩)

instance : comm_semiring (mv_formal_power_series σ α) :=
{ mul_comm := mv_formal_power_series.mul_comm,
  .. mv_formal_power_series.semiring }

section trunc
variables [decidable_eq α] (n : σ →₀ ℕ)

/-- The `n`th truncation of a multivariate formal power series to a multivariate polynomial -/
def trunc (φ : mv_formal_power_series σ α) : mv_polynomial σ α :=
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

lemma coeff_trunc (m) (φ : mv_formal_power_series σ α) :
  mv_polynomial.coeff m (trunc n φ) =
  if m ≤ n then coeff m φ else 0 := rfl

@[simp] lemma trunc_zero : trunc n (0 : mv_formal_power_series σ α) = 0 :=
mv_polynomial.ext _ _ $ λ m,
begin
  rw [coeff_trunc, coeff_zero, mv_polynomial.coeff_zero],
  split_ifs; refl
end

@[simp] lemma trunc_one : trunc n (1 : mv_formal_power_series σ α) = 1 :=
mv_polynomial.ext _ _ $ λ m,
begin
  rw [coeff_trunc, coeff_one],
  split_ifs with H H' H',
  { subst m, exact rfl },
  { symmetry, exact if_neg (ne.elim (ne.symm H')) },
  { symmetry, refine if_neg _,
    intro H', apply H, subst m, intro s, exact nat.zero_le _ }
end

@[simp] lemma trunc_C (a : α) : trunc n (C a) = mv_polynomial.C a :=
mv_polynomial.ext _ _ $ λ m,
begin
  rw [coeff_trunc, coeff_C, mv_polynomial.coeff_C],
  split_ifs with H; refl <|> try {simp * at *},
  exfalso, apply H, subst m, intro s, exact nat.zero_le _
end

@[simp] lemma trunc_add (φ ψ : mv_formal_power_series σ α) :
  trunc n (φ + ψ) = trunc n φ + trunc n ψ :=
mv_polynomial.ext _ _ $ λ m,
begin
  simp only [coeff_trunc, coeff_add, mv_polynomial.coeff_add],
  split_ifs with H, {refl}, {rw [zero_add]}
end

end trunc

end comm_semiring

section ring
variables [ring α]

protected def neg (φ : mv_formal_power_series σ α) :
  mv_formal_power_series σ α := λ n, - coeff n φ

instance : has_neg (mv_formal_power_series σ α) := ⟨mv_formal_power_series.neg⟩

@[simp] lemma coeff_neg (φ : mv_formal_power_series σ α) (n) : coeff n (- φ) = - coeff n φ := rfl

protected lemma add_left_neg (φ : mv_formal_power_series σ α) : (-φ) + φ = 0 :=
ext $ λ n, by rw [coeff_add, coeff_zero, coeff_neg, add_left_neg]

instance : ring (mv_formal_power_series σ α) :=
{ add_left_neg := mv_formal_power_series.add_left_neg,
  .. mv_formal_power_series.has_neg, .. mv_formal_power_series.semiring }

instance C.is_ring_hom : is_ring_hom (C : α → mv_formal_power_series σ α) :=
{ map_one := C_one _ _,
  map_add := C_add,
  map_mul := C_mul }

instance coeff.is_add_group_hom (n : σ →₀ ℕ) :
  is_add_group_hom (coeff n : mv_formal_power_series σ α → α) :=
{ map_add := coeff_add n }

instance map.is_ring_hom {β : Type*} [comm_ring β] (f : α → β) [is_ring_hom f] :
  is_ring_hom (map f : mv_formal_power_series σ α → mv_formal_power_series σ β) :=
{ .. map.is_semiring_hom f }

instance : module α (mv_formal_power_series σ α) :=
{ ..mv_formal_power_series.semimodule }

/-
The inverse of a multivariate formal power series is defined by
well-founded recursion on the coeffients of the inverse.
-/

/-- Auxiliary definition that unifies
 the totalised inverse formal power series `(_)⁻¹` and
 the inverse formal power series that depends on
 an inverse of the constant coefficient `inv_of_unit`.-/
protected def inv.aux (a : α) (φ : mv_formal_power_series σ α) : mv_formal_power_series σ α
| n := if n = 0 then a else
- a * n.antidiagonal.support.sum (λ (x : (σ →₀ ℕ) × (σ →₀ ℕ)),
    if h : x.2 < n then coeff x.1 φ * inv.aux x.2 else 0)
using_well_founded
{ rel_tac := λ _ _, `[exact ⟨_, finsupp.lt_wf σ⟩],
  dec_tac := tactic.assumption }

lemma coeff_inv_aux (n : σ →₀ ℕ) (a : α) (φ : mv_formal_power_series σ α) :
  coeff n (inv.aux a φ) = if n = 0 then a else
  - a * n.antidiagonal.support.sum (λ (x : (σ →₀ ℕ) × (σ →₀ ℕ)),
    if x.2 < n then coeff x.1 φ * coeff x.2 (inv.aux a φ) else 0) :=
by rw [coeff, inv.aux]; refl

/-- A multivariate formal power series is invertible if the constant coefficient is invertible.-/
def inv_of_unit (φ : mv_formal_power_series σ α) (u : units α) : mv_formal_power_series σ α :=
inv.aux (↑u⁻¹) φ

lemma coeff_inv_of_unit (n : σ →₀ ℕ) (φ : mv_formal_power_series σ α) (u : units α) :
  coeff n (inv_of_unit φ u) = if n = 0 then ↑u⁻¹ else
  - ↑u⁻¹ * n.antidiagonal.support.sum (λ (x : (σ →₀ ℕ) × (σ →₀ ℕ)),
    if x.2 < n then coeff x.1 φ * coeff x.2 (inv_of_unit φ u) else 0) :=
coeff_inv_aux n (↑u⁻¹) φ

@[simp] lemma coeff_zero_inv_of_unit (φ : mv_formal_power_series σ α) (u : units α) :
  coeff (0 : σ →₀ ℕ) (inv_of_unit φ u) = ↑u⁻¹ :=
by rw [coeff_inv_of_unit, if_pos rfl]

lemma mul_inv_of_unit (φ : mv_formal_power_series σ α) (u : units α) (h : coeff 0 φ = u) :
  φ * inv_of_unit φ u = 1 :=
ext $ λ n,
if H : n = 0 then
by erw [H, coeff_mul, coeff_one_zero, finsupp.antidiagonal_zero,
  finset.sum_singleton, coeff_zero_inv_of_unit, h, units.mul_inv]
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

instance : comm_ring (mv_formal_power_series σ α) :=
{ .. mv_formal_power_series.comm_semiring, .. mv_formal_power_series.ring }

instance : algebra α (mv_formal_power_series σ α) :=
{ to_fun := C,
  commutes' := λ _ _, mul_comm _ _,
  smul_def' := λ c p, rfl,
  .. mv_formal_power_series.module }

/-- Multivariate formal power series over a local ring form a local ring.-/
def is_local_ring (h : is_local_ring α) : is_local_ring (mv_formal_power_series σ α) :=
begin
  split,
  { intro H, apply ‹is_local_ring α›.1, simpa using congr_arg (coeff 0) H },
  { intro φ, have := ‹is_local_ring α›.2 (coeff 0 φ),
    cases this with h h; [left, right]; cases h with u h;
    { exact is_unit_of_mul_one _ _ (mul_inv_of_unit _ _ h) } }
end

-- TODO(jmc): once adic topology lands, show that this is complete

end comm_ring

section local_ring
variables {β : Type*} (f : α → β)
variables [local_ring α] [local_ring β] [is_local_ring_hom f]

instance : local_ring (mv_formal_power_series σ α) :=
local_of_is_local_ring $ is_local_ring ⟨zero_ne_one, local_ring.is_local⟩

instance map.is_local_ring_hom :
  is_local_ring_hom (map f : mv_formal_power_series σ α → mv_formal_power_series σ β) :=
{ map_nonunit :=
  begin
    rintros φ ⟨ψ, h⟩,
    replace h := congr_arg (coeff 0) h,
    rw coeff_map at h,
    have : is_unit (coeff 0 ↑ψ) := @is_unit_coeff_zero σ β _ _ (↑ψ) (is_unit_unit ψ),
    rw ← h at this,
    rcases is_unit_of_map_unit f _ this with ⟨c, hc⟩,
    exact is_unit_of_mul_one φ (inv_of_unit φ c) (mul_inv_of_unit φ c hc)
  end,
  .. map.is_ring_hom f }

end local_ring

section discrete_field
variables [discrete_field α]

protected def inv (φ : mv_formal_power_series σ α) : mv_formal_power_series σ α :=
inv.aux (coeff 0 φ)⁻¹ φ

instance : has_inv (mv_formal_power_series σ α) := ⟨mv_formal_power_series.inv⟩

lemma coeff_inv (n) (φ : mv_formal_power_series σ α) :
  coeff n (φ⁻¹) = if n = 0 then (coeff 0 φ)⁻¹ else
  - (coeff 0 φ)⁻¹ * n.antidiagonal.support.sum (λ (x : (σ →₀ ℕ) × (σ →₀ ℕ)),
    if x.2 < n then coeff x.1 φ * coeff x.2 (φ⁻¹) else 0) :=
coeff_inv_aux n _ φ

@[simp] lemma coeff_zero_inv (φ : mv_formal_power_series σ α) :
  coeff 0 (φ⁻¹) = (coeff 0 φ)⁻¹ :=
by rw [coeff_inv, if_pos rfl]

lemma inv_eq_zero {φ : mv_formal_power_series σ α} :
  φ⁻¹ = 0 ↔ coeff 0 φ = 0 :=
⟨λ h, by simpa using congr_arg (coeff 0) h,
 λ h, ext $ λ n, by { rw coeff_inv, split_ifs;
 simp only [h, mv_formal_power_series.coeff_zero, zero_mul, inv_zero, neg_zero] }⟩

@[simp] lemma inv_of_unit_eq (φ : mv_formal_power_series σ α) (h : coeff 0 φ ≠ 0) :
  inv_of_unit φ (units.mk0 _ h) = φ⁻¹ := rfl

@[simp] lemma inv_of_unit_eq' (φ : mv_formal_power_series σ α) (u : units α) (h : coeff 0 φ = u) :
  inv_of_unit φ u = φ⁻¹ :=
begin
  rw ← inv_of_unit_eq φ (h.symm ▸ u.ne_zero),
  congr' 1, rw [units.ext_iff], exact h.symm,
end

@[simp] protected lemma mul_inv (φ : mv_formal_power_series σ α) (h : coeff 0 φ ≠ 0) :
  φ * φ⁻¹ = 1 :=
by rw [← inv_of_unit_eq φ h, mul_inv_of_unit φ (units.mk0 _ h) rfl]

@[simp] protected lemma inv_mul (φ : mv_formal_power_series σ α) (h : coeff 0 φ ≠ 0) :
  φ⁻¹ * φ = 1 :=
by rw [mul_comm, φ.mul_inv h]

end discrete_field

end mv_formal_power_series

namespace mv_polynomial
open finsupp
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] [comm_semiring α]

/-- The natural inclusion from multivariate polynomials into multivariate formal power series.-/
def to_mv_formal_power_series (φ : mv_polynomial σ α) : mv_formal_power_series σ α :=
λ n, coeff n φ

@[simp] lemma to_mv_formal_power_series_coeff (φ : mv_polynomial σ α) (n) :
mv_formal_power_series.coeff n (φ.to_mv_formal_power_series) = coeff n φ := rfl

namespace to_mv_formal_power_series

instance :
  is_semiring_hom (to_mv_formal_power_series : mv_polynomial σ α → mv_formal_power_series σ α) :=
{ map_zero := mv_formal_power_series.ext $ λ n, by simp,
  map_one := mv_formal_power_series.ext $ λ n,
  begin
    rw [to_mv_formal_power_series_coeff, mv_formal_power_series.coeff_one],
    split_ifs; rw ← C_1; simp [-C_1, h],
    { rw ← ne_from_not_eq at h, simp [h.symm] }
  end,
  map_add := λ φ ψ, mv_formal_power_series.ext $ λ n, by simp,
  map_mul := λ φ ψ, mv_formal_power_series.ext $ λ n,
  by simp only [to_mv_formal_power_series_coeff, mv_formal_power_series.coeff_mul, coeff_mul] }

end to_mv_formal_power_series

end mv_polynomial

/-- Formal power series over the coefficient ring `α`.-/
def formal_power_series (α : Type*) := mv_formal_power_series unit α

namespace formal_power_series
open finsupp (single)
variable {α : Type*}

/-- The `n`th coefficient of a formal power series.-/
def coeff (n : ℕ) : formal_power_series α → α := mv_formal_power_series.coeff (single () n)

/-- Two formal power series are equal if all their coefficients are equal.-/
@[extensionality] lemma ext {φ ψ : formal_power_series α} (h : ∀ n, coeff n φ = coeff n ψ) :
  φ = ψ :=
mv_formal_power_series.ext $ λ n,
have this : n = single () (n ()), from (finsupp.unique_single n),
by convert h (n ())

/-- Two formal power series are equal if all their coefficients are equal.-/
lemma ext_iff {φ ψ : formal_power_series α} : φ = ψ ↔ (∀ n, coeff n φ = coeff n ψ) :=
⟨λ h n, congr_arg (coeff n) h, ext⟩

/-- Constructor for formal power series.-/
def mk (f : ℕ → α) : formal_power_series α := λ s, f (s ())

@[simp] lemma coeff_mk (n : ℕ) (f : ℕ → α) : coeff n (mk f) = f n := rfl

section comm_semiring
variable [comm_semiring α]

instance : comm_semiring (formal_power_series α) := by delta formal_power_series; apply_instance

/-- The `n`th monimial with coefficient `a` as formal power series.-/
def monomial (n : ℕ) : α → formal_power_series α := mv_formal_power_series.monomial (single () n)

/-- The constant formal power series.-/
def C : α → formal_power_series α := mv_formal_power_series.C

/-- The variable of the formal power series ring.-/
def X : formal_power_series α := mv_formal_power_series.X ()

lemma coeff_monomial (m n : ℕ) (a : α) :
  coeff m (monomial n a) = if m = n then a else 0 :=
calc coeff m (monomial n a) = _ : mv_formal_power_series.coeff_monomial _ _ _
    ... = if m = n then a else 0 :
by { simp only [finsupp.unique_single_eq_iff], split_ifs; refl }

lemma monomial_eq_mk (n : ℕ) (a : α) :
  monomial n a = mk (λ m, if m = n then a else 0) :=
ext $ λ m, coeff_monomial _ _ _

@[simp] lemma coeff_monomial' (n : ℕ) (a : α) :
  coeff n (monomial n a) = a := if_pos rfl

lemma coeff_C (n : ℕ) (a : α) :
  coeff n (C a : formal_power_series α) = if n = 0 then a else 0 :=
calc coeff n (C a) = _ : mv_formal_power_series.coeff_C _ _
    ... = if n = 0 then a else 0 :
by { simp only [finsupp.single_eq_zero], split_ifs; refl }

@[simp] lemma coeff_C_zero (a : α) : coeff 0 (C a) = a :=
coeff_monomial' 0 a

@[simp] lemma monomial_zero (a : α) : (monomial 0 a : formal_power_series α) = C a := rfl

lemma coeff_X (n : ℕ) :
  coeff n (X : formal_power_series α) = if n = 1 then 1 else 0 :=
calc coeff n (X : formal_power_series α) = _ : mv_formal_power_series.coeff_X _ _
    ... = if n = 1 then 1 else 0 :
by { simp only [finsupp.unique_single_eq_iff], split_ifs; refl }

@[simp] lemma coeff_X' : coeff 1 (X : formal_power_series α) = 1 :=
by rw [coeff_X, if_pos rfl]

@[simp] lemma coeff_zero (n : ℕ) : coeff n (0 : formal_power_series α) = 0 := rfl

@[simp] lemma C_zero : (C 0 : formal_power_series α) = 0 := mv_formal_power_series.C_zero _ _

@[simp] lemma coeff_one (n : ℕ) :
  coeff n (1 : formal_power_series α) = if n = 0 then 1 else 0 :=
calc coeff n (1 : formal_power_series α) = _ : mv_formal_power_series.coeff_one _ _ _
    ... = if n = 0 then 1 else 0 :
by { simp only [finsupp.single_eq_zero], split_ifs; refl }

@[simp] lemma coeff_one_zero : coeff 0 (1 : formal_power_series α) = 1 :=
coeff_C_zero 1

@[simp] lemma C_one : (C 1 : formal_power_series α) = 1 := rfl

@[simp] lemma coeff_add (n : ℕ) (φ ψ : formal_power_series α) :
  coeff n (φ + ψ) = coeff n φ + coeff n ψ := rfl

@[simp] lemma monomial_add (n : ℕ) (a b : α) :
  (monomial n (a + b) : formal_power_series α) = monomial n a + monomial n b :=
mv_formal_power_series.monomial_add _ _ _

@[simp] lemma C_add (a b : α) : (C (a + b) : formal_power_series α) = C a + C b :=
monomial_add 0 a b

lemma coeff_mul (n : ℕ) (φ ψ : formal_power_series α) :
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

@[simp] lemma C_mul (a b : α) : (C (a * b) : formal_power_series α) = C a * C b :=
mv_formal_power_series.C_mul _ _

instance C.is_semiring_hom : is_semiring_hom (C : α → formal_power_series α) :=
mv_formal_power_series.C.is_semiring_hom

instance coeff.is_add_monoid_hom (n : ℕ) :
  is_add_monoid_hom (coeff n : formal_power_series α → α) :=
{ map_zero := coeff_zero n,
  map_add := coeff_add n }

instance : semimodule α (formal_power_series α) :=
mv_formal_power_series.semimodule

section map
variables {β : Type*} {γ : Type*} [comm_semiring β] [comm_semiring γ]
variables (f : α → β) (g : β → γ)

/-- The map between formal power series induced by a map on the coefficients.-/
def map : formal_power_series α → formal_power_series β :=
mv_formal_power_series.map f

@[simp] lemma map_id : (map (id : α → α) :
  formal_power_series α → formal_power_series α) = id := rfl

lemma map_comp : (map (g ∘ f) :
  formal_power_series α → formal_power_series γ) = map g ∘ map f := rfl

@[simp] lemma coeff_map (n : ℕ) (φ : formal_power_series α) :
  coeff n (map f φ) = f (coeff n φ) := rfl

variables [is_semiring_hom f] [is_semiring_hom g]

@[simp] lemma map_zero : map f (0 : formal_power_series α) = 0 :=
mv_formal_power_series.map_zero f

@[simp] lemma map_one : map f (1 : formal_power_series α) = 1 :=
mv_formal_power_series.map_one f

@[simp] lemma map_add (φ ψ : formal_power_series α) : map f (φ + ψ) = map f φ + map f ψ :=
mv_formal_power_series.map_add f φ ψ

@[simp] lemma map_mul (φ ψ : formal_power_series α) : map f (φ * ψ) = map f φ * map f ψ :=
mv_formal_power_series.map_mul f φ ψ

instance map.is_semiring_hom :
  is_semiring_hom (map f : formal_power_series α → formal_power_series β) :=
mv_formal_power_series.map.is_semiring_hom f

end map

section trunc

variables [decidable_eq α] (n : ℕ)

/-- The `n`th truncation of a formal power series to a polynomial -/
def trunc (φ : formal_power_series α) : polynomial α :=
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

lemma coeff_trunc (m) (φ : formal_power_series α) :
  polynomial.coeff (trunc n φ) m = if m ≤ n then coeff m φ else 0 := rfl

@[simp] lemma trunc_zero : trunc n (0 : formal_power_series α) = 0 :=
polynomial.ext.2 $ λ m,
begin
  rw [coeff_trunc, coeff_zero, polynomial.coeff_zero],
  split_ifs; refl
end

@[simp] lemma trunc_one : trunc n (1 : formal_power_series α) = 1 :=
polynomial.ext.2 $ λ m,
begin
  rw [coeff_trunc, coeff_one],
  split_ifs with H H' H',
  { subst m, exact rfl },
  { symmetry, exact if_neg (ne.elim (ne.symm H')) },
  { symmetry, refine if_neg _,
    intro H', apply H, subst m, exact nat.zero_le _ }
end

@[simp] lemma trunc_C (a : α) : trunc n (C a) = polynomial.C a :=
polynomial.ext.2 $ λ m,
begin
  rw [coeff_trunc, coeff_C, polynomial.coeff_C],
  split_ifs with H; refl <|> try {simp * at *}
end

@[simp] lemma trunc_add (φ ψ : formal_power_series α) :
  trunc n (φ + ψ) = trunc n φ + trunc n ψ :=
polynomial.ext.2 $ λ m,
begin
  simp only [coeff_trunc, coeff_add, polynomial.coeff_add],
  split_ifs with H, {refl}, {rw [zero_add]}
end

end trunc

end comm_semiring

section comm_ring
variables [comm_ring α]

instance : comm_ring (formal_power_series α) := by delta formal_power_series; apply_instance

instance C.is_ring_hom : is_ring_hom (C : α → formal_power_series α) :=
mv_formal_power_series.C.is_ring_hom

instance map.is_ring_hom {β : Type*} [comm_ring β] (f : α → β) [is_ring_hom f] :
  is_ring_hom (map f : formal_power_series α → formal_power_series β) :=
{ .. map.is_semiring_hom f }

instance : module α (formal_power_series α) :=
mv_formal_power_series.module

instance : algebra α (formal_power_series α) :=
mv_formal_power_series.algebra

protected def inv.aux : α → formal_power_series α → formal_power_series α :=
mv_formal_power_series.inv.aux

lemma coeff_inv_aux (n : ℕ) (a : α) (φ : formal_power_series α) :
  coeff n (inv.aux a φ) = if n = 0 then a else
  - a * (finset.nat.antidiagonal n).sum (λ (x : ℕ × ℕ),
    if x.2 < n then coeff x.1 φ * coeff x.2 (inv.aux a φ) else 0) :=
begin
  rw [coeff, inv.aux, mv_formal_power_series.coeff_inv_aux],
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
def inv_of_unit (φ : formal_power_series α) (u : units α) : formal_power_series α :=
mv_formal_power_series.inv_of_unit φ u

lemma coeff_inv_of_unit (n : ℕ) (φ : formal_power_series α) (u : units α) :
  coeff n (inv_of_unit φ u) = if n = 0 then ↑u⁻¹ else
  - ↑u⁻¹ * (finset.nat.antidiagonal n).sum (λ (x : ℕ × ℕ),
    if x.2 < n then coeff x.1 φ * coeff x.2 (inv_of_unit φ u) else 0) :=
coeff_inv_aux n ↑u⁻¹ φ

@[simp] lemma coeff_zero_inv_of_unit (φ : formal_power_series α) (u : units α) :
  coeff (0 : ℕ) (inv_of_unit φ u) = ↑u⁻¹ :=
by rw [coeff_inv_of_unit, if_pos rfl]

lemma mul_inv_of_unit (φ : formal_power_series α) (u : units α) (h : coeff 0 φ = u) :
  φ * inv_of_unit φ u = 1 :=
mv_formal_power_series.mul_inv_of_unit φ u h

end comm_ring

section local_ring
variables [comm_ring α]

lemma is_local_ring (h : is_local_ring α) :
  is_local_ring (formal_power_series α) :=
mv_formal_power_series.is_local_ring h

end local_ring

section local_ring
variables {β : Type*} (f : α → β)
variables [local_ring α] [local_ring β] [is_local_ring_hom f]

instance : local_ring (formal_power_series α) :=
mv_formal_power_series.local_ring

instance map.is_local_ring_hom :
  is_local_ring_hom (map f : formal_power_series α → formal_power_series β) :=
mv_formal_power_series.map.is_local_ring_hom f

end local_ring

section discrete_field
variables [discrete_field α]

protected def inv : formal_power_series α → formal_power_series α :=
mv_formal_power_series.inv

instance : has_inv (formal_power_series α) := ⟨formal_power_series.inv⟩

lemma coeff_inv (n) (φ : formal_power_series α) :
  coeff n (φ⁻¹) = if n = 0 then (coeff 0 φ)⁻¹ else
  - (coeff 0 φ)⁻¹ * (finset.nat.antidiagonal n).sum (λ (x : ℕ × ℕ),
    if x.2 < n then coeff x.1 φ * coeff x.2 (φ⁻¹) else 0) :=
coeff_inv_aux n _ φ

@[simp] lemma coeff_zero_inv (φ : formal_power_series α) :
  coeff 0 (φ⁻¹) = (coeff 0 φ)⁻¹ :=
mv_formal_power_series.coeff_zero_inv φ

lemma inv_eq_zero {φ : formal_power_series α} :
  φ⁻¹ = 0 ↔ coeff 0 φ = 0 :=
mv_formal_power_series.inv_eq_zero

@[simp] lemma inv_of_unit_eq (φ : formal_power_series α) (h : coeff 0 φ ≠ 0) :
  inv_of_unit φ (units.mk0 _ h) = φ⁻¹ := rfl

@[simp] lemma inv_of_unit_eq' (φ : formal_power_series α) (u : units α) (h : coeff 0 φ = u) :
  inv_of_unit φ u = φ⁻¹ :=
mv_formal_power_series.inv_of_unit_eq' φ u h

@[simp] protected lemma mul_inv (φ : formal_power_series α) (h : coeff 0 φ ≠ 0) :
  φ * φ⁻¹ = 1 :=
mv_formal_power_series.mul_inv φ h

@[simp] protected lemma inv_mul (φ : formal_power_series α) (h : coeff 0 φ ≠ 0) :
  φ⁻¹ * φ = 1 :=
mv_formal_power_series.inv_mul φ h

end discrete_field

end formal_power_series

namespace formal_power_series
variable {α : Type*}

local attribute [instance] classical.prop_decidable

noncomputable theory
section order_basic
variables [comm_semiring α]

def order (φ : formal_power_series α) : enat :=
{ dom := ∃ i, φ.coeff i ≠ 0,
  get := nat.find }

lemma order_le (φ : formal_power_series α) (n : ℕ) (h : coeff n φ ≠ 0) :
  order φ ≤ n :=
begin
  have : (order φ).dom := ⟨n, h⟩,
  rw [← enat.coe_get this, enat.coe_le_coe],
  apply nat.find_min' this h
end

lemma coeff_of_lt_order (φ : formal_power_series α) (n : ℕ) (h: ↑n < order φ) :
  coeff n φ = 0 :=
by { rw ← not_le at h, by_contra H, exact h (order_le _ n H) }

lemma coeff_order (φ : formal_power_series α) (h : ∃ i, φ.coeff i ≠ 0) :
  coeff (φ.order.get h) φ ≠ 0 :=
nat.find_spec h

lemma order_ge_nat (φ : formal_power_series α) (n : ℕ) (h : ∀ i < n, coeff i φ = 0) :
  order φ ≥ n :=
begin
  by_contra H, rw not_le at H,
  have : (order φ).dom := enat.dom_of_le_some (le_of_lt H),
  rw [← enat.coe_get this, enat.coe_lt_coe] at H,
  exact coeff_order _ this (h _ H)
end

@[simp] lemma order_zero : order (0 : formal_power_series α) = ⊤ :=
roption.ext $ λ i,
by { split; rintro ⟨⟨n, h⟩, rfl⟩, exfalso, exact h (coeff_zero n) }

lemma order_eq_top {φ : formal_power_series α} :
  φ.order = ⊤ ↔ φ = 0 :=
begin
  split,
  { intro h, replace h : _ = false := congr_arg roption.dom h,
    ext n, by_contra H, exact eq.rec_on h ⟨n, H⟩ },
  { rintro rfl, exact order_zero }
end

lemma order_ge (φ : formal_power_series α) (n : enat) (h : ∀ i : ℕ, ↑i < n → coeff i φ = 0) :
  order φ ≥ n :=
begin
  induction n using enat.cases_on,
  { show _ ≤ _, rw [lattice.top_le_iff, order_eq_top],
    ext i, exact h _ (enat.coe_lt_top i) },
  { apply order_ge_nat, simpa only [enat.coe_lt_coe] using h }
end

lemma order_eq_nat {φ : formal_power_series α} {n : ℕ} :
  order φ = n ↔ (coeff n φ ≠ 0) ∧ (∀ i:ℕ, i < n → coeff i φ = 0) :=
begin
  split,
  { intro hn, have : (order φ).dom, { rw hn, exact trivial },
    have R := coeff_of_lt_order φ,
    simp only [hn, enat.coe_lt_coe] at R,
    rw [← enat.coe_get this, enat.coe_inj] at hn, subst hn,
    exact ⟨coeff_order φ this, R⟩ },
  { rintro ⟨h₁, h₂⟩,
    exact le_antisymm (order_le _ _ h₁) (order_ge_nat _ _ h₂) }
end

lemma order_eq {φ : formal_power_series α} {n : enat} :
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
lemma order_add_ge (φ ψ : formal_power_series α) :
  order (φ + ψ) ≥ order φ ⊓ order ψ :=
order_ge _ _ $ λ n hn,
begin
  rw lattice.lt_inf_iff at hn,
  rw [coeff_add, coeff_of_lt_order φ n hn.1, coeff_of_lt_order ψ n hn.2, zero_add]
end

private lemma order_add_of_order_eq.aux (φ ψ : formal_power_series α)
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
lemma order_add_of_order_eq (φ ψ : formal_power_series α) (h : order φ ≠ order ψ) :
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
lemma order_mul_ge (φ ψ : formal_power_series α) :
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

/-- The order of the monomial a*X^n.-/
lemma order_monomial (n : ℕ) (a : α) :
  order (monomial n a) = if a = 0 then ⊤ else n :=
begin
  split_ifs with h,
  { rw [h, order_eq_top], sorry },
  { rw [order_eq], split; intros i hi,
    { rw [enat.coe_inj] at hi, rwa [hi, coeff_monomial'] },
    { rw [enat.coe_lt_coe] at hi, rw [coeff_monomial, if_neg], exact ne_of_lt hi } }
end

/-- The order of the monomial a*X^n is n if a ≠ 0.-/
lemma order_monomial_of_ne_zero (n : ℕ) (a : α) (h : a ≠ 0) :
  order (monomial n a) = n :=
by rw [order_monomial, if_neg h]

end order_basic

section order_zero_ne_one
variables [nonzero_comm_ring α]

/-- The order of the formal power series 1 is 0.-/
@[simp] lemma order_one : order (1 : formal_power_series α) = 0 :=
order_eq_nat.2 $ by simp

/-- The order of the formal power series X is 1.-/
@[simp] lemma order_X : order (X : formal_power_series α) = 1 :=
begin
  rw [← X_eq],
-- order_eq_nat.2 $ ⟨one_ne_zero, λ i hi,
--   rw [coeff_X, if_neg],
--   have := nat.eq_zero_of_le_zero (nat.le_of_succ_le_succ hi),
--   subst i, exact zero_ne_one
end⟩

end order_zero_ne_one

section order_integral_domain
variables [integral_domain α]

/-- The order of the product of two formal power series over an integral domain
 is the sum of their orders.-/
lemma order_mul (φ ψ : formal_power_series α) :
  order (φ * ψ) = order φ + order ψ :=
begin
  apply le_antisymm _ (order_mul_ge _ _),
  generalize h : order φ + order ψ = n,
  induction n using enat.cases_on, { exact lattice.le_top },
  apply order_le,
  have H : (order φ + order ψ).dom, { rw h, exact trivial },
  rw [← enat.coe_get H, enat.coe_inj, enat.get_add] at h,
  rw [coeff_mul, finset.sum_eq_single ((order φ).get H.1, (order ψ).get H.2)],
  { exact mul_ne_zero (coeff_order _ H.1) (coeff_order _ H.2) },
  { rintro ⟨i,j⟩ hij hne,
    by_cases hi : ↑i < order φ,
    { rw [coeff_of_lt_order φ i hi, zero_mul] },
    by_cases hj : ↑j < order ψ,
    { rw [coeff_of_lt_order ψ j hj, mul_zero] },
    rw not_lt at hi hj,
    exfalso,
    by_cases hi' : ↑i ≤ order φ,
    { apply hne, have := le_antisymm hi hi',
      rw [← enat.coe_get H.1, enat.coe_inj] at this, subst this,
      rw [finset.nat.mem_antidiagonal, ← h] at hij,
      simpa using add_left_cancel hij },
    { rw not_le at hi',
      rw [← enat.coe_get H.1] at hi hi',
      rw [← enat.coe_get H.2] at hj,
      simp only [enat.coe_le_coe, enat.coe_lt_coe] at hi hj hi',
      have := add_lt_add_of_lt_of_le hi' hj,
      rw finset.nat.mem_antidiagonal at hij,
      rw h at this, exact ne_of_lt this hij.symm } },
  { intro H', exfalso, apply H', rwa [finset.nat.mem_antidiagonal] }
end

end order_integral_domain

end formal_power_series

namespace polynomial
open finsupp
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] [comm_semiring α]

/-- The natural inclusion from polynomials into formal power series.-/
def to_formal_power_series (φ : polynomial α) : formal_power_series α :=
formal_power_series.mk $ λ n, coeff φ n

@[simp] lemma to_formal_power_series_coeff (φ : polynomial α) (n) :
formal_power_series.coeff n (φ.to_formal_power_series) = coeff φ n := rfl

namespace to_formal_power_series

instance : is_semiring_hom (to_formal_power_series : polynomial α → formal_power_series α) :=
{ map_zero := formal_power_series.ext $ λ n, by simp,
  map_one := formal_power_series.ext $ λ n,
  begin
    rw [to_formal_power_series_coeff, polynomial.coeff_one, formal_power_series.coeff_one],
    split_ifs; refl <|> simp * at *
  end,
  map_add := λ φ ψ, formal_power_series.ext $ λ n, by simp,
  map_mul := λ φ ψ, formal_power_series.ext $ λ n,
  by simp only [to_formal_power_series_coeff, formal_power_series.coeff_mul, coeff_mul] }

end to_formal_power_series

end polynomial
