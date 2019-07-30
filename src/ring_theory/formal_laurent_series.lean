/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/

import data.power_series

local attribute [instance] classical.prop_decidable

noncomputable theory

/-- Formal Laurent series over the coefficient ring.-/
structure formal_laurent_series (α : Type*) [comm_semiring α] := mk' ::
(num       : formal_power_series α)
(int_order : ℤ)
(zero'     : num.coeff 0 = 0 → num = 0 ∧ int_order = 0)

namespace formal_laurent_series
variables {α : Type*} [comm_semiring α]

/-- The `n`th coefficient of a formal Laurent series.-/
def coeff (n : ℤ) (φ : formal_laurent_series α) : α :=
if φ.int_order ≤ n then φ.num.coeff (n - φ.int_order).nat_abs else 0

protected def zero : formal_laurent_series α :=
{ num := 0,
  int_order := 0,
  zero' := λ h, ⟨rfl, rfl⟩ }

instance : has_zero (formal_laurent_series α) := ⟨formal_laurent_series.zero⟩

@[simp] lemma coeff_zero (n : ℤ) : coeff n (0 : formal_laurent_series α) = 0 :=
if h : (0 : ℤ) ≤ n then
calc coeff n 0 = (0 : formal_laurent_series α).num.coeff _ : if_pos h
  ... = 0 : formal_power_series.coeff_zero _
else if_neg h

/-- The order of a formal Laurent series.-/
def order (φ : formal_laurent_series α) : with_top ℤ :=
if φ = 0 then ⊤ else φ.int_order

@[simp] lemma order_zero : order (0 : formal_laurent_series α) = ⊤ :=
if_pos rfl

/-- Coefficients with index less than the order of a formal Laurent series are zero. -/
lemma coeff_of_lt_order (φ : formal_laurent_series α) (i : ℤ) (h : ↑i < φ.order) :
  φ.coeff i = 0 :=
if H : φ.int_order ≤ i then
begin
  delta coeff, rw if_pos H,
  delta order at h, split_ifs at h with h' h',
  { rw [h', show num (0 : formal_laurent_series α) = 0, from rfl, formal_power_series.coeff_zero] },
  { rw [with_top.coe_lt_coe, lt_iff_not_ge] at h, exfalso, exact h H }
end
else if_neg H

lemma coeff_int_order_ne_zero (φ : formal_laurent_series α) (h : φ ≠ 0) :
  φ.coeff φ.int_order ≠ 0 :=
begin
  simp [coeff, if_pos (le_refl _)],
  intro H, apply h, cases φ.zero' H, cases φ, congr, assumption'
end

lemma int_order_eq (φ : formal_laurent_series α) (h : φ ≠ 0) (i : ℤ) :
  φ.int_order = i ↔ coeff i φ ≠ 0 ∧ (∀ j < i, coeff j φ = 0) :=
begin
  split,
  { rintro rfl, refine ⟨coeff_int_order_ne_zero φ h, _⟩,
    intros j hj, apply coeff_of_lt_order,
    rwa [order, if_neg h, with_top.coe_lt_coe] },
  { rintro ⟨h₁,h₂⟩, delta coeff at h₁, split_ifs at h₁ with H H,
    { apply le_antisymm H, by_contra H', apply h,
      rw not_le at H', specialize h₂ _ H', rw [coeff, if_pos (le_refl _)] at h₂,
      cases (φ.zero' _), { cases φ, congr, assumption' },
      simpa using h₂ },
    { exfalso, exact h₁ rfl } }
end

lemma order_eq (φ : formal_laurent_series α) (i : with_top ℤ) :
  φ.order = i ↔ (∀ i' : ℤ, i = i' → coeff i' φ ≠ 0) ∧ (∀ j : ℤ, ↑j < i → coeff j φ = 0) :=
begin
  split,
  { rintros rfl, refine ⟨_, coeff_of_lt_order φ⟩,
    intros i h, rw order at h, split_ifs at h with H H,
    { exfalso, exact option.no_confusion h },
    { rw with_top.coe_eq_coe at h, subst i, exact coeff_int_order_ne_zero φ H } },
  { rintros ⟨h₁, h₂⟩, rw order, split_ifs with H H,
    { subst H, cases i, {refl}, { exfalso, apply h₁ i rfl (coeff_zero i) } },
    { cases i,
      { exfalso, apply coeff_int_order_ne_zero _ H,
        exact h₂ _ (with_top.coe_lt_top (φ.int_order)) },
      { erw [with_top.coe_eq_coe, int_order_eq _ H],
        exact ⟨h₁ _ rfl, λ j hj, h₂ j (with_top.coe_lt_coe.2 hj)⟩ } } }
end

/-- Two formal Laurent series are equal if all their coefficients are equal.-/
@[extensionality] lemma ext {φ ψ : formal_laurent_series α} (h : ∀ n, coeff n φ = coeff n ψ) :
  φ = ψ :=
begin
  by_cases H : ψ = 0,
  { subst H, cases φ with φ i hφi, cases hφi _ with h₁ h₂,
    { congr, assumption' },
    { specialize h i, rw [coeff_zero, coeff, if_pos (le_refl _)] at h, simpa using h } },
  { have H' : φ.int_order = ψ.int_order,
    { rw int_order_eq,
      { split,
        { rw h, exact coeff_int_order_ne_zero ψ H },
        { intros j hj, rw h, apply coeff_of_lt_order,
          rwa [order, if_neg H, with_top.coe_lt_coe] } },
      { rintro rfl, apply H,
        cases ψ.zero' _, { cases ψ, congr, assumption' },
        specialize h ψ.int_order, convert h.symm,
        { rw [coeff, if_pos (le_refl _)], simp },
        { exact (coeff_zero _).symm } } },
    cases φ with φ i hφ, cases ψ with ψ j hψ, congr,
    { ext, specialize h (n + i), dsimp only [coeff] at h H',
      rw [add_sub_cancel, H', add_sub_cancel] at h,
      rw if_pos (le_add_of_nonneg_left $ int.coe_zero_le n) at h,
      rw if_pos (le_add_of_nonneg_left $ int.coe_zero_le n) at h,
      simpa using h },
    { exact H' } }
end

/-- Two formal Laurent series are equal
 if and only if all their coefficients are equal.-/
lemma ext_iff {φ ψ : formal_laurent_series α} :
  φ = ψ ↔ (∀ n, coeff n φ = coeff n ψ) :=
⟨λ h n, congr_arg (coeff n) h, ext⟩

lemma order_eq_top {φ : formal_laurent_series α} :
  φ.order = ⊤ ↔ φ = 0 :=
begin
  split,
  { rw order, split_ifs, { exact λ _, h },
    intro H, exfalso, exact option.no_confusion H },
  { rintro rfl, exact order_zero }
end

end formal_laurent_series

namespace formal_laurent_series
variables {α : Type*} [comm_semiring α]

/-- `mk φ i` constructs the formal Laurent series `φ / X^i`. -/
def mk (φ : formal_power_series α) (i : ℤ) : formal_laurent_series α :=
if h : φ.order.dom then
let n := φ.order.get h in
{ num := formal_power_series.mk $ λ k, φ.coeff (n + k),
  int_order := n - i,
  zero' := λ H, false.elim $ formal_power_series.coeff_order _ h (by simpa using H) }
else 0

lemma int_order_mk (φ : formal_power_series α) (i : ℤ) :
  (mk φ i).int_order = if h : φ.order.dom then φ.order.get h - i else 0 :=
by { rw mk, split_ifs with h; refl }

lemma coeff_mk (n : ℤ) (φ : formal_power_series α) (i : ℤ) :
  coeff n (mk φ i) =
  if h : φ.order.dom then
    if 0 ≤ n + i then φ.coeff (n + i).nat_abs else 0
  else 0 :=
begin
  split_ifs with h H,
  { rw [mk, dif_pos h, coeff], split_ifs with h';
    dsimp [-sub_eq_add_neg] at *; rw ← sub_nonneg at h',
    { refine congr_arg (λ i, φ.coeff i) _,
      rw [← int.coe_nat_inj', int.coe_nat_add,
        ← int.eq_nat_abs_of_zero_le h', ← int.eq_nat_abs_of_zero_le H],
      simp [-add_comm] },
    { refine (φ.coeff_of_lt_order _ _).symm,
      rw [← enat.coe_get h, enat.coe_lt_coe, ← int.coe_nat_lt,
        ← int.eq_nat_abs_of_zero_le H],
      rwa [not_le, sub_eq_add_neg, neg_sub, add_sub, sub_lt, sub_zero] at h' } },
  { rw [coeff, int_order_mk, dif_pos h], apply dif_neg, intro H', apply H,
    have : (0 : ℤ) ≤ φ.order.get h := int.coe_zero_le _,
    rw sub_le_iff_le_add at H', exact le_trans this H' },
  { rw [mk, dif_neg h, coeff_zero] }
end

def of (φ : formal_power_series α) : formal_laurent_series α := mk φ 0

lemma coeff_of (n : ℤ) (φ : formal_power_series α) :
  coeff n (of φ) = if 0 ≤ n then φ.coeff n.nat_abs else 0 :=
begin
  rw [of, coeff_mk], simp only [add_zero],
  by_cases h : φ.order.dom,
  { rw dif_pos h, split_ifs; refl },
  { rw dif_neg h, split_ifs,
    { suffices : φ = 0, { rw [this, formal_power_series.coeff_zero] },
      erw [← formal_power_series.order_eq_top, roption.eq_none_iff'], exact h },
    { refl } }
end

def C (a : α) : formal_laurent_series α := of (formal_power_series.C a)

@[simp] lemma of_C (a : α) : of (formal_power_series.C a) = C a := rfl

lemma coeff_C (n : ℤ) (a : α) :
  coeff n (C a) = if n = 0 then a else 0 :=
begin
  rw [C, coeff_of],
  by_cases h : 0 ≤ n,
  { rw if_pos h, split_ifs with H,
    { rw [H, int.nat_abs_zero, formal_power_series.coeff_C_zero] },
    { rw [formal_power_series.coeff_C, if_neg],
      exact int.nat_abs_ne_zero_of_ne_zero H } },
  { rw [if_neg h, if_neg], rintro rfl, exact h (le_refl 0) }
end

def one : formal_laurent_series α := of 1

instance : has_one (formal_laurent_series α) := ⟨one⟩

@[simp] lemma C_one : C (1 : α) = 1 := rfl

@[simp] lemma of_one : of (1 : formal_power_series α) = 1 := rfl

lemma coeff_one (n : ℤ) :
  coeff n (1 : formal_laurent_series α) = if n = 0 then 1 else 0 :=
by rw [← C_one, coeff_C]

def monomial (n : ℤ) (a : α) : formal_laurent_series α :=
mk (formal_power_series.C a) n

@[simp] lemma of_monomial (n : ℕ) (a : α) :
  of (formal_power_series.monomial n a) = monomial n a :=
begin

end

def mul (φ ψ : formal_laurent_series α) : formal_laurent_series α :=
mk (φ.num * ψ.num) (φ.int_order + ψ.int_order)



end formal_laurent_series


#exit

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
