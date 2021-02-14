/-
Copyright (c) 2021 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Filippo A. E. Nuccio
-/
import data.mv_polynomial
import linear_algebra.std_basis
import ring_theory.ideal.operations
import ring_theory.multiplicity
import ring_theory.algebra_tower
import tactic.linarith

/-!
# Formal power series

This file defines (multivariate) formal power series
and develops the basic properties of these objects.

A formal power series is to a polynomial like an infinite sum is to a finite sum.

We provide the natural inclusion from polynomials to formal power series.

## Generalities

The file starts with setting up the (semi)ring structure on multivariate power series.

`trunc n φ` truncates a formal power series to the polynomial
that has the same coefficients as `φ`, for all `m ≤ n`, and `0` otherwise.

If the constant coefficient of a formal power series is invertible,
then this formal power series is invertible.

Formal power series over a local ring form a local ring.

## Formal power series in one variable

We prove that if the ring of coefficients is an integral domain,
then formal power series in one variable form an integral domain.

The `order` of a formal power series `φ` is the multiplicity of the variable `X` in `φ`.

If the coefficients form an integral domain, then `order` is a valuation
(`order_mul`, `le_order_add`).

## Implementation notes

In this file we define multivariate formal power series with
variables indexed by `σ` and coefficients in `R` as
`mv_power_series σ R := (σ →₀ ℕ) → R`.
Unfortunately there is not yet enough API to show that they are the completion
of the ring of multivariate polynomials. However, we provide most of the infrastructure
that is needed to do this. Once I-adic completion (topological or algebraic) is available
it should not be hard to fill in the details.

Formal power series in one variable are defined as
`power_series R := mv_power_series unit R`.

This allows us to port a lot of proofs and properties
from the multivariate case to the single variable case.
However, it means that formal power series are indexed by `unit →₀ ℕ`,
which is of course canonically isomorphic to `ℕ`.
We then build some glue to treat formal power series as if they are indexed by `ℕ`.
Occasionally this leads to proofs that are uglier than expected.
-/

-- namespace maxumal

-- def maxumal := ℕ

-- def equiv_to_nat : maxumal ≃ nat := equiv.refl _

-- notation `𝕄` := maxumal
-- notation `℘` := equiv_to_nat.to_fun
-- notation `℘⁻¹` := equiv_to_nat.symm
-- notation `𝟘` := ℘⁻¹ 0

-- instance : inhabited 𝕄 := ⟨𝟘⟩
-- instance : has_zero 𝕄 := ⟨𝟘⟩
-- instance : nontrivial 𝕄 := ⟨⟨𝟘, ℘⁻¹ 1, nat.zero_ne_one⟩⟩

-- lemma nat.max_zero : ∀ {m : ℕ}, max m 0 = m :=
-- begin
--   intro a,
--   rw [max_comm a 0, nat.zero_max],
-- end

-- instance : add_comm_monoid 𝕄 :=
-- { add := begin change ℕ → ℕ → ℕ, use max, end,
--   add_assoc := by convert max_assoc,
--   zero := 𝟘,
--   zero_add := λ _, nat.zero_max,
--   add_zero := λ _, nat.max_zero,
--   add_comm := max_comm, }

-- def sub_left_maxumal : 𝕄 × 𝕄 → 𝕄
-- | (𝕜₁, 𝕜₂) := ℘⁻¹ (℘ (𝕜₁ + 𝕜₂) - ℘ 𝕜₁)
-- notation `μ` := sub_left_maxumal

-- @[simp] lemma zero_sub_left : ∀ (𝕜 : 𝕄), μ (𝟘, 𝕜) = 𝕜 := sorry
-- @[simp] lemma sub_left_zero : ∀ (𝕜 : 𝕄 ), μ (𝕜, 𝟘) = 𝟘 := sorry

-- #eval ℘ ((℘⁻¹ 8) + (℘⁻¹ 5))
-- #eval μ (℘⁻¹ 8, ℘⁻¹ 5)
-- #eval μ (℘⁻¹ 5, ℘⁻¹ 8)
-- -- #eval equiv_to_nat.to_fun ((equiv_to_nat.inv_fun 5) + (equiv_to_nat.inv_fun 8))
-- -- #eval equiv_to_nat.to_fun ((equiv_to_nat.inv_fun 3) + (equiv_to_nat.inv_fun 5))
-- -- #eval equiv_to_nat.to_fun ((equiv_to_nat.inv_fun 2) + (equiv_to_nat.inv_fun 0))

-- end maxumal
noncomputable theory
open_locale classical big_operators

namespace punctured_power_series

/-- Multivariate formal power series, where `σ` is the index set of the variables
and `R` is the coefficient ring.-/
-- def mv_power_series (σ : Type*) (R : Type*) := (σ →₀ ℕ) →
def punctured_power_series (R : Type*) := ℕ × (ℕ → R)

-- open finsupp
variables {R : Type*}

instance [inhabited R]       : inhabited       (punctured_power_series R) := ⟨(default _, (λ _, default _))⟩
instance [has_zero R]        : has_zero        (punctured_power_series R) := ⟨(0, 0)⟩
instance [nontrivial R]      : nontrivial      (punctured_power_series R) := nontrivial_prod_left

@[ext, simp] lemma ext_punctured_power_series (F₁ F₂ : punctured_power_series R) :
  F₁ = F₂ ↔ F₁.1 = F₂.1 ∧ F₁.2 = F₂.2 :=
begin
  split,
    {intro h,
    split,
    apply_fun prod.fst at h,
    assumption,
    apply_fun prod.snd at h,
    assumption },
  { intro h,
    ext,
    exact h.1,
    simp only * at * },
end

def shift_fun {R : Type*} [has_zero R]: ℕ → (ℕ → R) → (ℕ → R)
| (k) := λ f, λ n, if (n : ℤ) < k then (0 : R) else f (n - k)

@[simp] lemma shift_fun_by_zero [has_zero R] (f : ℕ → R) : shift_fun 0 f = f := rfl

-- @[simp] lemma shift_fun_eq_iff [has_zero R] (f₁ f₂ : ℕ → R) (k : ℕ) :
-- shift_fun k f₁ = shift_fun k f₂ ↔ f₁ = f₂ :=
-- begin
--   split,
--   { intro h,
--     funext,
--     apply congr_fun h x,

--   },
--   {sorry,},
--   -- ext,
-- end

@[simp] lemma shift_fun_assoc [has_zero R] (f : ℕ → R) (k₁ k₂ : ℕ):
  shift_fun k₁ (shift_fun k₂ f) = shift_fun (k₁ + k₂) f :=
  begin
    ext,
    dsimp [shift_fun],
    show ite (↑x < ↑k₁) 0 (ite (↑(x - k₁) < ↑k₂) 0 (f (x - k₁ - k₂))) =
      ite (↑x < ↑k₁ + ↑k₂) 0 (f (x - (k₁ + k₂))),
    by_cases hx₁ : ↑x < ↑k₁,
    { have this : (x : ℤ) < ↑k₁ + ↑k₂,
      apply lt_add_of_lt_of_nonneg hx₁ (int.coe_nat_nonneg k₂),
      rw [if_pos hx₁, if_pos this], },
    {by_cases hx₂ : (x : ℤ) < k₂,
      { have hx₁₂ : ↑x < ↑k₁ + ↑k₂,
        apply lt_add_of_nonneg_of_lt (int.of_nat_nonneg k₁) hx₂,
        have hx₁₂' : (x - k₁ : ℤ) < ↑k₂,
        apply int.sub_left_lt_of_lt_add hx₁₂,
        rw [if_neg hx₁, if_pos hx₁₂, int.coe_nat_sub, if_pos hx₁₂'],
        rw [int.coe_nat_lt, not_lt] at hx₁,
        exact hx₁ },
      { by_cases hx₁₂ : (x : ℤ) < k₁ + k₂,
        { have hx₁₂' : (x - k₁ : ℤ) < ↑k₂,
          apply int.sub_left_lt_of_lt_add hx₁₂,--uguale a riga 171
          rw [if_neg hx₁, if_pos hx₁₂, int.coe_nat_sub, if_pos hx₁₂'],
          rw [int.coe_nat_lt, not_lt] at hx₁, --uguale a riga 173
          exact hx₁ },--uguale a riga 174
          have hx₁₂' : ¬ (x - k₁ : ℤ) < ↑k₂,
          simp only [not_lt, int.coe_nat_lt] at *,
          rw [← int.coe_nat_add, int.coe_nat_le, add_comm, nat.add_le_to_le_sub] at hx₁₂,
          rw [← int.coe_nat_sub, int.coe_nat_le],
          exact hx₁₂,
          repeat {exact hx₁},
          rw [if_neg hx₁, if_neg hx₁₂, int.coe_nat_sub, if_neg hx₁₂', nat.sub_sub],
          rw [int.coe_nat_lt, not_lt] at hx₁, --uguale a riga 173
          exact hx₁} },--uguale a riga 174
end
-- @[simp] lemma eq_shift_fun [has_neg R] [has_zero R] (𝕜₁ 𝕜₂ : 𝕄) (f₁ f₂ : ℕ → R) :
--   𝕜₁ = 𝕜₂ → shift_fun 𝕜₁ f₁ = shift_fun 𝕜₂ f₂ ↔ f₁ = f₂ := sorry



/-We only consider the case where R is a commutative additive monoid, for simplicity-/
variable [add_comm_monoid R]

-- lemma cst_shift_fun' (𝕜 : 𝕄) : shift_fun 𝕜 (function.const : ℕ → R) = (0 : ℕ → R) := sorry,

@[simp] lemma shift_fun_of_zero (k : ℕ) : shift_fun k (0 : ℕ → R) = (0 : ℕ → R) :=
begin
      funext,
      dsimp [shift_fun],
      by_cases h: (n : ℤ) < k,
      rw if_pos h,
      tauto,
      rw if_neg h,
      tauto,
end

@[simp] lemma shift_neg [ring R] (f : ℕ → R) (k : ℕ) :
  shift_fun k (-f) = - (shift_fun k f) :=
begin
  ext,
  rw pi.neg_apply,
  dsimp [shift_fun],
  by_cases h : (x : ℤ) < ↑k,
  { repeat {rw if_pos h},
    exact neg_zero.symm },
  { repeat {rw if_neg h},
    rw pi.neg_apply },
end

@[simp] lemma shift_fun_add (k : ℕ) (f₁ f₂ : ℕ → R) : shift_fun k (f₁ + f₂) =
  shift_fun k f₁ + shift_fun k f₂ :=
begin
  funext,
  rw pi.add_apply,
  dsimp [shift_fun],
  by_cases h: (n : ℤ) < k,
  { repeat {rw if_pos h},
    ring },
  { repeat {rw if_neg h},
    rw pi.add_apply },
end

def add : (punctured_power_series R) → (punctured_power_series R) → (punctured_power_series R) :=
begin
  rintros ⟨k₁, f₁⟩ ⟨k₂, f₂⟩,
  exact ⟨k₁ + k₂, shift_fun k₂ f₁ + shift_fun k₁ f₂⟩,
end

lemma add_assoc : ∀ (F₁ F₂ F₃ : punctured_power_series R), punctured_power_series.add (punctured_power_series.add  F₁ F₂) F₃ =
 punctured_power_series.add F₁ (punctured_power_series.add F₂ F₃) :=
begin
  rintros ⟨k₁, f₁⟩ ⟨k₂, f₂⟩ ⟨k₃, f₃⟩,
  ext,
  apply nat.add_assoc,
  dsimp [punctured_power_series.add],
  show (shift_fun k₃ (shift_fun k₂ f₁ + shift_fun k₁ f₂) + shift_fun (k₁ + k₂) f₃) x
    = (shift_fun (k₂ + k₃) f₁ + shift_fun k₁ (shift_fun k₃ f₂ + shift_fun k₂ f₃)) x,
  simp only [pi.add_apply, shift_fun_assoc, shift_fun_add] at *,
  rw [← add_assoc, add_comm k₃ k₂, add_comm k₃ k₁],
end

lemma zero_add : ∀ (F: punctured_power_series R), punctured_power_series.add 0 F = F :=
begin
  rintro ⟨k, f⟩,
  ext,
  apply nat.zero_add,
  show (shift_fun k 0 + shift_fun 0 f) x = f x,
  simp only [shift_fun_of_zero, zero_add, shift_fun_by_zero],
end

lemma add_zero : ∀ (F: punctured_power_series R), punctured_power_series.add F 0 = F :=
begin
  rintro ⟨k, f⟩,
  ext,
  apply nat.add_zero,
  show (shift_fun 0 f + shift_fun k 0) x = f x,
  simp only [shift_fun_of_zero, add_zero, shift_fun_by_zero],
end

lemma add_comm : ∀ (F G: punctured_power_series R), punctured_power_series.add F G =
  punctured_power_series.add G F :=
begin
  rintro ⟨k₁, f₁⟩ ⟨k₂, f₂⟩,
  ext,
  apply nat.add_comm,
  show (shift_fun k₂ f₁ + shift_fun k₁ f₂) x =
    (shift_fun k₁ f₂ + shift_fun k₂ f₁) x,
  simp only [pi.add_apply, add_comm],
end

instance : add_comm_monoid (punctured_power_series R) :=
{ add := punctured_power_series.add,
  add_assoc := punctured_power_series.add_assoc,
  zero := (0, 0),
  zero_add := punctured_power_series.zero_add,
  add_zero := punctured_power_series.add_zero,
  add_comm := punctured_power_series.add_comm }

@[simp] lemma add_fst {F₁ F₂ : punctured_power_series R} :
 (F₁ + F₂).fst = F₁.fst + F₂.fst :=
begin
  rcases F₁ with ⟨k₁, _⟩,
  rcases F₂ with ⟨k₂, _⟩,
  apply rfl,
end

@[simp] lemma add_snd {F₁ F₂ : punctured_power_series R} :
 (F₁ + F₂).snd = shift_fun F₂.fst F₁.snd + shift_fun F₁.fst F₂.snd :=
begin
  rcases F₁ with ⟨_, f₁⟩,
  rcases F₂ with ⟨_, f₂⟩,
  apply rfl,
end

-- #print punctured_power_series.add
-- def a : ℕ → ℤ := λ n, 4*n+3
-- def b : ℕ → ℤ := λ n, 1-2*n
-- -- def 𝕜₁ : 𝕄 := ℘⁻¹ 1
-- -- def 𝕜₂ : 𝕄 := ℘⁻¹ 3

-- def F₁ : punctured_power_series ℤ := (1, a)
-- def F₂ : punctured_power_series ℤ := (3, b)
-- #eval a 5
-- #eval (F₁ + F₂).snd 9
/-The right answers are
0 → 0, 1 → 1, 2 → -1, 3 → 0, 4 → 2, 5 → 4, 6 → 6, 7 → 8, 8 → 10, 9 → 12

def F₃ := (𝟘, b) --check!
--/

-- def eqv_punctured_old (F₁ F₂ : punctured_power_series R) : Prop :=
-- ∃ ℓ₁₂ ℓ₂₁ : 𝕄, F₁ + (ℓ₁₂, 0) = F₂ + (ℓ₂₁, 0)

def eqv_punctured (F₁ F₂ : punctured_power_series R) : Prop :=
∃ ℓ₁₂ ℓ₂₁ : ℕ, F₁ + (ℓ₁₂, 0) = F₂ + (ℓ₂₁, 0)

lemma eqv_punctured_rfl: reflexive (@eqv_punctured R _) :=
begin
  intros F,
  use [0, 0],
end

lemma eqv_punctured_symm : symmetric (@eqv_punctured R _) :=
begin
  rintros F₁ F₂ ⟨ℓ₁₂, ℓ₂₁, h⟩,
  use [ℓ₂₁, ℓ₁₂],
  exact h.symm,
end

lemma eqv_punctured_trans : transitive (@eqv_punctured R _) :=
begin
  rintros F₁ F₂ F₃ ⟨ℓ₁₂, ℓ₂₁, h₁₂⟩ ⟨ℓ₂₃, ℓ₃₂, h₂₃⟩,
  use [ℓ₁₂ + ℓ₂₃, ℓ₂₁ + ℓ₃₂],
  simp only [*, add_zero, add_snd, ext_punctured_power_series,
   shift_fun_of_zero, add_fst] at *,
  split,
  { rw [← nat.add_assoc, h₁₂.1, nat.add_assoc, nat.add_comm ℓ₂₁ ℓ₂₃,
    ← nat.add_assoc, h₂₃.1],
    ring },
  { ring,
    replace h₁₂ : shift_fun ℓ₁₂ F₁.snd = shift_fun ℓ₂₁ F₂.snd,
    { convert h₁₂.right; ring },
    replace h₂₃ : shift_fun ℓ₂₃ F₂.snd = shift_fun ℓ₃₂ F₃.snd,
    { convert h₂₃.right; ring },
    repeat {rw ← shift_fun_assoc},
    rw [← h₂₃, shift_fun_assoc F₂.snd ℓ₂₁ ℓ₂₃, nat.add_comm ℓ₂₁ ℓ₂₃,
      ← shift_fun_assoc F₂.snd ℓ₂₃ ℓ₂₁, ← h₁₂],
    repeat {rw shift_fun_assoc},
    rw nat.add_comm ℓ₁₂ ℓ₂₃ },
end

theorem eqv_punctured.is_equivalence :  equivalence (@eqv_punctured R _) :=
 ⟨eqv_punctured_rfl, eqv_punctured_symm, eqv_punctured_trans⟩

def eqv_punctured.add_con (R : Type*) [add_comm_monoid R] : add_con (punctured_power_series R) :=
begin
  use @eqv_punctured R _,
  exact eqv_punctured.is_equivalence,
  rintros ⟨k₁, f₁⟩ ⟨k₂, f₂⟩ ⟨k₃, f₃⟩ ⟨k₄, f₄⟩ ⟨ℓ₁₂, ℓ₂₁, h₁₂⟩ ⟨ℓ₃₄, ℓ₄₃, h₃₄⟩,
  rw eqv_punctured,
  use [ℓ₁₂ + ℓ₃₄, ℓ₂₁ + ℓ₄₃],
  simp only [*, add_zero, add_snd, ext_punctured_power_series,
    shift_fun_assoc, shift_fun_of_zero, shift_fun_add, add_fst] at *,
  split,
  { rwa [nat.add_assoc, nat.add_comm ℓ₁₂ ℓ₃₄, ← nat.add_assoc k₃ ℓ₃₄ ℓ₁₂, h₃₄.1,
      nat.add_comm, nat.add_assoc, ← nat.add_comm k₁ ℓ₁₂, h₁₂.left],
    ring, },
  { have h₁₂': shift_fun ℓ₁₂ f₁ = shift_fun ℓ₂₁ f₂,
    { convert h₁₂.right; ring },
    have h₃₄': shift_fun ℓ₃₄ f₃ = shift_fun ℓ₄₃ f₄,
    { convert h₃₄.right; ring },
    ring,
    repeat {rw nat.add_assoc},
    rw [nat.add_comm, ← shift_fun_assoc, h₁₂', nat.add_comm ℓ₃₄ k₁,
     ← nat.add_assoc ℓ₁₂ k₁ ℓ₃₄, ← shift_fun_assoc f₃, h₃₄'],
    repeat {rw shift_fun_assoc},
    rw [nat.add_comm ℓ₄₃ k₄, ← h₃₄.left, nat.add_comm ℓ₁₂ k₁, h₁₂.left],
    ring },
end

def laurent_series (R : Type*) [add_comm_monoid R]:= (eqv_punctured.add_con R).quotient
instance inhabited : inhabited (laurent_series R) :=
  begin
    use (eqv_punctured.add_con R).mk' 0,
  end

instance : add_comm_monoid (laurent_series R) := (eqv_punctured.add_con R).add_comm_monoid

instance : has_coe (punctured_power_series R) (laurent_series R) :=
⟨@quotient.mk _ (eqv_punctured.add_con R).to_setoid⟩

variables {S : Type*} [comm_ring S]


noncomputable theory
open classical
-- open_locale classical


-- lemma add_comm : ∀ (F G: punctured_power_series R), punctured_power_series.add F G =
--   punctured_power_series.add G F :=
-- begin
--   rintros ⟨𝕜₁, f₁⟩ ⟨𝕜₂, f₂⟩,
--   ext,
--   apply max_comm,
--   show (shift_fun (μ (𝕜₁, 𝕜₂)) f₁ + shift_fun (μ (𝕜₂, 𝕜₁)) f₂) x =
--     (shift_fun (μ (𝕜₂, 𝕜₁)) f₂ + shift_fun (μ (𝕜₁, 𝕜₂)) f₁) x,
--   simp only [pi.add_apply] at *,
--   apply add_comm,
-- end
-- #check (eqv_punctured.add_con S).mk'

def lift_neg : (punctured_power_series S) → (laurent_series S) :=
  λ ⟨k, f⟩, (eqv_punctured.add_con S).mk' ⟨k, -f⟩

lemma cong_neg : ∀ (F₁ F₂ : punctured_power_series S),  eqv_punctured F₁ F₂ →
  lift_neg F₁ = lift_neg F₂ :=
begin
  rintros ⟨k₁, f₁⟩ ⟨k₂, f₂⟩ ⟨ℓ₁₂, ℓ₂₁, h⟩,
  dsimp [lift_neg],
  rw ext_punctured_power_series at h,
  replace h : eqv_punctured (k₁, -f₁) (k₂, -f₂),
  { use [ℓ₁₂, ℓ₂₁],
    ext,
    exact h.1,
    simp * at * },
  apply (add_con.eq (eqv_punctured.add_con S)).mpr h,
end

def lift_sub : (punctured_power_series S) → (punctured_power_series S) → (laurent_series S) :=
  λ ⟨k₁, f₁⟩ ⟨k₂, f₂⟩, (eqv_punctured.add_con S).mk' ⟨k₁ + k₂, f₁ - f₂⟩

lemma cong_sub : ∀ (F₁ F₂ G₁ G₂: punctured_power_series S),  eqv_punctured F₁ G₁ →
  eqv_punctured.add_con S F₂ G₂ → lift_sub F₁ F₂ = lift_sub G₁ G₂ :=
begin
  rintros ⟨k₁, f₁⟩ ⟨m₁, g₁⟩ ⟨k₂, f₂⟩ ⟨m₂, g₂⟩ ⟨μ₁₂, μ₂₁, h₁⟩ ⟨θ₁₂, θ₂₁, h₂⟩,
  dsimp [lift_sub],
  rw ext_punctured_power_series at h₁,
  rw ext_punctured_power_series at h₂,
  have h : eqv_punctured (k₁ + m₁, f₁ - g₁) (k₂ + m₂, f₂ - g₂),
  { rw eqv_punctured,
    use [μ₁₂ + θ₁₂, μ₂₁ + θ₂₁],
    ext,
    { simp only [*, add_zero, add_snd, shift_fun_of_zero, add_fst] at *,
      sorry },
    { simp only [*, add_zero, add_snd, shift_fun_of_zero, add_fst,
      pi.add_apply] at *,
      have h₁' : shift_fun μ₁₂ f₁ = shift_fun μ₂₁ g₁, sorry,
      have h₂' : shift_fun θ₁₂ f₂ = shift_fun θ₂₁ g₂, sorry,
      rw nat.add_comm,
      rw ← shift_fun_assoc,
      rw sub_eq_add_neg,
      rw shift_fun_add,
      rw h₁',
      rw nat.add_comm,
      rw ← shift_fun_assoc,
      rw sub_eq_add_neg,
      -- rw shift_fun_add μ₂₁ g₁ (-g₂),
      rw ← h₁',
      sorry,
  }},
  -- have
  -- sorry,
  -- rw lift_sub,
  apply (add_con.eq (eqv_punctured.add_con S)).mpr h,
end

instance : comm_ring (laurent_series S) :=
{ add := λ F₁ F₂, F₁ + F₂,
  add_assoc := sorry,
  zero := (eqv_punctured.add_con S).mk' 0,
  zero_add := λ _, by simp,
  add_zero := λ _, by simp,
  -- begin
  --   rintros F,
  --   obtain ⟨f⟩ : ∃ f : (punctured_power_series S),
  --     (eqv_punctured.add_con S).mk' f = F,
  -- end,
  neg := λ F, add_con.lift_on F lift_neg cong_neg,

  -- begin
  --   let φ : (punctured_power_series S) → (punctured_power_series S) :=
  -- λ ⟨𝕜, f⟩, ⟨𝕜, -f⟩,
  --   use (add_con.lift_on (laurent_series S) φ),
  -- end,
  --               -- refine quot.lift_on _ _ _,
  --               -- use (punctured_power_series S),
  --               -- -- rintros F₁ F₂,
  --               -- rintros ⟨𝕜₁, f₁⟩ ⟨𝕜₂,f₂⟩,
  --               -- use eqv_punctured ⟨𝕜₁, f₁⟩ ⟨𝕜₂,f₂⟩,
  --               -- --  (λ (𝕜, f), (𝕜, -f))⟩,
  --               -- -- begin

  --               --   intro G,
  --               -- have hG : ∃ f : (punctured_power_series S),
  --               --     (eqv_punctured.add_con S).mk' f = G,
  --               -- apply add_con.mk'_surjective,
  --               -- rcases some hG with ⟨𝕜, g⟩,
  --               -- use (eqv_punctured.add_con S).mk' ⟨𝕜, -g⟩,
  --               -- end,
  sub :=  λ F₁ F₂, add_con.lift_on₂ F₁ F₂ lift_sub cong_sub,
  -- begin
  --           intros F₁ F₂,
  --                 have hF₁ : ∃ f₁ : (punctured_power_series S),
  --                   (eqv_punctured.add_con S).mk' f₁ = F₁,
  --                 apply add_con.mk'_surjective,
  --                 have hF₂ : ∃ f₂ : (punctured_power_series S),
  --                   (eqv_punctured.add_con S).mk' f₂ = F₂,
  --                 apply add_con.mk'_surjective,
  --                 rcases some hF₁ with ⟨𝕜₁, f₁⟩,
  --                 rcases some hF₂ with ⟨𝕜₂, f₂⟩,
  --                 use (eqv_punctured.add_con S).mk' (μ (𝕜₁, 𝕜₂), f₁-f₂),
  --               end,
  sub_eq_add_neg := --by simp,
                begin intros F₁ F₂,
                rcases F₁,
                rcases F₂,
                rcases F₁ with ⟨𝕜₁, f₁⟩,
                rcases F₂ with ⟨𝕜₂, f₂⟩,
                suffices this : f₁ - f₂ = f₁ + -f₂,
                simp * at *,
                sorry,
                sorry,
                end,
  add_left_neg := sorry,
  add_comm := sorry,
  mul := sorry,
  mul_assoc := sorry,
  one := sorry,
  one_mul := sorry,
  mul_one := sorry,
  left_distrib := sorry,
  right_distrib := sorry,
  mul_comm := sorry }

-- end add_comm_monoid
end punctured_power_series--SEE PAG 166 tpil



-- instance [add_group R]       : add_group       (punctured_power_series R) := pi.add_group
-- instance [add_comm_group R]  : add_comm_group  (punctured_power_series R) := pi.add_comm_group


-- instance {A} [semiring R] [add_comm_monoid A] [semimodule R A] :
--   semimodule R (punctured_power_series R) := pi.semimodule _ _ _

-- example  {A} [semiring R] [add_comm_monoid A] [semimodule R A] :
--   semimodule R (ℕ → A) :=
--   begin
--     refine pi.semimodule ℕ (λ (_ : ℕ), A) R
--   end

-- example  {A} [semiring R] [add_comm_monoid A] [semimodule R A] :
--   semimodule R (ℕ × A) :=
-- begin

-- end

-- end punctured_power_series
