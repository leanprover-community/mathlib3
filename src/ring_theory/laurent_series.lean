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

@[simp] lemma shift_fun_neg [ring R] (f : ℕ → R) (k : ℕ) :
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

/-- The `n`th coefficient of a punctured power series.-/
def punctured_power_series.coeff (n : ℤ) : (punctured_power_series R) → R :=
 λ ⟨k, f⟩, if n < - k then 0 else f (int.nat_abs (n + k))

end punctured_power_series

namespace laurent_series
open punctured_power_series

def laurent_series (R : Type*) [add_comm_monoid R]:= (eqv_punctured.add_con R).quotient

variables {R : Type*} [add_comm_monoid R]

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

def lift_neg : (punctured_power_series.punctured_power_series S) → (laurent_series S) :=
  λ ⟨k, f⟩, (punctured_power_series.eqv_punctured.add_con S).mk' ⟨k, -f⟩

lemma cong_neg : ∀ (F₁ F₂ : punctured_power_series.punctured_power_series S),
  punctured_power_series.eqv_punctured F₁ F₂ → lift_neg F₁ = lift_neg F₂ :=
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

lemma neg_add_cong_zero (k : ℕ) (f: ℕ → S) : eqv_punctured ((k, -f) + (k, f)) 0 :=
begin
  use [0, k + k],
  simp * at *,
end


def lift_sub : (punctured_power_series S) → (punctured_power_series S) → (laurent_series S) :=
  λ ⟨k₁, f₁⟩ ⟨k₂, f₂⟩, (eqv_punctured.add_con S).mk' ⟨k₁ + k₂, shift_fun k₂ f₁ - shift_fun k₁ f₂⟩

lemma cong_sub {S : Type*} [comm_ring S] : ∀ (F₁ F₂ G₁ G₂: punctured_power_series S), eqv_punctured.add_con S F₁ G₁ →
  eqv_punctured.add_con S F₂ G₂ → lift_sub F₁ F₂ = lift_sub G₁ G₂ :=
begin
  rintros ⟨k₁, f₁⟩ ⟨k₂, f₂⟩ ⟨m₁, g₁⟩  ⟨m₂, g₂⟩ ⟨ℓ₁₂, ℓ₂₁, hf⟩ ⟨μ₁₂, μ₂₁, hg⟩,
  dsimp [lift_sub],
  rw ext_punctured_power_series at hf,
  rw ext_punctured_power_series at hg,
  have h : eqv_punctured (k₁ + k₂, shift_fun k₂ f₁ - shift_fun k₁ f₂)
    (m₁ + m₂, shift_fun m₂ g₁ - shift_fun m₁ g₂),
  { rw eqv_punctured,
    use [ℓ₁₂ + μ₁₂, ℓ₂₁ + μ₂₁],
    ext,
    { simp only [*, punctured_power_series.add_zero, add_snd, shift_fun_of_zero, add_fst] at *,
      rw [← nat.add_left_comm, nat.add_assoc k₁ k₂ μ₁₂, hg.left,
        nat.add_assoc m₁, nat.add_comm m₂ (ℓ₂₁ + μ₂₁), nat.add_assoc ℓ₂₁,
        ← nat.add_assoc m₁, ← hf.left],
      ring },
    { simp only [*, sub_eq_add_neg, punctured_power_series.add_zero, add_snd, pi.add_apply,
        pi.neg_apply, shift_fun_assoc, shift_fun_of_zero, shift_fun_add,
        add_fst, shift_fun_neg, add_monoid.add_zero] at *,
      rw nat.add_assoc,
      rw nat.add_comm ℓ₁₂,
      rw ← shift_fun_assoc f₁ (μ₁₂ + k₂) ℓ₁₂,
      rw hf.right,
      rw nat.add_assoc _ μ₁₂ k₁,
      rw nat.add_comm μ₁₂ k₁,
      rw ← nat.add_assoc _ k₁ μ₁₂,
      rw ← shift_fun_assoc f₂ (ℓ₁₂ + k₁) μ₁₂,
      rw [hg.right],
      simp only [shift_fun_assoc],
      have hf₁ : μ₁₂ + k₂ + ℓ₂₁ = ℓ₂₁ + μ₂₁ + m₂,
      { rw [nat.add_comm μ₁₂ k₂, hg.left],
        ring },
      have hg₁ : ℓ₁₂ + k₁ + μ₂₁ = ℓ₂₁ + μ₂₁ + m₁,
      { rw [nat.add_comm ℓ₁₂ k₁, hf.left],
        ring },
      rwa [hf₁, hg₁] }},
  apply (add_con.eq (eqv_punctured.add_con S)).mpr h,
end

def punctured_power_series.mul : (punctured_power_series S) → (punctured_power_series S) → (punctured_power_series S) :=
λ ⟨k₁, f₁⟩ ⟨k₂, f₂⟩, ⟨k₁ + k₂, λ n, ∑ p in (finset.nat.antidiagonal n), f₁ p.2 * f₂ p.1⟩

def lift_mul : (punctured_power_series S) → (punctured_power_series S) → (laurent_series S) :=
  λ F₁ F₂, (eqv_punctured.add_con S).mk' (punctured_power_series.mul F₁ F₂)


lemma lift_mul_assoc : ∀ (F₁ F₂ F₃ : punctured_power_series.punctured_power_series S), punctured_power_series.mul
    (punctured_power_series.mul F₁ F₂ ) F₃ = punctured_power_series.mul F₁ (punctured_power_series.mul F₂ F₃) :=
begin
  intros,
  sorry,
end

lemma cong_mul {S : Type*} [comm_ring S] : ∀ (F₁ F₂ G₁ G₂: punctured_power_series S), eqv_punctured.add_con S F₁ G₁ →
  punctured_power_series.eqv_punctured.add_con S F₂ G₂ → lift_mul F₁ F₂ = lift_mul G₁ G₂ :=
begin
  rintros ⟨k₁, f₁⟩ ⟨k₂, f₂⟩ ⟨m₁, g₁⟩  ⟨m₂, g₂⟩ ⟨ℓ₁₂, ℓ₂₁, hf⟩ ⟨μ₁₂, μ₂₁, hg⟩,
  dsimp [lift_mul],
  rw ext_punctured_power_series at hf,
  rw ext_punctured_power_series at hg,
  sorry,
  -- have h : eqv_punctured (k₁ + k₂, shift_fun k₂ f₁ - shift_fun k₁ f₂)
  --   (m₁ + m₂, shift_fun m₂ g₁ - shift_fun m₁ g₂),
  -- { rw eqv_punctured,
  --   use [ℓ₁₂ + μ₁₂, ℓ₂₁ + μ₂₁],
  --   ext,
  --   { simp only [*, add_zero, add_snd, shift_fun_of_zero, add_fst] at *,
  --     rw [← nat.add_left_comm, nat.add_assoc k₁ k₂ μ₁₂, hg.left,
  --       nat.add_assoc m₁, nat.add_comm m₂ (ℓ₂₁ + μ₂₁), nat.add_assoc ℓ₂₁,
  --       ← nat.add_assoc m₁, ← hf.left],
  --     ring },
  --   { simp only [*, sub_eq_add_neg, add_zero, add_snd, pi.add_apply,
  --       pi.neg_apply, shift_fun_assoc, shift_fun_of_zero, shift_fun_add,
  --       add_fst, shift_fun_neg, add_monoid.add_zero] at *,
  --     rw nat.add_assoc,
  --     rw nat.add_comm ℓ₁₂,
  --     rw ← shift_fun_assoc f₁ (μ₁₂ + k₂) ℓ₁₂,
  --     rw hf.right,
  --     rw nat.add_assoc _ μ₁₂ k₁,
  --     rw nat.add_comm μ₁₂ k₁,
  --     rw ← nat.add_assoc _ k₁ μ₁₂,
  --     rw ← shift_fun_assoc f₂ (ℓ₁₂ + k₁) μ₁₂,
  --     rw [hg.right],
  --     simp only [shift_fun_assoc],
  --     have hf₁ : μ₁₂ + k₂ + ℓ₂₁ = ℓ₂₁ + μ₂₁ + m₂,
  --     { rw [nat.add_comm μ₁₂ k₂, hg.left],
  --       ring },
  --     have hg₁ : ℓ₁₂ + k₁ + μ₂₁ = ℓ₂₁ + μ₂₁ + m₁,
  --     { rw [nat.add_comm ℓ₁₂ k₁, hf.left],
  --       ring },
  --     rwa [hf₁, hg₁] }},
  -- apply (add_con.eq (eqv_punctured.add_con S)).mpr h,
end

instance : comm_ring (laurent_series S) :=
{ add := λ F₁ F₂, F₁ + F₂,
  add_assoc :=  λ F₁ F₂ F₃, quotient.induction_on₃' F₁ F₂ F₃
                $ λ _ _ _, congr_arg coe $ punctured_power_series.add_assoc _ _ _,
  zero := (punctured_power_series.eqv_punctured.add_con S).mk' 0,
  zero_add := λ _, by simp,
  add_zero := λ _, by simp,
  neg := λ F, add_con.lift_on F lift_neg cong_neg,
  sub :=  λ F₁ F₂, add_con.lift_on₂ F₁ F₂ lift_sub cong_sub,
  sub_eq_add_neg := begin
                      intros G₁ G₂,
                      apply quotient.induction_on₂' G₁ G₂,
                      rintros ⟨k₁, f₁⟩  ⟨k₂, f₂⟩,
                      apply congr_arg quotient.mk',
                      ext,
                      apply rfl,
                      simp only [add_snd, pi.add_apply, pi.neg_apply,
                        pi.sub_apply, shift_fun_neg],
                      ring,
                    end,
  add_left_neg := begin
                intro G,
                apply quotient.induction_on' G,
                rintro ⟨k, f⟩,
                apply (add_con.eq (eqv_punctured.add_con S)).mpr (neg_add_cong_zero k f),
                  end,
  add_comm := begin
                intros G₁ G₂,
                apply quotient.induction_on₂' G₁ G₂,
                rintros F₁ F₂,
                apply congr_arg quotient.mk',
                exact punctured_power_series.add_comm F₁ F₂,
              end,
  mul := λ F₁ F₂, add_con.lift_on₂ F₁ F₂ lift_mul cong_mul,
  mul_assoc := λ F₁ F₂ F₃, quotient.induction_on₃' F₁ F₂ F₃
              $ λ _ _ _, congr_arg coe $ lift_mul_assoc _ _ _,
  one := (eqv_punctured.add_con S).mk' (0, λ n, if n = 0 then 1 else 0),
  one_mul := begin
              intro G,
              apply quotient.induction_on' G,
              rintro ⟨k, f⟩,
              apply congr_arg quotient.mk',
              ext,
              apply nat.zero_add,
              dsimp [punctured_power_series.mul],
              induction x with n hn,
              { rw [finset.nat.antidiagonal_zero, finset.sum_singleton,
                  if_pos],
                apply one_mul,
                apply rfl },
              { rw finset.nat.antidiagonal_succ,
                sorry },
            end,
  mul_one := sorry,
  left_distrib := begin sorry, end,
  right_distrib := begin sorry, end,
  mul_comm := sorry }

/-- The `n`th coefficient of a laurent power series.-/
lemma cong_coeff (n : ℤ) (F₁ F₂ : punctured_power_series S) :
  eqv_punctured.add_con S F₁ F₂ → punctured_power_series.coeff n F₁ = punctured_power_series.coeff n F₂ :=
begin
  sorry,
end


def coeff (n : ℤ) : (laurent_series S) → S :=
begin
  let coeff : (laurent_series S) → S := λ F, add_con.lift_on F (punctured_power_series.coeff n) (cong_coeff n),
  use coeff,
end


-- -- #print punctured_power_series.add
def a : ℕ → ℤ := λ n, if n < 5 then 4*n+3 else 0
def b : ℕ → ℤ := λ n, if n < 7 then 1-2*n else 0
-- -- -- def 𝕜₁ : 𝕄 := ℘⁻¹ 1
-- -- -- def 𝕜₂ : 𝕄 := ℘⁻¹ 3

-- def F₁ : punctured_power_series ℤ := (1, a)
-- def F₂ : punctured_power_series ℤ := (3, b)
-- def G₁ : laurent_series ℤ := F₁
-- def F₃ : punctured_power_series ℤ := F₁ + (7, 0)
-- def G₃ : laurent_series ℤ := F₃
-- #eval F₁.2 2
-- #eval punctured_power_series.coeff (-1) F₁
-- #eval punctured_power_series.coeff (1) F₃
-- #eval coeff 4 G₃
-- -- #eval a 5
-- #eval F₁.snd 2
-- #eval F₂.snd 9
-- #eval (F₁ + F₂).snd 7
-- #eval (lift_mul F₁ F₂).snd 10
/-The right answers for F₁ + F₂ are
0 → 0, 1 → 1, 2 → -1, 3 → 0, 4 → 2, 5 → 4, 6 → 6, 7 → 8, 8 → 10, 9 → 12

def F₃ := (𝟘, b) --check!
--/




end laurent_series
