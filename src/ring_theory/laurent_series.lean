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

namespace maxumal

def maxumal := ℕ

def equiv_to_nat : maxumal ≃ nat := equiv.refl _

notation `𝕄` := maxumal
notation `℘` := equiv_to_nat.to_fun
notation `℘⁻¹` := equiv_to_nat.symm
notation `𝟘` := ℘⁻¹ 0

instance : inhabited 𝕄 := ⟨𝟘⟩
instance : has_zero 𝕄 := ⟨𝟘⟩
instance : nontrivial 𝕄 := ⟨⟨𝟘, ℘⁻¹ 1, nat.zero_ne_one⟩⟩

lemma nat.max_zero : ∀ {m : ℕ}, max m 0 = m :=
begin
  intro a,
  rw [max_comm a 0, nat.zero_max],
end

instance : add_comm_monoid 𝕄 :=
{ add := begin change ℕ → ℕ → ℕ, use max, end,
  add_assoc := by convert max_assoc,
  zero := 𝟘,
  zero_add := λ _, nat.zero_max,
  add_zero := λ _, nat.max_zero,
  add_comm := max_comm, }

def sub_left_maxumal : 𝕄 × 𝕄 → 𝕄
| (𝕜₁, 𝕜₂) := ℘⁻¹ (℘ (𝕜₁ + 𝕜₂) - ℘ 𝕜₁)
notation `μ` := sub_left_maxumal

@[simp] lemma zero_sub_left : ∀ (𝕜 : 𝕄), μ (𝟘, 𝕜) = 𝕜 := sorry
@[simp] lemma sub_left_zero : ∀ (𝕜 : 𝕄 ), μ (𝕜, 𝟘) = 𝟘 := sorry

#eval ℘ ((℘⁻¹ 8) + (℘⁻¹ 5))
#eval μ (℘⁻¹ 8, ℘⁻¹ 5)
#eval μ (℘⁻¹ 5, ℘⁻¹ 8)
-- #eval equiv_to_nat.to_fun ((equiv_to_nat.inv_fun 5) + (equiv_to_nat.inv_fun 8))
-- #eval equiv_to_nat.to_fun ((equiv_to_nat.inv_fun 3) + (equiv_to_nat.inv_fun 5))
-- #eval equiv_to_nat.to_fun ((equiv_to_nat.inv_fun 2) + (equiv_to_nat.inv_fun 0))

end maxumal
noncomputable theory
open_locale classical big_operators

namespace punctured_power_series

/-- Multivariate formal power series, where `σ` is the index set of the variables
and `R` is the coefficient ring.-/
-- def mv_power_series (σ : Type*) (R : Type*) := (σ →₀ ℕ) →
def punctured_power_series (R : Type*) := 𝕄 × (ℕ → R)

-- open finsupp
variables {R : Type*}

instance [inhabited R]       : inhabited       (punctured_power_series R) := ⟨(default _, (λ _, default _))⟩
instance [has_zero R]        : has_zero        (punctured_power_series R) := ⟨(𝟘, 0)⟩
instance [nontrivial R]      : nontrivial      (punctured_power_series R) := nontrivial_prod_left

@[simp] lemma ext_punctured_power_series (F₁ F₂ : punctured_power_series R) :
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

def shift_fun {R : Type*} [has_zero R]: 𝕄 → (ℕ → R) → (ℕ → R)
| (k) := λ f, λ n, if n < (℘ k) then (0 : R) else f (n - ℘ k)

@[simp] lemma shift_fun_by_zero [has_zero R] (f : ℕ → R) : shift_fun 𝟘 f = f := rfl

-- section add_comm_monoid

/-We only consider the case where R is a commutative additive monoid, for simplicity-/
variable [add_comm_monoid R]

-- lemma cst_shift_fun' (𝕜 : 𝕄) : shift_fun 𝕜 (function.const : ℕ → R) = (0 : ℕ → R) := sorry,

@[simp] lemma cst_shift_fun (𝕜 : 𝕄) : shift_fun 𝕜 (0 : ℕ → R) = (0 : ℕ → R) :=
begin
      -- funext,
      -- dsimp [shift_fun],
      sorry,
      -- apply if_congr,
      -- split,
      -- -- apply dif_eq_if,
      -- apply dif_neg,
      -- simp * at *,
      -- rw function.const_apply _ 0 n,
      -- apply rfl,

end

def add : (punctured_power_series R) → (punctured_power_series R) → (punctured_power_series R) :=
begin
  rintros ⟨𝕜₁, f₁⟩ ⟨𝕜₂, f₂⟩,
  exact ⟨𝕜₁ + 𝕜₂, shift_fun (μ (𝕜₁, 𝕜₂)) f₁ + shift_fun (μ (𝕜₂, 𝕜₁)) f₂⟩,
end

lemma add_assoc : ∀ (F₁ F₂ F₃ : punctured_power_series R), punctured_power_series.add (punctured_power_series.add  F₁ F₂) F₃ =
 punctured_power_series.add F₁ (punctured_power_series.add F₂ F₃) :=
begin -- sorry,
  rintros ⟨𝕜₁, f₁⟩ ⟨𝕜₂, f₂⟩ ⟨𝕜₃, f₃⟩,
  ext,
  apply max_assoc,
  dsimp [punctured_power_series.add],
  show (shift_fun (μ (𝕜₁ + 𝕜₂, 𝕜₃)) (shift_fun (μ (𝕜₁, 𝕜₂)) f₁ + shift_fun (μ (𝕜₂, 𝕜₁)) f₂) +
       shift_fun (μ (𝕜₃, 𝕜₁ + 𝕜₂)) f₃) x = (shift_fun (μ (𝕜₁, 𝕜₂ + 𝕜₃)) f₁ +
        shift_fun (μ (𝕜₂ + 𝕜₃, 𝕜₁)) (shift_fun (μ (𝕜₂, 𝕜₃)) f₂ + shift_fun (μ (𝕜₃, 𝕜₂)) f₃)) x,
  simp only [pi.add_apply] at *,
  sorry,
  -- apply add_assoc,
  --     x,
  -- show (shift_fun μ (μ (𝕜₁, 𝕜₂), 𝕜₃) (punctured_power_series.add  F₁ F₂).snd + shift_fun μ (𝕜₃, μ (𝕜₁, 𝕜₂)) f₃).snd x =
  --   (shift_fun μ (𝕜₁, μ (𝕜₂, 𝕜₃)) f₁ + shift_fun μ (μ (𝕜₂, 𝕜₃), 𝕜₁) (punctured_power_series.add F₂ F₃).snd).snd x,
-- suffices primo : (((k₁, f₁) + (k₂, f₂)) + (k₃, f₃)).2 x = ((k₁, f₁) + ((k₂, f₂) + (k₃, f₃))).2 x,
-- exact primo,
-- suffices this : (shift_fun ((max (max k₁ k₂) k₃) - max k₁ k₂) (((k₁,f₁) + (k₂, f₂)).snd)
--     + shift_fun ((max (max k₁ k₂) k₃) - k₃) f₃) x = (shift_fun ((max k₁ (max k₂ k₃)) - k₁) f₁ + shift_fun ((max k₁ (max k₂ k₃)) - max k₂ k₃)
--     (((k₂,f₂) + (k₃, f₃)).snd)) x,
--                 exact this,
end

lemma zero_add : ∀ (F: punctured_power_series R), punctured_power_series.add 0 F = F :=
begin
  rintro ⟨𝕜, f⟩,
  ext,
  apply nat.zero_max,
  show (shift_fun (μ (𝟘, 𝕜)) 0 + shift_fun (μ (𝕜, 𝟘)) f) x = f x,
  rw [maxumal.zero_sub_left, maxumal.sub_left_zero, pi.add_apply, shift_fun_by_zero,
    cst_shift_fun, pi.zero_apply, zero_add],
end

lemma add_zero : ∀ (F: punctured_power_series R), punctured_power_series.add F 0 = F :=
begin
  rintro ⟨𝕜, f⟩,
  ext,
  apply maxumal.nat.max_zero,
  show (shift_fun (μ (𝕜, 𝟘)) f + shift_fun (μ (𝟘, 𝕜)) 0) x = f x,
  rw [maxumal.zero_sub_left, maxumal.sub_left_zero, pi.add_apply, shift_fun_by_zero,
    cst_shift_fun, pi.zero_apply, add_zero],
end

lemma add_comm : ∀ (F G: punctured_power_series R), punctured_power_series.add F G =
  punctured_power_series.add G F :=
begin
  rintros ⟨𝕜₁, f₁⟩ ⟨𝕜₂, f₂⟩,
  ext,
  apply max_comm,
  show (shift_fun (μ (𝕜₁, 𝕜₂)) f₁ + shift_fun (μ (𝕜₂, 𝕜₁)) f₂) x =
    (shift_fun (μ (𝕜₂, 𝕜₁)) f₂ + shift_fun (μ (𝕜₁, 𝕜₂)) f₁) x,
  simp only [pi.add_apply] at *,
  apply add_comm,
end

instance : add_comm_monoid (punctured_power_series R) :=
{ add := punctured_power_series.add,
  add_assoc := punctured_power_series.add_assoc,
  zero := (0, 0),
  zero_add := punctured_power_series.zero_add,
  add_zero := punctured_power_series.add_zero,
  add_comm := punctured_power_series.add_comm }

#print punctured_power_series.add
-- def a : ℕ → ℤ := λ n, 4*n+3
-- def b : ℕ → ℤ := λ n, 1-2*n
-- def 𝕜₁ : 𝕄 := ℘⁻¹ 1
-- def 𝕜₂ : 𝕄 := ℘⁻¹ 3

-- def F₁ : punctured_power_series ℤ := (𝕜₁, a)
-- def F₂ : punctured_power_series ℤ := (𝕜₂, b)

-- #eval (F₁ + F₂).snd 8
/-The right answers are
0 → 1, 1 → -1, 2 → 0, 3 → 2, 4 → 4, 5 → 6, 6 → 8, 7 → 10, 8 → 12

def F₃ := (𝟘, b) --check!
--/

def eqv_punctured (F₁ F₂ : punctured_power_series R) : Prop :=
∃ ℓ₁₂ ℓ₂₁ : 𝕄, F₁ + (ℓ₁₂, 0) = F₂ + (ℓ₂₁, 0)

lemma eqv_punctured_rfl: reflexive (@eqv_punctured R _) := sorry
lemma eqv_punctured_symm : symmetric (@eqv_punctured R _) := sorry
lemma eqv_punctured_trans : transitive (@eqv_punctured R _) := sorry

theorem eqv_punctured.is_equivalence :  equivalence (@eqv_punctured R _) :=
 ⟨eqv_punctured_rfl, eqv_punctured_symm, eqv_punctured_trans⟩

def eqv_punctured.add_con (R : Type*) [add_comm_monoid R] : add_con (punctured_power_series R) :=
begin
  use @eqv_punctured R _,
  exact eqv_punctured.is_equivalence,
  sorry,
end

def laurent_series (R : Type*) [add_comm_monoid R]:= (eqv_punctured.add_con R).quotient
instance inhabited : inhabited (laurent_series R) :=-- ⟨((eqv_punctured.add_con R).mk' 0)⟩
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
#check (eqv_punctured.add_con S).mk'

def lift_neg : (punctured_power_series S) → (laurent_series S) :=
  λ ⟨𝕜, f⟩, (eqv_punctured.add_con S).mk' ⟨𝕜, -f⟩
lemma cong_neg : ∀ (F₁ F₂ : punctured_power_series S),  eqv_punctured F₁ F₂ →
  lift_neg F₁ = lift_neg F₂ :=
begin
  rintros ⟨𝕜₁, f₁⟩ ⟨𝕜₂, f₂⟩ h,
  dsimp [lift_neg],
  rw eqv_punctured at h,
  rcases h with ⟨ℓ₁₂, ℓ₂₁, h⟩,
  replace h : 𝕜₁ + ℓ₁₂ = 𝕜₂ + ℓ₂₁ ∧ shift_fun (μ (𝕜₁, ℓ₁₂)) (-f₁) = shift_fun (μ (𝕜₂, ℓ₂₁)) (-f₂),
  split,
  rw ext_punctured_power_series at h,
  exact h.1,
  sorry,
  replace h : eqv_punctured (𝕜₁, -f₁) (𝕜₂, -f₂),
  { use [ℓ₁₂, ℓ₂₁],
    ext, exact h.1,
    show (shift_fun (μ (𝕜₁, ℓ₁₂)) (- f₁) + shift_fun (μ (ℓ₁₂, 𝕜₁)) 0) x =
    (shift_fun (μ (𝕜₂, ℓ₂₁)) (-f₂) + shift_fun (μ (ℓ₂₁, 𝕜₂)) 0) x,
    simp only [*, cst_shift_fun]},
  apply (add_con.eq (eqv_punctured.add_con S)).mpr h,
end

def lift_sub : (punctured_power_series S) → (punctured_power_series S) → (laurent_series S) :=
  λ ⟨𝕜₁, f₁⟩, λ ⟨𝕜₂, f₂⟩, (eqv_punctured.add_con S).mk' ⟨μ (𝕜₁, 𝕜₂), f₁-f₂⟩
lemma cong_sub : ∀ (F₁ F₂ G₁ G₂: punctured_power_series S),  eqv_punctured F₁ G₁ →
  eqv_punctured.add_con S F₂ G₂ → lift_sub F₁ F₂ = lift_sub G₁ G₂ := sorry

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
