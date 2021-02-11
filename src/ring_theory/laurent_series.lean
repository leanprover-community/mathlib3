/-
Copyright (c) 2021 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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

noncomputable theory
open_locale classical big_operators

/-- Multivariate formal power series, where `σ` is the index set of the variables
and `R` is the coefficient ring.-/
-- def mv_power_series (σ : Type*) (R : Type*) := (σ →₀ ℕ) → R
def punctured_power_series (R : Type*) := ℕ × (ℕ → R)

def old_shift_fun {R : Type*} : ℕ → (ℕ → R) → (ℕ → R)
-- | 0 := λ x, x
| (n) := λ f, function.comp f (nat.add n)

def preshift : ℕ → ℕ → ℕ
| 0 := λ x, x
| k := λ x, if x < k then 0 else x-k

lemma preshift_by_zero : preshift 0 = (λ x, x) := rfl

def shift_fun {R : Type*} : ℕ → (ℕ → R) → (ℕ → R)
| (n) := λ f, function.comp f (preshift n)

lemma shift_fun_by_zero {R : Type*} (f : ℕ → R) : shift_fun 0 f = f :=
begin
  rw shift_fun,
  funext,
  simp only [nat.add_def, function.comp_app, preshift_by_zero],
end

namespace punctured_power_series
-- open finsupp
variables {R : Type*}

instance [inhabited R]       : inhabited       (punctured_power_series R) := ⟨(default _, (λ _, default _))⟩
instance [has_zero R]        : has_zero        (punctured_power_series R) := ⟨(0, 0)⟩
instance [nontrivial R]      : nontrivial      (punctured_power_series R) := nontrivial_prod_left

section monoid

variable [add_monoid R]

lemma zero_shift_fun (k : ℕ) : shift_fun k (0 : ℕ → R) = 0 := rfl

protected def add : (punctured_power_series R) → (punctured_power_series R) → (punctured_power_series R) :=
begin
  rintros ⟨k₁, f₁⟩ ⟨k₂, f₂⟩,
  exact ⟨max k₁ k₂, (shift_fun ((max k₁ k₂) - k₁ ) f₁) + (shift_fun ((max k₁ k₂) - k₂ ) f₂)⟩,
end

lemma add_assoc (F₁ F₂ F₃ : punctured_power_series R) : punctured_power_series.add (punctured_power_series.add  F₁ F₂) F₃ =
 punctured_power_series.add F₁ (punctured_power_series.add F₂ F₃) :=
begin sorry,
                -- rintros ⟨k₁, f₁⟩ ⟨k₂, f₂⟩ ⟨k₃, f₃⟩,
                -- ext,
                -- apply max_assoc,
-- suffices primo : (((k₁, f₁) + (k₂, f₂)) + (k₃, f₃)).2 x = ((k₁, f₁) + ((k₂, f₂) + (k₃, f₃))).2 x,
-- exact primo,
-- suffices this : (shift_fun ((max (max k₁ k₂) k₃) - max k₁ k₂) (((k₁,f₁) + (k₂, f₂)).snd)
--     + shift_fun ((max (max k₁ k₂) k₃) - k₃) f₃) x = (shift_fun ((max k₁ (max k₂ k₃)) - k₁) f₁ + shift_fun ((max k₁ (max k₂ k₃)) - max k₂ k₃)
--     (((k₂,f₂) + (k₃, f₃)).snd)) x,
--                 exact this,
end

lemma zero_add : ∀ (F: punctured_power_series R), punctured_power_series.add 0 F = F :=
begin
  rintro ⟨k, f⟩,
  ext,
  apply nat.zero_max,
  suffices this : (shift_fun ((max 0 k) - 0) 0 + shift_fun ((max 0 k) - k) f) x = f x,
  exact this,
  rw [nat.zero_max, nat.sub_zero, nat.sub_self, shift_fun_by_zero, zero_shift_fun, zero_add],
end

lemma add_zero : ∀ (F: punctured_power_series R), punctured_power_series.add F 0 = F :=
begin
  rintro ⟨k, f⟩,
  ext,
  convert nat.zero_max,
  apply max_comm k 0,
  suffices this : (shift_fun ((max k 0) - k) f + shift_fun ((max k 0) - 0) 0) x = f x,
  exact this,
  simp only [max_comm k 0, nat.zero_max, shift_fun_by_zero, zero_shift_fun, add_zero, nat.sub_self],
end

instance [add_monoid R]      : add_monoid      (punctured_power_series R) :=
{ add := punctured_power_series.add,
  add_assoc := punctured_power_series.add_assoc,
  zero := (0, 0),
  zero_add := punctured_power_series.zero_add,
  add_zero := punctured_power_series.add_zero}

lemma add_comm : ∀ (F G: punctured_power_series R), punctured_power_series.add F G = punctured_power_series.add G F := sorry

instance [add_comm_monoid R] : add_comm_monoid (punctured_power_series R) :=
{ add := punctured_power_series.add,
  add_assoc := punctured_power_series.add_assoc,
  zero := (0, 0),
  zero_add := punctured_power_series.zero_add,
  add_zero := punctured_power_series.add_zero,
  add_comm := punctured_power_series.add_comm }

variables F₁ F₂ : punctured_power_series R


def eqv_punctured_shift {R : Type*} [semiring R] (F₁ F₂ : punctured_power_series R) : Prop :=
(F₂.snd = (shift_fun (F₂.fst - F₁.fst) F₁.snd)) ∨ (F₁.snd = (shift_fun (F₁.fst - F₂.fst) F₂.snd))

lemma eqv_punctured_shift_rfl {R : Type*} [semiring R] (F : punctured_power_series R) :
  eqv_punctured_shift F F :=
sorry

lemma eqv_punctured_shift_symm {R : Type*} [semiring R] (F₁ F₂ : punctured_power_series R) :
  eqv_punctured_shift F₁ F₂ →  eqv_punctured_shift F₂ F₁:=
sorry

lemma eqv_punctured_shift_trans {R : Type*} [semiring R] (F₁ F₂ F₃: punctured_power_series R) :
  eqv_punctured_shift F₁ F₂ →  eqv_punctured_shift F₂ F₃ → eqv_punctured_shift F₁ F₃ :=
begin sorry,
end


-- theorem is_equivalence_shift {R : Type*} [semiring R] equivalence (@eqv_punctured_shift :=
-- begin
-- end SEE PAG 166 tpil



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

end monoid
end punctured_power_series
