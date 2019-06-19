/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.finsupp

/-- Multivariate power series, where `σ` is the index set of the variables
and `α` is the coefficient ring.-/
def power_series (σ : Type*) (α : Type*) := (σ →₀ ℕ) → α

namespace power_series
variables {σ : Type*} {α : Type*} [decidable_eq σ] [comm_semiring α]

def coeff (c : σ →₀ ℕ) (φ : power_series σ α) := φ c

@[extensionality] lemma ext {φ ψ : power_series σ α} (h : ∀ c, coeff c φ = coeff c ψ) : φ = ψ :=
funext h

lemma ext_iff {φ ψ : power_series σ α} : φ = ψ ↔ (∀ c, coeff c φ = coeff c ψ) :=
⟨congr_fun, ext⟩

def monomial (c : σ →₀ ℕ) (a : α) : power_series σ α := λ i, if i = c then a else 0

lemma coeff_monomial (c i : σ →₀ ℕ) (a : α) :
  coeff i (monomial c a) = if i = c then a else 0 := rfl

@[simp] lemma coeff_monomial' (c : σ →₀ ℕ) (a : α) :
  coeff c (monomial c a) = a := if_pos rfl

def C (a : α) : power_series σ α := monomial 0 a

lemma coeff_C (c : σ →₀ ℕ) (a : α) :
  coeff c (C a : power_series σ α) = if c = 0 then a else 0 := rfl

@[simp] lemma coeff_C_zero (a : α) : coeff 0 (C a : power_series σ α) = a :=
coeff_monomial' 0 a

@[simp] lemma monomial_zero (a : α) : (monomial 0 a : power_series σ α) = C a := rfl

def X (s : σ) : power_series σ α := monomial (finsupp.single s 1) 1

lemma coeff_X (c : σ →₀ ℕ) (s : σ) :
  coeff c (X s : power_series σ α) = if c = finsupp.single s 1 then 1 else 0 := rfl

lemma coeff_X' (s t : σ) :
  coeff (finsupp.single t 1) (X s : power_series σ α) = if t = s then 1 else 0 :=
if h : t = s then by simp [h, coeff_X] else
begin
  rw [coeff_X, if_neg h],
  split_ifs with H,
  { have := @finsupp.single_apply σ ℕ _ _ _ t s 1,
    rw [if_neg h, H, finsupp.single_apply, if_pos rfl] at this,
    exfalso, exact one_ne_zero this, },
  { refl }
end

@[simp] lemma coeff_X'' (s : σ) :
  coeff (finsupp.single s 1) (X s : power_series σ α) = 1 :=
by rw [coeff_X', if_pos rfl]

section ring
variables (σ) (α) (c : σ →₀ ℕ) (φ ψ : power_series σ α)

def zero : power_series σ α := λ c, 0

instance : has_zero (power_series σ α) := ⟨zero σ α⟩

@[simp] lemma coeff_zero : coeff c (0 : power_series σ α) = 0 := rfl

@[simp] lemma C_zero : (C 0 : power_series σ α) = 0 :=
ext $ λ c, if h : c = 0 then by simp [h] else by rw [coeff_C, if_neg h, coeff_zero]

def one : power_series σ α := C 1

instance : has_one (power_series σ α) := ⟨one σ α⟩

@[simp] lemma coeff_one :
  coeff c (1 : power_series σ α) = if c = 0 then 1 else 0 := rfl

@[simp] lemma coeff_one_zero : coeff 0 (1 : power_series σ α) = 1 :=
coeff_C_zero 1

@[simp] lemma C_one : (C 1 : power_series σ α) = 1 := rfl

def add (φ ψ : power_series σ α) : power_series σ α :=
λ c, coeff c φ + coeff c ψ

instance : has_add (power_series σ α) := ⟨add σ α⟩

variables {σ α}

@[simp] lemma coeff_add : coeff c (φ + ψ) = coeff c φ + coeff c ψ := rfl

@[simp] lemma zero_add : (0 : power_series σ α) + φ = φ := ext $ λ c, zero_add _

@[simp] lemma add_zero : φ + 0 = φ := ext $ λ c, add_zero _

lemma add_comm : φ + ψ = ψ + φ := ext $ λ c, add_comm _ _

@[simp] lemma monomial_add (c : σ →₀ ℕ) (a b : α) :
  (monomial c (a + b) : power_series σ α) = monomial c a + monomial c b :=
ext $ λ i, if h : i = c then by simp [h] else by simp [coeff_monomial, if_neg h]

@[simp] lemma C_add (a b : α) : (C (a + b) : power_series σ α) = C a + C b :=
monomial_add 0 a b

def mul (φ ψ : power_series σ α) : power_series σ α :=
λ c, _


end ring

end power_series
