/-
Copyright (c) 2023 Niels Voss. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Niels Voss
-/

import number_theory.arithmetic_function

open_locale big_operators

namespace nat
namespace arithmetic_function

variable {R : Type*}

-- For results that don't require the arithmetic function's codomain to be a field
-- The functions might also have diffent codomains
section distinct_codomains

variable {M : Type*}
variables [has_zero R] [add_comm_monoid M] [has_smul R M] [has_one M]
variables (f : arithmetic_function R) (g : arithmetic_function M)

def is_dirichlet_inv : Prop := f • g = 1

/-theorem dirichlet_inv_unique (g₁ : arithmetic_function M) (g₂ : arithmetic_function M)
  (h₁ : is_dirichlet_inv f g₁) (h₂ : is_dirichlet_inv f g₂) : g₁ = g₂ :=
begin
  sorry
end-/

end distinct_codomains

section same_codomain_with_comm_ring

variable [comm_ring R]
variables (f : arithmetic_function R) (g : arithmetic_function R)

def dirichlet_inv_as_mul (h : is_dirichlet_inv f g) : f * g = 1 := h

def dirichlet_inv_symm (h : is_dirichlet_inv f g) : g • f = 1 :=
(mul_comm g f).trans h

def dirichlet_inv_to_unit (h : is_dirichlet_inv f g) : (arithmetic_function R)ˣ :=
{ val := f,
  inv := g,
  val_inv := h,
  inv_val := dirichlet_inv_symm f g h }

theorem dirichlet_inv_of_unit (u : (arithmetic_function R)ˣ) :
  is_dirichlet_inv u.val u.inv := u.val_inv

theorem dirichlet_inv_unique {g₁ : arithmetic_function R} {g₂ : arithmetic_function R}
  (h₁ : is_dirichlet_inv f g₁) (h₂ : is_dirichlet_inv f g₂) : g₁ = g₂ :=
inv_unique h₁ h₂

end same_codomain_with_comm_ring

section specific_dirichlet_inverse

variable [field R]

def dirichlet_inv_fun (f : arithmetic_function R) : ℕ → R
| 0 := 0
| 1 := 1 / (f 1)
| n := -1 / (f 1) * ∑ x : (divisors_antidiagonal n).erase ⟨1, n⟩,
  ( have x.val.2 < n := sorry,
    (f x.val.1) * (dirichlet_inv_fun x.val.2))

def dirichlet_inv (f : arithmetic_function R) : arithmetic_function R :=
{ to_fun := dirichlet_inv_fun f,
  map_zero' := by unfold dirichlet_inv_fun }

instance has_inv : has_inv (arithmetic_function R) :=
{ inv := dirichlet_inv }


lemma dirichlet_inv_to_fun (f : arithmetic_function R) :
  ((f⁻¹ : arithmetic_function R) : ℕ → R) = dirichlet_inv_fun f :=
begin
  unfold has_inv.inv,
  sorry
end

theorem dirichlet_inv_zero (f : arithmetic_function R) : f⁻¹ 0 = 0 :=
calc (f⁻¹ : arithmetic_function R) 0 = dirichlet_inv_fun f 0 : by rw dirichlet_inv_to_fun f
                                 ... = 0                     : by unfold dirichlet_inv_fun

theorem dirichlet_inv_one (f : arithmetic_function R) : f⁻¹ 1 = 1 / f 1 :=
calc (f⁻¹ : arithmetic_function R) 1 = dirichlet_inv_fun f 1 : by rw dirichlet_inv_to_fun f
                                 ... = 1 / f 1               : by unfold dirichlet_inv_fun

theorem dirichlet_inv_is_inv {f : arithmetic_function R} (h : f 1 ≠ 0) : is_dirichlet_inv f f⁻¹ :=
begin
  unfold is_dirichlet_inv,
  sorry
end

end specific_dirichlet_inverse

end arithmetic_function
end nat
