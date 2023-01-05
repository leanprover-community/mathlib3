/-
Copyright (c) 2023 Niels Voss. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Niels Voss
-/

import number_theory.arithmetic_function
import tactic.field_simp

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

/--
Used to prove that `dirichlet_inv_fun` terminates
-/
private lemma divisors_antidiagonal_erase_bounds {n : ℕ} {x : ℕ × ℕ}
  (h : x ∈ (divisors_antidiagonal n).erase ⟨1, n⟩) : x.2 < n :=
begin
  cases x with a b,
  change b < n,
  have h₁ : a * b = n := (mem_divisors_antidiagonal.mp (finset.mem_of_mem_erase h)).1,
  have h₂ : 0 < n := zero_lt_iff.mpr (mem_divisors_antidiagonal.mp (finset.mem_of_mem_erase h)).2,
  have h₃ : b ≤ n := le_of_dvd h₂ (dvd.intro_left a h₁),
  have h₄ : b ≠ n,
  { intro hb,
    rw hb at h₁,
    have : a = 1,
    { calc a = a * n / n : by rw nat.mul_div_cancel _ h₂
         ... = n / n : by rw h₁
         ... = 1 : by rw nat.div_self h₂ },
    rw [this, hb] at h,
    exact absurd h (finset.not_mem_erase (1, n) (divisors_antidiagonal n)) },
  exact ne.lt_of_le h₄ h₃
end

def dirichlet_inv_fun (f : arithmetic_function R) : ℕ → R
| 0 := 0
| 1 := 1 / (f 1)
| n := -1 / (f 1) * ∑ x : (divisors_antidiagonal n).erase ⟨1, n⟩,
  ( have x.val.2 < n := divisors_antidiagonal_erase_bounds x.property,
    (f x.val.1) * (dirichlet_inv_fun x.val.2))

def dirichlet_inv (f : arithmetic_function R) : arithmetic_function R :=
{ to_fun := dirichlet_inv_fun f,
  map_zero' := by unfold dirichlet_inv_fun }

instance has_inv : has_inv (arithmetic_function R) :=
{ inv := dirichlet_inv }


lemma dirichlet_inv_to_fun (f : arithmetic_function R) :
  ((f⁻¹ : arithmetic_function R) : ℕ → R) = dirichlet_inv_fun f := rfl

theorem dirichlet_inv_zero (f : arithmetic_function R) : f⁻¹ 0 = 0 :=
calc (f⁻¹ : arithmetic_function R) 0 = dirichlet_inv_fun f 0 : by rw dirichlet_inv_to_fun f
                                 ... = 0                     : by unfold dirichlet_inv_fun

theorem dirichlet_inv_one (f : arithmetic_function R) : f⁻¹ 1 = 1 / f 1 :=
calc (f⁻¹ : arithmetic_function R) 1 = dirichlet_inv_fun f 1 : by rw dirichlet_inv_to_fun f
                                 ... = 1 / f 1               : by unfold dirichlet_inv_fun

theorem dirichlet_inv_of_add_two (f : arithmetic_function R) (n : ℕ) :
  f⁻¹ (n + 2) = -1 / (f 1) * ∑ x in (divisors_antidiagonal (n + 2)).erase ⟨1, n + 2⟩,
    ((f x.1) * (f⁻¹ x.2)) :=
begin
  rw dirichlet_inv_to_fun f,
  unfold dirichlet_inv_fun,
  rw ←@finset.sum_coe_sort R (ℕ × ℕ),
  refl,
end

theorem dirichlet_inv_of_ge_two (f : arithmetic_function R) {n : ℕ} (h : 2 ≤ n) :
  f⁻¹ n = -1 / (f 1) * ∑ x in (divisors_antidiagonal n).erase ⟨1, n⟩, ((f x.1) * (f⁻¹ x.2)) :=
begin
  rw dirichlet_inv_to_fun f,
  rw ←nat.sub_add_cancel h,
  set k := n - 2,
  exact dirichlet_inv_of_add_two f k
end

private lemma dirichlet_id_of_ge_two {n : ℕ} (h : 2 ≤ n) : (1 : arithmetic_function R) n = 0 :=
begin
  rw ←nat.sub_add_cancel h,
  refl
end

private lemma finset_sum_split (f : ℕ × ℕ → R) {n : ℕ} (h : n ≠ 0) :
  ∑ x in n.divisors_antidiagonal, f x = f (1, n) + ∑ x in n.divisors_antidiagonal.erase ⟨1, n⟩, f x :=
begin
  have h₁ : (1, n) ∉ n.divisors_antidiagonal.erase (1, n) := finset.not_mem_erase _ _,
  have h₂ : (1, n) ∈ n.divisors_antidiagonal := mem_divisors_antidiagonal.mpr ⟨by simp, h⟩,
  have h₃ : n.divisors_antidiagonal = finset.cons (1, n) (n.divisors_antidiagonal.erase (1, n)) h₁,
  { simpa [h₁] using (finset.insert_erase h₂).symm },
  conv { to_lhs, rw h₃ },
  exact finset.sum_cons h₁
end

theorem dirichlet_inv_is_inv {f : arithmetic_function R} (h : f 1 ≠ 0) : is_dirichlet_inv f f⁻¹ :=
begin
  ext n,
  have to_split : n = 0 ∨ n = 1 ∨ 2 ≤ n,
  { rcases n with n | n | n,
    { left, refl },
    { right, left, refl },
    { right, right, exact le_add_self } },
  rcases to_split with h₁ | h₁ | h₁,
  { simp only [h₁, map_zero] },
  { rw h₁,
    change ∑ (x : ℕ × ℕ) in {(1, 1)}, f x.fst * f⁻¹ x.snd = 1,
    rw finset.sum_singleton,
    change f 1 * f⁻¹ 1 = 1,
    rw dirichlet_inv_one,
    simp [h] },
  { rw dirichlet_id_of_ge_two h₁,
    change ∑ (x : ℕ × ℕ) in n.divisors_antidiagonal, f x.fst * f⁻¹ x.snd = 0,
    have h₂ : n ≠ 0 := by linarith,
    rw finset_sum_split _ h₂,
    change f 1 * f⁻¹ n + ∑ (x : ℕ × ℕ) in n.divisors_antidiagonal.erase (1, n), f x.fst * f⁻¹ x.snd = 0,
    suffices : ∑ (x : ℕ × ℕ) in n.divisors_antidiagonal.erase (1, n), f x.fst * f⁻¹ x.snd = - f 1 * f⁻¹ n,
    { simp [this] },
    suffices : 1 / f 1 * ∑ (x : ℕ × ℕ) in n.divisors_antidiagonal.erase (1, n), f x.fst * f⁻¹ x.snd = - f⁻¹ n,
    { field_simp at this,
      simp [mul_comm, this] },
    suffices : f⁻¹ n = - 1 / f 1 * ∑ (x : ℕ × ℕ) in n.divisors_antidiagonal.erase (1, n), f x.fst * f⁻¹ x.snd,
    { rw this, ring },
    exact dirichlet_inv_of_ge_two f h₁ }
end

@[simp] lemma dirichlet_inv_mul_cancel {f : arithmetic_function R} (h : f 1 ≠ 0) : f * f⁻¹ = 1 :=
dirichlet_inv_is_inv h

@[simp] lemma dirichlet_inv_mul_cancel' {f : arithmetic_function R} (h : f 1 ≠ 0) : f⁻¹ * f = 1 :=
mul_comm f f⁻¹ ▸ dirichlet_inv_is_inv h

end specific_dirichlet_inverse

end arithmetic_function
end nat
