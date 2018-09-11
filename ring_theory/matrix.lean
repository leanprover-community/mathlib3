/-
Copyright (c) 2018 Ellen Arlt and Blair Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi

Matrices over a ring
-/

import algebra.big_operators data.set.finite
import algebra.module 
import algebra.pi_instances

definition matrix (R) (n m : ℕ) [ring R] :=  fin n → fin m → R 
 
namespace matrix

open finset

variables {R : Type*} [ring R] {k l m n : ℕ}

instance : add_comm_group (matrix R k l) := by unfold matrix; apply_instance

definition mul (A : matrix R k l) (B : matrix R l m) : matrix R k m := 
λ x y, sum univ (λ i, A x i * B i y)

theorem mul_assoc (A : matrix R k l) (B : matrix R l m) (C : matrix R m n) :
mul (mul A B) C = mul A (mul B C) :=
begin
  ext x y,
  unfold mul,
  suffices : sum univ
      (λ (j : fin m), sum univ (λ (i : fin l), 
        A x i * B i j * C j y)) =
    sum univ
      (λ (i : fin l), sum univ (λ (j : fin m), 
        A x i * (B i j * C j y))),
    simpa [finset.mul_sum,finset.sum_mul],
  rw finset.sum_comm,
  simp [mul_assoc],
end

theorem left_distrib (A : matrix R m n) (B C : matrix R n l) :
mul A (B + C) = mul A B + mul A C :=
begin
  ext i k,
  show sum univ (λ j, A i j * (B j k + C j k)) =
    sum univ (λ j, A i j * B j k) +
    sum univ (λ j, A i j * C j k),
  simp [finset.sum_add_distrib,mul_add],
end

theorem right_distrib (A B : matrix R m n) (C : matrix R n l) :
mul (A + B) C = mul A C + mul B C :=
begin
  ext i k,
  show sum univ (λ j, (A i j + B i j) * C j k) =
    sum univ (λ j, A i j * C j k) +
    sum univ (λ j, B i j * C j k),
  simp [finset.sum_add_distrib,add_mul],
end

definition identity_matrix : (matrix R n n) := 
λ i j, if i = j then 1 else 0

instance : has_one (matrix R n n) := ⟨identity_matrix⟩
instance : has_mul (matrix R n n) := ⟨mul⟩

theorem one_mul (A : matrix R n n) : 1 * A = A :=
begin
  ext i k,
  show sum univ (λ j, ite (i = j) 1 0 * A j k) = A i k,
  have H : ∀ j : fin n, j ∉ finset.singleton i → ite (i = j) 1 0 * A j k = 0,
    intros w Hw,split_ifs,
      rw h at Hw,simp * at *,
    rw zero_mul,
  rw ←finset.sum_subset (finset.subset_univ _) (λ j _, H j),
  simp,
end

theorem mul_one (A : matrix R n n) : A * 1 = A :=
begin
  ext i k,
  show sum univ (λ (j : fin n), A i j * ite (j = k) 1 0) = A i k,
  have H : ∀ j : fin n, j ∉ finset.singleton k → A i j * ite (j = k) 1 0 = 0,
    intros j Hj,
    split_ifs,
      rw h at Hj, simp * at *,
    rw mul_zero,
  rw ←finset.sum_subset (finset.subset_univ _) (λ j _, H j),
  simp,      
end

instance : ring (matrix R n n) := {
mul := (*),
mul_assoc := mul_assoc,
mul_one := mul_one,
one := identity_matrix,
one_mul := one_mul,
left_distrib := left_distrib,
right_distrib := right_distrib,
..matrix.add_comm_group
}

def smul (a : R) (M : matrix R m n) :
matrix R m n := λ i j, a * M i j

instance : has_scalar R (matrix R m n) := ⟨smul⟩

theorem smul_add (s : R) (m1 m2 : matrix R m n) : s • (m1 + m2) = s • m1 + s • m2 := 
by funext i j; exact mul_add s (m1 i j) (m2 i j)

theorem add_smul (r s : R) (M : matrix R m n) : (r + s) • M = r • M + s • M :=
by funext i j; exact add_mul r s (M i j)

theorem mul_smul (s t : R) (M : matrix R m n) : (s * t) • M = s • (t • M) := 
by funext i j; exact _root_.mul_assoc s t (M i j)

theorem one_smul (M : matrix R m n) : (1 : R) • M = M :=
by funext i j; exact _root_.one_mul (M i j)

instance : module R (matrix R m n) :=
{
  smul_add := smul_add,
  add_smul := add_smul,
  mul_smul := mul_smul,
  one_smul := one_smul,
}

end matrix
