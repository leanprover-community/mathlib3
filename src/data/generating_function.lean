/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.power_series
import data.stream.basic
import data.nat.fib
import tactic

/-!
# Generating functions

-/

def generating_function {R : Type*} [comm_semiring R] (a : ℕ → R) :
  power_series R :=
power_series.mk a

@[simp] lemma coeff_generating_function {R : Type*} [comm_semiring R] (a : ℕ → R) (n : ℕ) :
  power_series.coeff R n (generating_function a) = a n :=
power_series.coeff_mk _ _

def exponential_generating_function {K : Type*} [discrete_field K] (a : ℕ → K) :
  power_series K :=
power_series.mk $ λ n, a n / n.fact

def bell_series {R : Type*} [comm_semiring R] (p : ℕ) (a : ℕ → R) :
  power_series R :=
power_series.mk $ λ n, a (p^n)

def geometric_sequence {G : Type*} [monoid G] (x : G) (n : ℕ) := x^n

@[simp] lemma geometric_sequence_one (G : Type*) [monoid G] :
  geometric_sequence (1 : G) = λ n, 1 :=
funext $ λ n, one_pow n

section
open power_series

@[simp] lemma units.coe_mk_of_mul_eq_one {G : Type*} [comm_monoid G] {x y : G} (h : x * y = 1) :
  (units.mk_of_mul_eq_one x y h : G) = x := rfl

@[simp] lemma power_series.coeff_mul_C {R : Type*} [comm_semiring R] (n : ℕ) (φ : power_series R) (r : R) :
  coeff R n (φ * (C R r)) = (coeff R n φ) * r :=
begin
  rw [coeff_mul n φ, finset.sum_eq_single (n,0)],
  { rw [coeff_C, if_pos rfl] },
  { rintro ⟨i,j⟩ hij hne,
    by_cases hj : j = 0,
    { subst hj, simp at *, contradiction },
    { simp [coeff_C, hj] } },
  { intro h, exfalso, apply h, simp },
end

@[simp] lemma power_series.coeff_succ_mul_X {R : Type*} [comm_semiring R] (n : ℕ) (φ : power_series R) :
  coeff R (n+1) (φ * X) = (coeff R n φ) :=
begin
  rw [coeff_mul _ φ, finset.sum_eq_single (n,1)],
  { rw [coeff_X, if_pos rfl, mul_one] },
  { rintro ⟨i,j⟩ hij hne,
    by_cases hj : j = 1,
    { subst hj, simp at *, contradiction },
    { simp [coeff_X, hj] } },
  { intro h, exfalso, apply h, simp },
end

@[simp] lemma power_series.coeff_zero_mul_X {R : Type*} [comm_semiring R] (φ : power_series R) :
  coeff R 0 (φ * X) = 0 :=
begin
  rw [coeff_mul _ φ, finset.sum_eq_zero],
  rintro ⟨i,j⟩ hij,
  obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0, { simpa using hij },
  simp,
end

lemma generating_function_geometric_sequence {K : Type*} [discrete_field K] (x : K) :
  generating_function (geometric_sequence x) = (1 - C K x * X)⁻¹ :=
begin
  have invertible : (1 - C K x * X) * (1 - C K x * X)⁻¹ = 1,
  { apply power_series.mul_inv,
    simpa only [ring_hom.map_sub, ring_hom.map_mul, ring_hom.map_one,
      constant_coeff_X, mul_zero, sub_zero] using one_ne_zero },
  suffices : generating_function (geometric_sequence x) * (1 - ((C K) x * X)) = 1,
  { apply (units.mul_right_inj (units.mk_of_mul_eq_one _ _ invertible)).mp,
    simpa [invertible] },
  ext n,
  rw [mul_sub, mul_one, add_monoid_hom.map_sub, coeff_one, ← mul_assoc],
  rw [coeff_generating_function (geometric_sequence x)],
  cases n,
  { rw [power_series.coeff_zero_mul_X ((generating_function (geometric_sequence x)) * C K x)],
    simp [geometric_sequence] },
  { rw [power_series.coeff_succ_mul_X n ((generating_function (geometric_sequence x)) * C K x)],
    rw [power_series.coeff_mul_C n (generating_function (geometric_sequence x))],
    rw [coeff_generating_function (geometric_sequence x)],
    simp [geometric_sequence, pow_succ', if_neg (nat.succ_ne_zero n)] }
end

lemma generating_function_const_one (K : Type*) [discrete_field K] :
  generating_function (λ n, (1 : K)) = (1 - X)⁻¹ :=
calc generating_function (λ n, (1 : K))
      = generating_function (geometric_sequence 1) : by simp
  ... = (1 - C K 1 * X)⁻¹                          : generating_function_geometric_sequence 1
  ... = (1 - X)⁻¹                                  : by simp

end

namespace nat
universe variables u
variables {X : ℕ → Sort u} (f : Π n, (Π (m:fin n), X m) → X n)

protected def strong_recursion_aux :
  Π n m, m < n → X m
| 0     := λ _ h, absurd h (not_lt_zero _)
| (n+1) := λ m h,
(lt_or_eq_of_le (le_of_lt_succ h)).by_cases
  (strong_recursion_aux n m)
  (λ e, f _ (λ k, strong_recursion_aux n _ $ lt_of_lt_of_le k.2 $ le_of_eq e))

def strong_recursion (n : ℕ) : X n :=
nat.strong_recursion_aux f (n+1) n $ n.lt_succ_self

@[simp] lemma strong_recursion_aux_lt (m n : ℕ) (h : m < n) :
  nat.strong_recursion_aux f n m h = strong_recursion f m :=
begin
  obtain ⟨k, rfl⟩ : ∃ k, n = m + 1 + k :=
  by simpa [add_right_comm] using nat.exists_eq_add_of_lt h,
  induction k with k ih, { refl },
  have hm : m < m + 1 + k, by linarith,
  rw ← ih hm,
  exact dif_pos hm,
end

lemma strong_recursion_apply (n : ℕ) :
  strong_recursion f n = f n (λ i, strong_recursion f i) :=
begin
  show nat.strong_recursion_aux f (n+1) n _ = _,
  show dite (n < n) _ _ = _,
  rw [dif_neg (lt_irrefl n)],
  show dite (n = n) _ _ = _,
  rw [dif_pos rfl],
  refine congr_arg (f n) _,
  funext k,
  apply strong_recursion_aux_lt,
end

end nat

section bernoulli

def bernoulli : ℕ → ℚ :=
nat.strong_recursion $ λ n bernoulli,
1 - finset.univ.sum (λ k, (n.choose ↑k) * (bernoulli k) / (n + 1 - k))

lemma bernoulli_def' (n : ℕ) :
  bernoulli n = 1 - finset.univ.sum (λ (k : fin n), (n.choose k) * (bernoulli k) / (n + 1 - k)) :=
nat.strong_recursion_apply _ _

lemma bernoulli_def (n : ℕ) :
  bernoulli n = 1 - (finset.range n).sum (λ k, (n.choose k) * (bernoulli k) / (n + 1 - k)) :=
begin
  rw bernoulli_def',
  congr' 1,
  refine finset.sum_bij (λ k hk, k) _ _ _ _,
  { rintro ⟨k, hk⟩ _, simp * },
  { rintro ⟨k, hk⟩ _, simp * },
  { intros, rwa fin.eq_iff_veq },
  { intros k hk, rw finset.mem_range at hk, exact ⟨⟨k, hk⟩, finset.mem_univ _, rfl⟩, }
end

@[simp] lemma bernoulli_zero  : bernoulli 0 = 1   := rfl
@[simp] lemma bernoulli_one   : bernoulli 1 = 1/2 := rfl
@[simp] lemma bernoulli_two   : bernoulli 2 = 1/6 := rfl
@[simp] lemma bernoulli_three : bernoulli 3 = 0   :=
begin
  rw [bernoulli_def],
  repeat { rw [finset.sum_range_succ, nat.choose_succ_succ], simp, norm_num1, },
end

@[simp] lemma bernoulli_four  : bernoulli 4 = -1/30 :=
begin
  rw [bernoulli_def],
  repeat
  { try { rw [finset.sum_range_succ] },
    try { rw [nat.choose_succ_succ] },
    simp, norm_num1, },
end


@[simp] lemma sum_bernoulli (n : ℕ) :
  (finset.range n).sum (λ k, (n.choose k : ℚ) * bernoulli k) = n :=
begin
  induction n with n ih, { simp, },
  { rw [finset.sum_range_succ'], }
end

def bernoulli_fun (n : ℕ) (l : list (ℕ × ℚ)) : ℚ :=
1 - (list.sum $ l.map $ λ ⟨k,B⟩, (n.choose k) * B / (n + 1 - k))

def bernoulli_aux : stream ((ℕ × ℚ) × list (ℕ × ℚ)) :=
stream.iterate
  (λ ⟨⟨n, B⟩, l⟩, ((n+1, bernoulli_fun (n+1) ((n, B) :: l)), ((n, B) :: l)))
  ((0, 1), [])

def bernoulli' (n : ℕ) : ℚ := (bernoulli_aux n).fst.snd

lemma bernoulli_aux_length : ∀ (n : ℕ), (bernoulli_aux n).snd.length = n
| 0     := rfl
| (n+1) :=
begin
  -- show (stream.nth (n+1) bernoulli_aux).snd.length = n + 1,
  change list.length (list.cons _) = n+1,
end

@[simp] lemma sum_bernoulli (n : ℕ) :
  (finset.range n).sum (λ k, (n.choose k : ℚ) * bernoulli k) = n :=
begin
  induction n with n ih, { simp, },
  {  }
end

lemma bernoulli_def (n : ℕ) :
  bernoulli n = 1 - (finset.range n).sum (λ k, (n.choose k) * (bernoulli k) / (n + 1 - k)) :=
begin
  induction n with n ih, { refl },
  rw bernoulli,
  -- apply nat.strong_induction_on n,
end

#eval bernoulli_aux 16
-- ((16, -3617/510), [(15, 0), (14, 7/6), (13, 0), (12, -691/2730), (11, 0), (10, 5/66), (9, 0), (8, -1/30), (7, 0), (6, 1/42), (5, 0), (4, -1/30), (3, 0), (2, 1/6), (1, 1/2), (0, 1)]) :=

-- lemma bernoulli_zero  : bernoulli 0 = 1   := rfl
-- lemma bernoulli_one   : bernoulli 1 = 1/2 := rfl
-- lemma bernoulli_two   : bernoulli 2 = 1/6 := rfl
-- lemma bernoulli_three : bernoulli 3 = 0   := by norm_num

end bernoulli
