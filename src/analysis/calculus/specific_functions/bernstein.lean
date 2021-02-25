/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.polynomial.derivative
import data.nat.choose
import linear_algebra.basis
import data.nat.pochhammer
import tactic.omega
import tactic.slim_check

namespace linear_map

universes u v

def iterate {R : Type u} [semiring R]
   {M : Type v} [add_comm_monoid M] [semimodule R M] (f : M →ₗ[R] M) : ℕ → (M →ₗ[R] M)
| 0 := linear_map.id
| (n+1) := (iterate n).comp f

@[simp] lemma iterate_apply {R : Type u} [semiring R]
   {M : Type v} [add_comm_monoid M] [semimodule R M] (f : M →ₗ[R] M) (n : ℕ) (m : M) :
  f.iterate n m = ((f : M → M)^[n] m) :=
begin
  induction n with n ih generalizing m,
  { refl, },
  { apply ih, },
end

instance {R : Type u} [semiring R] {M : Type v} [add_comm_monoid M] [semimodule R M] :
  has_pow (M →ₗ[R] M) ℕ :=
{ pow := λ f n, f.iterate n, }

@[simp] lemma pow_apply {R : Type u} [semiring R]
   {M : Type v} [add_comm_monoid M] [semimodule R M] (f : M →ₗ[R] M) (n : ℕ) (m : M) :
  (f^n) m = ((f : M → M)^[n] m) :=
iterate_apply f n m

end linear_map

@[simp] lemma polynomial.derivative_lhom_coe {R : Type*} [comm_ring R] :
  (polynomial.derivative_lhom R : polynomial R → polynomial R) = polynomial.derivative :=
rfl

noncomputable theory

meta def tactic.interactive.ls := tactic.interactive.library_search

@[simp]
lemma fin.succ_coe (n : ℕ) (i : fin n) : (i.cast_succ : ℕ) = (i : ℕ) :=
rfl

@[simp, norm_cast] theorem polynomial.coe_nat_inj' {m n : ℕ} : (↑m : polynomial ℤ) = ↑n ↔ m = n :=
sorry

open nat (choose)
open polynomial (X)

def bernstein_polynomial (n ν : ℕ) : polynomial ℤ := (choose n ν) * X^ν * (1 - X)^(n - ν)

-- Sanity check
example : bernstein_polynomial 3 2 = 3 * X^2 - 3 * X^3 :=
begin
  norm_num [bernstein_polynomial, choose],
  ring,
end

namespace bernstein_polynomial

lemma eval_at_0 (n ν : ℕ) : (bernstein_polynomial n ν).eval 0 = if ν = 0 then 1 else 0 :=
begin
  dsimp [bernstein_polynomial],
  split_ifs,
  { subst h, simp, },
  { simp [zero_pow (nat.pos_of_ne_zero h)], },
end

lemma eval_at_1 (n ν : ℕ) : (bernstein_polynomial n ν).eval 1 = if ν = n then 1 else 0 :=
begin
  dsimp [bernstein_polynomial],
  split_ifs,
  { subst h, simp, },
  { by_cases w : 0 < n - ν,
    { simp [zero_pow w], },
    { simp [(show n < ν, by omega), nat.choose_eq_zero_of_lt], }, },
end.

lemma derivative' (n ν : ℕ) :
  (bernstein_polynomial (n+1) (ν+1)).derivative =
    (n+1) * (bernstein_polynomial n ν - bernstein_polynomial n (ν + 1)) :=
begin
  dsimp [bernstein_polynomial],
  suffices :
    ↑((n + 1).choose (ν + 1)) * ((↑ν + 1) * X ^ ν) * (1 - X) ^ (n - ν)
      -(↑((n + 1).choose (ν + 1)) * X ^ (ν + 1) * (↑(n - ν) * (1 - X) ^ (n - ν - 1))) =
    (↑n + 1) * (↑(n.choose ν) * X ^ ν * (1 - X) ^ (n - ν) -
         ↑(n.choose (ν + 1)) * X ^ (ν + 1) * (1 - X) ^ (n - (ν + 1))),
  { simpa [polynomial.derivative_pow, ←sub_eq_add_neg], }, -- make this a simp lemma?
  conv_rhs { rw mul_sub, },
  -- -- We'll prove the two terms match up separately.
  refine congr (congr_arg has_sub.sub _) _,
  { simp only [←mul_assoc],
    refine congr (congr_arg (*) (congr (congr_arg (*) _) rfl)) rfl,
    -- Now it's just about binomial coefficients
    norm_cast,
    convert (nat.succ_mul_choose_eq _ _).symm, },
  { rw nat.sub_sub, rw [←mul_assoc,←mul_assoc], congr' 1,
    rw mul_comm , rw [←mul_assoc,←mul_assoc],  congr' 1,
    norm_cast,
    convert (nat.choose_mul_succ_eq n (ν + 1)).symm using 1,
    { convert mul_comm _ _ using 2,
      simp, },
    { apply mul_comm, }, },
end

lemma derivative (n ν : ℕ) :
  (bernstein_polynomial n (ν+1)).derivative =
    n * (bernstein_polynomial (n-1) ν - bernstein_polynomial (n-1) (ν+1)) :=
begin
  cases n,
  { simp [bernstein_polynomial], },
  { apply derivative', }
end

lemma derivative_zero (n : ℕ) :
  (bernstein_polynomial n 0).derivative = -n * bernstein_polynomial (n-1) 0 :=
begin
  dsimp [bernstein_polynomial],
  simp [polynomial.derivative_pow],
end

lemma iterate_derivative_at_zero_eq_zero_of_lt (n : ℕ) {ν k : ℕ} :
  k < ν → (polynomial.derivative^[k] (bernstein_polynomial n ν)).eval 0 = 0 :=
begin
  cases ν,
  { rintro ⟨⟩, },
  { intro w,
    replace w := nat.lt_succ_iff.mp w,
    revert w,
    induction k with k ih generalizing n ν,
    { simp [eval_at_0], rintro ⟨⟩, },
    { simp only [derivative, int.coe_nat_eq_zero, int.nat_cast_eq_coe_nat, mul_eq_zero,
        function.comp_app, function.iterate_succ,
        polynomial.iterate_derivative_sub, polynomial.iterate_derivative_coe_nat_mul,
        polynomial.eval_mul, polynomial.eval_nat_cast, polynomial.eval_sub],
      intro h,
      right,
      rw ih,
      simp only [sub_zero],
      convert @ih (n-1) (ν-1) _,
      { omega, },
      { omega, },
      { exact le_of_lt h, }, }, },
end

@[simp]
lemma iterate_derivative_succ_at_zero_eq_zero (n ν : ℕ) :
  (polynomial.derivative^[ν] (bernstein_polynomial n (ν+1))).eval 0 = 0 :=
iterate_derivative_at_zero_eq_zero_of_lt n (lt_add_one ν)

@[simp]
lemma iterate_derivative_self_at_0 (n ν : ℕ) :
  (polynomial.derivative^[ν] (bernstein_polynomial n ν)).eval 0 = n.falling_factorial ν :=
begin
  induction ν with ν ih generalizing n,
  { simp [eval_at_0], },
  { simp [derivative, ih],
    rw [nat.falling_factorial_eq_mul_left],
    push_cast, }
end

-- lemma iterate_derivative_at_one_eq_zero_of_lt (n : ℕ) {ν k : ℕ} :
--   ν < k → (polynomial.derivative^[k] (bernstein_polynomial n ν)).eval 1 = 0 :=
-- begin
--   induction k with k ih,
--   { rintro ⟨⟩, },
--   { induction ν,

--     simp [derivative_zero], },
-- end

-- @[simp]
-- lemma iterate_derivative_succ_at_zero_eq_zero (n ν : ℕ) :
--   (polynomial.derivative^[ν] (bernstein_polynomial n (ν+1))).eval 0 = 0 :=
-- iterate_derivative_at_zero_eq_zero_of_lt n (lt_add_one ν)

-- @[simp]
-- lemma iterate_derivative_self_at_0 (n ν : ℕ) :
--   (polynomial.derivative^[ν] (bernstein_polynomial n ν)).eval 0 = n.falling_factorial ν :=
-- begin
--   induction ν with ν ih generalizing n,
--   { simp [eval_at_0], },
--   { simp [derivative, ih],
--     rw [nat.falling_factorial_eq_mul_left],
--     push_cast, }
-- end


@[simp] lemma fin.init_lambda {n : ℕ} {α : fin (n+1) → Type*} {q : Π i, α i} :
  fin.init (λ k : fin (n+1), q k) = (λ k : fin n, q k.cast_succ) := rfl

open submodule

lemma apply_mem_span_of_mem_span {R : Type*} [semiring R]
   {M : Type*} [add_comm_monoid M] [semimodule R M]
   {N : Type*} [add_comm_monoid N] [semimodule R N]
   (f : M →ₗ[R] N) {x : M} {s : set M} (h : x ∈ submodule.span R s) :
   f x ∈ submodule.span R (f '' s) :=
begin
  simp only [submodule.mem_span, submodule.mem_map, submodule.span_image] at h ⊢,
  exact ⟨x, ⟨h, rfl⟩⟩,
end

lemma not_mem_span_of_apply_not_mem_span {R : Type*} [semiring R]
   {M : Type*} [add_comm_monoid M] [semimodule R M]
   {N : Type*} [add_comm_monoid N] [semimodule R N]
   (f : M →ₗ[R] N) {x : M} {s : set M} (h : f x ∉ submodule.span R (f '' s)) :
   x ∉ submodule.span R s :=
not.imp h (apply_mem_span_of_mem_span f)

lemma ne_of_apply_ne {α β : Sort*} (f : α → β) {x y : α} {h : f x ≠ f y} : x ≠ y :=
λ (w : x = y), h (congr_arg f w)

lemma eval_zero {R : Type*} [semiring R] (p : polynomial R) : p.eval 0 = p.coeff 0 :=
begin
  sorry,
end

@[simp]
lemma eval_zero_map {R S : Type*} [comm_ring R] [comm_ring S] (f : R →+* S) (p : polynomial R) :
  (p.map f).eval 0 = f (p.eval 0) :=
by simp [eval_zero]

lemma linear_independent_aux (n k : ℕ) (h : k ≤ n + 1):
  linear_independent ℚ (λ ν : fin k, (bernstein_polynomial n ν).map (algebra_map ℤ ℚ)) :=
begin
  induction k with k ih,
  { apply linear_independent_empty_type,
    rintro ⟨⟨n, ⟨⟩⟩⟩, },
  { apply linear_independent_fin_succ'.mpr,
    fsplit,
    { exact ih (le_of_lt h), },
    { -- The actual work!
      -- We show that the k-th derivative at 0 doesn't vanish,
      -- but vanishes for everything in the span.
      clear ih,
      simp only [fin.coe_last, fin.init_lambda],
      dsimp,
      apply not_mem_span_of_apply_not_mem_span ((polynomial.derivative_lhom ℚ)^k),
      simp only [not_exists, not_and, submodule.mem_map, submodule.span_image],
      intros p h,
      simp,
      apply ne_of_apply_ne (polynomial.eval (0 : ℚ)),
      simp,
      suffices : (polynomial.derivative^[k] p).eval 0 = 0,
      sorry,
      apply span_induction h,
      { simp, rintro ⟨a, w⟩, rw [iterate_derivative_at_zero_eq_zero_of_lt _ w], },
      { simp, },
      { intros x y hx hy, simp [hx, hy], },
      { intros a x h, simp [h], },
      } }
end

lemma linear_independent (n : ℕ) :
  linear_independent ℚ (λ ν : fin (n+1), (bernstein_polynomial n ν).map (algebra_map ℤ ℚ)) :=
linear_independent_aux n (n+1) (le_refl _)

end bernstein_polynomial
