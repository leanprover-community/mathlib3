/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.polynomial.derivative
import data.polynomial.algebra_map
import data.nat.choose
import linear_algebra.basis
import data.nat.pochhammer
import tactic.omega

namespace polynomial

section
variables {R : Type*} [comm_ring R]

lemma derivative_comp_one_sub_X (p : polynomial R) :
  (p.comp (1-X)).derivative = -p.derivative.comp (1-X) :=
begin
  simp [derivative_comp],
end

@[simp]
lemma iterate_derivative_comp_one_sub_X (p : polynomial R) (k : ℕ) :
  derivative^[k] (p.comp (1-X)) = (-1)^k * (derivative^[k] p).comp (1-X) :=
begin
  induction k with k ih generalizing p,
  { simp, },
  { simp [ih p.derivative, iterate_derivative_neg, derivative_comp, pow_succ], },
end
end

end polynomial

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


noncomputable theory


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

lemma flip (n ν : ℕ) (h : ν ≤ n) :
  (bernstein_polynomial n ν).comp (1-X) = bernstein_polynomial n (n-ν) :=
begin
  dsimp [bernstein_polynomial],
  simp [h, nat.sub_sub_assoc, mul_right_comm],
end

lemma flip' (n ν : ℕ) (h : ν ≤ n) :
  bernstein_polynomial n ν = (bernstein_polynomial n (n-ν)).comp (1-X) :=
begin
  rw [←flip _ _ h, polynomial.comp_assoc],
  simp,
end

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
  { simpa [polynomial.derivative_pow, ←sub_eq_add_neg], }, -- make `derivative_pow` a simp lemma?
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

lemma derivative_succ (n ν : ℕ) :
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
    { simp only [derivative_succ, int.coe_nat_eq_zero, int.nat_cast_eq_coe_nat, mul_eq_zero,
        function.comp_app, function.iterate_succ,
        polynomial.iterate_derivative_sub, polynomial.iterate_derivative_cast_nat_mul,
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
lemma iterate_derivative_at_0 (n ν : ℕ) :
  (polynomial.derivative^[ν] (bernstein_polynomial n ν)).eval 0 = n.falling_factorial ν :=
begin
  induction ν with ν ih generalizing n,
  { simp [eval_at_0], },
  { simp [derivative_succ, ih],
    rw [nat.falling_factorial_eq_mul_left],
    push_cast, }
end

lemma iterate_derivative_at_0_ne_zero (n ν : ℕ) (h : ν ≤ n) :
  (polynomial.derivative^[ν] (bernstein_polynomial n ν)).eval 0 ≠ 0 :=
begin
  simp only [int.coe_nat_eq_zero, bernstein_polynomial.iterate_derivative_at_0, ne.def],
  exact nat.falling_factorial_ne_zero h,
end

/--
Rather than redoing the work of evaluating the derivatives at 1,
we use the symmetry of the Bernstein polynomials.
-/
lemma iterate_derivative_at_one_eq_zero_of_lt (n : ℕ) {ν k : ℕ} :
  k < n - ν → (polynomial.derivative^[k] (bernstein_polynomial n ν)).eval 1 = 0 :=
begin
  intro w,
  rw flip' _ _ (show ν ≤ n, by omega),
  simp [polynomial.eval_comp, iterate_derivative_at_zero_eq_zero_of_lt n w],
end


@[simp]
lemma iterate_derivative_at_1 (n ν : ℕ) (h : ν ≤ n) :
  (polynomial.derivative^[n-ν] (bernstein_polynomial n ν)).eval 1 =
    (-1)^(n-ν) * n.falling_factorial (n-ν) :=
begin
  rw flip' _ _ h,
  simp [polynomial.eval_comp],
end

@[simp] lemma int.neg_one_pow_ne_zero {n : ℕ} : (-1 : ℤ)^n = 0 ↔ false :=
begin
  simp only [iff_false],
  exact pow_ne_zero _ (by norm_num)
end

lemma iterate_derivative_at_1_ne_zero (n ν : ℕ) (h : ν ≤ n) :
  (polynomial.derivative^[n-ν] (bernstein_polynomial n ν)).eval 1 ≠ 0 :=
begin
  simp only [int.coe_nat_eq_zero, bernstein_polynomial.iterate_derivative_at_1 _ _ h, ne.def,
    false_or, int.coe_nat_eq_zero, int.neg_one_pow_ne_zero, mul_eq_zero],
  exact nat.falling_factorial_ne_zero (nat.sub_le _ _),
end

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
  apply polynomial.induction_on' p,
  { intros p q hp hq, simp [hp, hq], },
  { intros n r, cases n; simp [pow_succ], }
end

@[simp]
lemma eval_zero_map {R S : Type*} [semiring R] [semiring S] (f : R →+* S) (p : polynomial R) :
  (p.map f).eval 0 = f (p.eval 0) :=
by simp [eval_zero]

@[simp]
lemma eval_one_map {R S : Type*} [semiring R] [semiring S] (f : R →+* S) (p : polynomial R) :
  (p.map f).eval 1 = f (p.eval 1) :=
begin
  apply polynomial.induction_on' p,
  { intros p q hp hq, simp [hp, hq], },
  { intros n r, simp, }
end

-- We could probably also add `eval_bit0_map` and `eval_bit1_map`, as well as
-- `eval_nat_cast_map` and `eval_int_cast_map`.

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
      -- We show that the (n-k)-th derivative at 1 doesn't vanish,
      -- but vanishes for everything in the span.
      clear ih,
      simp only [nat.succ_eq_add_one, add_le_add_iff_right] at h,
      simp only [fin.coe_last, fin.init_lambda],
      dsimp,
      apply not_mem_span_of_apply_not_mem_span ((polynomial.derivative_lhom ℚ)^(n-k)),
      simp only [not_exists, not_and, submodule.mem_map, submodule.span_image],
      intros p m,
      apply ne_of_apply_ne (polynomial.eval (1 : ℚ)),
      simp only [ne.def, polynomial.derivative_lhom_coe, polynomial.iterate_derivative_map,
        ring_hom.eq_int_cast, linear_map.pow_apply, bernstein_polynomial.eval_one_map],
      -- The right hand side is nonzero,
      -- so it will suffice to show the left hand side is always zero.
      suffices : (polynomial.derivative^[n-k] p).eval 1 = 0,
      { rw [this],
        norm_cast,
        refine (iterate_derivative_at_1_ne_zero n k h).symm, },
      apply span_induction m,
      { simp,
        rintro ⟨a, w⟩, simp only [fin.coe_mk],
        rw [iterate_derivative_at_one_eq_zero_of_lt _ (show n - k < n - a, by omega)], },
      { simp, },
      { intros x y hx hy, simp [hx, hy], },
      { intros a x h, simp [h], }, }, },
end

lemma linear_independent (n : ℕ) :
  linear_independent ℚ (λ ν : fin (n+1), (bernstein_polynomial n ν).map (algebra_map ℤ ℚ)) :=
linear_independent_aux n (n+1) (le_refl _)

end bernstein_polynomial
