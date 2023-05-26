/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Anatole Dedecker
-/
import measure_theory.integral.fund_thm_calculus
import analysis.normed_space.exponential
import analysis.quaternion
import algebra.lie.of_associative
import analysis.special_functions.exponential
import analysis.calculus.fderiv_symmetric
import analysis.calculus.mean_value
import analysis.calculus.cont_diff

/-! More lemmas aboutderiviatives of `exp`.

This follows https://physics.stackexchange.com/a/41671/185147. -/

@[simp]
lemma linear_map.smul_right_eq_op_smul (R M A) [comm_semiring R] [add_comm_monoid M] [semiring A]
  [module R M] [module R A] [is_scalar_tower R A A]
  (f : M →ₗ[R] A) (a : A) : f.smul_right a = mul_opposite.op a • f := rfl

@[simp]
lemma continuous_linear_map.smul_right_eq_op_smul (R M A) [comm_semiring R] [add_comm_monoid M] [semiring A]
  [module R M] [module R A] [is_scalar_tower R A A]
  [topological_space M] [topological_space A] [topological_semiring A]
  (f : M →L[R] A) (a : A) : f.smul_right a = mul_opposite.op a • f := rfl

  --- f x • a = f x * a

variables {𝕂 E 𝔸 𝔹 : Type*}

open_locale topology
open asymptotics filter

variables [normed_ring 𝔸] [normed_algebra ℝ 𝔸] [complete_space 𝔸]
variables [normed_add_comm_group E] [normed_space ℝ E] [complete_space E] [finite_dimensional ℝ E]

-- to make the goal view readable
notation (name := deriv) `∂` binders `, ` r:(scoped:67 f, deriv f) := r
local notation `e` := exp ℝ

attribute [continuity] exp_continuous

open mul_opposite

lemma deriv_exp_aux (A : ℝ → 𝔸) (r t : ℝ)
  (hA : differentiable_at ℝ A r) :
  exp ℝ (-t • A r) * deriv (λ x, exp ℝ (t • A x)) r =
    (∫ s : ℝ in 0..t, exp ℝ (-s • A r) * deriv A r * exp ℝ (s • A r)) :=
begin
  revert t,
  rw ←function.funext_iff,
  refine eq_of_fderiv_eq (_ : differentiable ℝ _) _ _ (0 : ℝ) _,
  { refine differentiable.mul
    (differentiable.comp (λ x, (has_deriv_at_exp_smul_const _ _).differentiable_at)
      differentiable_neg : _) _,
    sorry, },
  { sorry },
  swap,
  { simp },
  { intro t,
    ext1,
    rw [←deriv,←deriv],
    have : continuous_at (λ s, exp ℝ (-s • A r) * deriv A r * exp ℝ (s • A r)) r,
    { refine ((exp_continuous.continuous_at.comp (continuous_at_neg.smul continuous_at_const)).mul
        _).mul
          (exp_continuous.continuous_at.comp (continuous_at_id.smul continuous_at_const)),
      -- oh no
      sorry },
    rw interval_integral.deriv_integral_right,
    { rw deriv_mul,
      have deriv_comm : deriv (λ (y : ℝ), deriv (λ (x : ℝ), exp ℝ (y • A x)) r) t =
        deriv (λ (x : ℝ), deriv (λ (y : ℝ), exp ℝ (y • A x)) t) r,
      { -- this one is probably really annoying
        have := @second_derivative_symmetric,
        sorry },
      { rw deriv_comm,
        simp_rw [(has_deriv_at_exp_smul_const' (_ : 𝔸) t).deriv],
        rw deriv_mul,
        simp_rw [mul_add, ←add_assoc, ←mul_assoc],
        rw [add_right_comm],
        convert zero_add _,
        rw [←add_mul],
        convert zero_mul _,
        rw [←(has_deriv_at_exp_smul_const (_ : 𝔸) _).deriv, ←eq_neg_iff_add_eq_zero],
        change deriv ((λ t : ℝ, exp ℝ (t • A r)) ∘ has_neg.neg) t = _,
        rw [deriv.scomp t, deriv_neg, neg_one_smul],
        { exact (has_deriv_at_exp_smul_const _ _).differentiable_at },
        { exact differentiable_at_id.neg },
        { apply_instance },
        { exact hA },
        { change differentiable_at ℝ (exp ℝ ∘ _) _,
          refine differentiable_at.comp _ _ (hA.const_smul _),
          -- uh oh, this looks circular
          sorry }, },
      { exact has_deriv_at.differentiable_at
          ((has_deriv_at_exp_smul_const' (A r) (-t)).scomp _ (has_deriv_at_neg _)) },
      { sorry } },
    { sorry },
    { sorry },
    { have h : continuous_at (λ t : ℝ, exp ℝ (t • A r)) t :=
        exp_continuous.continuous_at.comp (continuous_at_id.smul continuous_at_const),
      have hn : continuous_at (λ t : ℝ, exp ℝ (-t • A r)) t :=
        exp_continuous.continuous_at.comp (continuous_at_neg.smul continuous_at_const),
      refine (hn.mul continuous_at_const).mul h,}, },
end

/-- Non-commutative version of `deriv_exp`. -/
lemma deriv_exp' (A : ℝ → 𝔸) (r : ℝ) (h : differentiable_at ℝ A r) :
  deriv (λ x, exp ℝ (A x)) r = (∫ s : ℝ in 0..1, exp ℝ ((1 - s) • A r) * deriv A r * exp ℝ (s • A r)) :=
begin
  apply (is_unit_exp ℝ (-A r)).mul_left_cancel,
  have := deriv_exp_aux A r 1 h,
  simp_rw [neg_one_smul, one_smul] at this,
  -- have hA : ∀ r s : ℝ, commute (A r) (-s • A r) := λ r s, commute.refl,
  simp_rw [sub_eq_add_neg, add_smul, one_smul,
    @exp_add_of_commute ℝ _ _ _ _ _ _ _ ((commute.refl (A _)).smul_right _)],
  rw this,
  -- `integral_const_mul` is not general enough!
  sorry,
end

/-- Non-commutative version of `has_deriv_at_exp`. -/
lemma has_deriv_at_exp' (A : ℝ → 𝔸) (A' : 𝔸) (r : ℝ) (h : has_deriv_at A A' r) :
  has_deriv_at (λ x, exp ℝ (A x)) (∫ (s : ℝ) in 0..1, exp ℝ ((1 - s) • A r) * A' * exp ℝ (s • A r)) r :=
begin
  sorry,
end

/-! ### Are the above proofs easier with `has_fderiv_at`? -/

/-- For every `t : ℝ`,

$\exp(-tA) \frac{∂}{∂x}(\exp(tA)) = \int_0^t \exp(-sA) \frac{∂A}{∂x} \exp(sA)$

Note we move the first term inside the derivative so that we can state this using `has_fderiv_at`.
-/
-- this proof is _really_ slow :(
lemma has_fderiv_at_exp_aux (A : E → 𝔸) (A' : E →L[ℝ] 𝔸) (t : ℝ) (x : E)
  (hA : has_fderiv_at A A' x) :
  has_fderiv_at (λ y, exp ℝ (-t • A x) * exp ℝ (t • A y))
    (∫ s : ℝ in 0..t, exp ℝ (-s • A x) • op (exp ℝ (s • A x)) • A') x :=
begin
  let intA := λ s : ℝ, exp ℝ (-s • A x) • op (exp ℝ (s • A x)) • A',
  have : continuous intA,
  -- this proofs works, commented out for speed
  sorry { refine continuous_clm_apply.2 (λ y, _),
    dsimp only [intA, continuous_linear_map.smul_apply, op_smul_eq_mul, smul_eq_mul],
    continuity },
  have := this.integral_has_strict_deriv_at 0 t,
  have LHS : has_fderiv_at (λ p : ℝ × E, exp ℝ (-p.1 • A x) * exp ℝ (p.1 • A p.2))
    (_ : _ →L[ℝ] 𝔸) (t, x),
  { refine has_fderiv_at.mul' _ _, rotate 2,
    change has_fderiv_at ((λ p : ℝ, e (p • A x)) ∘ (λ p : ℝ × E, -p.1)) _ (t, x),
    { refine has_fderiv_at.comp _ (has_fderiv_at_exp_smul_const' ℝ _ _) _, rotate 1,
      refine has_fderiv_at.neg (has_fderiv_at_fst) },
    sorry, -- uh oh, need the derivative of `λ (p : ℝ × E), e (p.fst • A p.snd)`
    sorry, },
  simp only [neg_smul, continuous_linear_map.smul_right_eq_op_smul,continuous_linear_map.smul_comp,
    continuous_linear_map.comp_neg, smul_neg] at LHS,
  simp only [smul_smul, ←op_mul] at LHS,
  rw [←exp_add_of_commute (commute.refl (_ : 𝔸)).neg_left, add_left_neg, exp_zero, op_one,
    one_smul] at LHS,
  sorry,
  -- have : has_strict_fderiv_at
  --   (λ p : ℝ × ℝ, ∫ s : ℝ in p.1..p.2, exp ℝ (-s • A x) • (mul_opposite.op (exp ℝ (s • A x))) • A')
  --   (_) (0, t) :=
  --   interval_integral.integral_has_strict_fderiv_at _ _ _ _ _,
  -- rw [neg_zero, zero_smul ℝ (_ : 𝔸), exp_zero, mul_opposite.op_one, one_smul, one_smul] at this,
  -- have := this.snd,
  -- sorry
end


-- lemma has_deriv_at_exp_aux (A : ℝ → 𝔸) (A' : 𝔸) (t : ℝ) (x : ℝ)
--   (hA : has_deriv_at A A' x) :
--   has_deriv_at (λ y, exp ℝ (-t • A x) * exp ℝ (t • A y))
--     (∫ s : ℝ in 0..t, exp ℝ (-s • A x) * A' * exp ℝ (s • A x)) x :=
-- begin
--   let intA := λ s : ℝ, exp ℝ (-s • A x) • op (exp ℝ (s • A x)) • A',
--   have : continuous intA,
--   sorry { refine continuous_clm_apply.2 (λ y, _),
--     dsimp only [intA, continuous_linear_map.smul_apply, op_smul_eq_mul, smul_eq_mul],
--     continuity },
--   have := this.integral_has_strict_deriv_at 0 t,
--   have : has_deriv_at (λ p : ℝ, exp ℝ (-p • A x) * exp ℝ (p • A x)) (_) t,
--   { refine has_fderiv_at.mul' _ _, rotate 2,
--     sorry,
--     sorry,
--     sorry,
--     sorry, },
--   -- have : has_strict_fderiv_at
--   --   (λ p : ℝ × ℝ, ∫ s : ℝ in p.1..p.2, exp ℝ (-s • A x) • (mul_opposite.op (exp ℝ (s • A x))) • A')
--   --   (_) (0, t) :=
--   --   interval_integral.integral_has_strict_fderiv_at _ _ _ _ _,
--   -- rw [neg_zero, zero_smul ℝ (_ : 𝔸), exp_zero, mul_opposite.op_one, one_smul, one_smul] at this,
--   -- have := this.snd,
--   -- sorry
-- end

-- an entirely different approach from 10.1007/978-3-540-44953-9_2, Chapter 2, pg 37

lemma has_deriv_at_exp'' (A : ℝ → 𝔸) (A' : 𝔸) (r : ℝ) (h : has_deriv_at A A' r) :
  has_deriv_at (λ x, exp ℝ (A x)) (∫ (s : ℝ) in 0..1, exp ℝ ((1 - s) • A r) * A' * exp ℝ (s • A r)) r :=
begin
  simp_rw exp_eq_tsum,
  sorry
end
