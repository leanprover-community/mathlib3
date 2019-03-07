/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

A proof of Hensel's lemma on ℤ_p, roughly following Keith Conrad's writeup:
http://www.math.uconn.edu/~kconrad/blurbs/gradnumthy/hensel.pdf
-/

import data.padics.padic_integers data.polynomial data.nat.choose topology.metric_space.cau_seq_filter
import analysis.specific_limits topology.instances.polynomial
import tactic.ring

noncomputable theory

local attribute [instance] classical.prop_decidable

lemma padic_polynomial_dist {p : ℕ} [p.prime] (F : polynomial ℤ_[p]) (x y : ℤ_[p]) :
  ∥F.eval x - F.eval y∥ ≤ ∥x - y∥ :=
let ⟨z, hz⟩ := F.eval_sub_factor x y in calc
  ∥F.eval x - F.eval y∥ = ∥z∥ * ∥x - y∥ : by simp [hz]
    ... ≤ 1 * ∥x - y∥ : mul_le_mul_of_nonneg_right (padic_norm_z.le_one _) (norm_nonneg _)
    ... = ∥x - y∥ : by simp

open filter metric

private lemma comp_tendsto_lim {p : ℕ} [p.prime] {F : polynomial ℤ_[p]} (ncs : cau_seq ℤ_[p] norm) :
  tendsto (λ i, F.eval (ncs i)) at_top (nhds (F.eval ncs.lim)) :=
@tendsto.comp _ _ _ ncs
  (λ k, F.eval k)
  _ _ _
  (tendsto_limit ncs)
  (continuous_iff_continuous_at.1 F.continuous_eval _)

section
parameters {p : ℕ} [nat.prime p] {ncs : cau_seq ℤ_[p] norm} {F : polynomial ℤ_[p]} {a : ℤ_[p]}
           (ncs_der_val : ∀ n, ∥F.derivative.eval (ncs n)∥ = ∥F.derivative.eval a∥)
include ncs_der_val

private lemma ncs_tendsto_const :
  tendsto (λ i, ∥F.derivative.eval (ncs i)∥) at_top (nhds ∥F.derivative.eval a∥) :=
by convert tendsto_const_nhds; ext; rw ncs_der_val

private lemma ncs_tendsto_lim :
  tendsto (λ i, ∥F.derivative.eval (ncs i)∥) at_top (nhds (∥F.derivative.eval ncs.lim∥)) :=
tendsto.comp (comp_tendsto_lim _) (continuous_iff_continuous_at.1 continuous_norm _)

private lemma norm_deriv_eq : ∥F.derivative.eval ncs.lim∥ = ∥F.derivative.eval a∥ :=
tendsto_nhds_unique at_top_ne_bot ncs_tendsto_lim ncs_tendsto_const

end

section
parameters {p : ℕ} [nat.prime p] {ncs : cau_seq ℤ_[p] norm} {F : polynomial ℤ_[p]}
           (hnorm : tendsto (λ i, ∥F.eval (ncs i)∥) at_top (nhds 0))
include hnorm

private lemma tendsto_zero_of_norm_tendsto_zero : tendsto (λ i, F.eval (ncs i)) at_top (nhds 0) :=
tendsto_iff_norm_tendsto_zero.2 (by simpa using hnorm)

lemma limit_zero_of_norm_tendsto_zero : F.eval ncs.lim = 0 :=
tendsto_nhds_unique at_top_ne_bot (comp_tendsto_lim _) tendsto_zero_of_norm_tendsto_zero

end

section hensel
open nat

parameters {p : ℕ} [nat.prime p] {F : polynomial ℤ_[p]} {a : ℤ_[p]}
           (hnorm : ∥F.eval a∥ < ∥F.derivative.eval a∥^2) (hnsol : F.eval a ≠ 0)
include hnorm

private def T : ℝ := ∥(F.eval a).val / ((F.derivative.eval a).val)^2∥

private lemma deriv_sq_norm_pos : 0 < ∥F.derivative.eval a∥ ^ 2 :=
lt_of_le_of_lt (norm_nonneg _) hnorm

private lemma deriv_sq_norm_ne_zero : ∥F.derivative.eval a∥^2 ≠ 0 := ne_of_gt deriv_sq_norm_pos

private lemma deriv_norm_ne_zero : ∥F.derivative.eval a∥ ≠ 0 :=
λ h, deriv_sq_norm_ne_zero (by simp [*, _root_.pow_two])

private lemma deriv_norm_pos : 0 < ∥F.derivative.eval a∥ :=
lt_of_le_of_ne (norm_nonneg _) (ne.symm deriv_norm_ne_zero)

private lemma deriv_ne_zero : F.derivative.eval a ≠ 0 := mt (norm_eq_zero _).2 deriv_norm_ne_zero

private lemma T_def : T = ∥F.eval a∥ / ∥F.derivative.eval a∥^2 :=
calc T = ∥(F.eval a).val∥ / ∥((F.derivative.eval a).val)^2∥ : norm_div _ _
   ... = ∥F.eval a∥ / ∥(F.derivative.eval a)^2∥ : by simp [norm, padic_norm_z]
   ... = ∥F.eval a∥ / ∥(F.derivative.eval a)∥^2 : by simp [pow, monoid.pow]

private lemma T_lt_one : T < 1 :=
let h := (div_lt_one_iff_lt deriv_sq_norm_pos).2 hnorm in
by rw T_def; apply h

private lemma T_pow {n : ℕ} (hn : n > 0) : T ^ n < 1 :=
have T ^ n ≤ T ^ 1, from pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt T_lt_one) (succ_le_of_lt hn),
lt_of_le_of_lt (by simpa) T_lt_one

private lemma T_pow' (n : ℕ) : T ^ (2 ^ n) < 1 := (T_pow (nat.pow_pos (by norm_num) _))

private lemma T_pow_nonneg (n : ℕ) : T ^ n ≥ 0 := pow_nonneg (norm_nonneg _) _

private def ih (n : ℕ) (z : ℤ_[p]) : Prop :=
∥F.derivative.eval z∥ = ∥F.derivative.eval a∥ ∧ ∥F.eval z∥ ≤ ∥F.derivative.eval a∥^2 * T ^ (2^n)

private lemma ih_0 : ih 0 a :=
⟨ rfl, by simp [T_def, mul_div_cancel' _ (ne_of_gt (deriv_sq_norm_pos hnorm))] ⟩

private lemma calc_norm_le_one {n : ℕ} {z : ℤ_[p]} (hz : ih n z) :
         ∥(↑(F.eval z) : ℚ_[p]) / ↑(F.derivative.eval z)∥ ≤ 1 :=
calc ∥(↑(F.eval z) : ℚ_[p]) / ↑(F.derivative.eval z)∥
    = ∥(↑(F.eval z) : ℚ_[p])∥ / ∥(↑(F.derivative.eval z) : ℚ_[p])∥ : norm_div _ _
... = ∥F.eval z∥ / ∥F.derivative.eval a∥ : by simp [hz.1]
... ≤ ∥F.derivative.eval a∥^2 * T^(2^n) / ∥F.derivative.eval a∥ :
  (div_le_div_right deriv_norm_pos).2 hz.2
... = ∥F.derivative.eval a∥ * T^(2^n) : div_sq_cancel (ne_of_gt deriv_norm_pos) _
... ≤ 1 : mul_le_one (padic_norm_z.le_one _) (T_pow_nonneg _) (le_of_lt (T_pow' _))

private lemma calc_deriv_dist {z z' z1 : ℤ_[p]} (hz' : z' = z - z1)
  (hz1 : ∥z1∥ = ∥F.eval z∥ / ∥F.derivative.eval a∥) {n} (hz : ih n z) :
  ∥F.derivative.eval z' - F.derivative.eval z∥ < ∥F.derivative.eval a∥ :=
calc
  ∥F.derivative.eval z' - F.derivative.eval z∥
    ≤ ∥z' - z∥ : padic_polynomial_dist _ _ _
... = ∥z1∥ : by simp [hz']
... = ∥F.eval z∥ / ∥F.derivative.eval a∥ : hz1
... ≤ ∥F.derivative.eval a∥^2 * T^(2^n) / ∥F.derivative.eval a∥ : (div_le_div_right deriv_norm_pos).2 hz.2
... = ∥F.derivative.eval a∥ * T^(2^n) : div_sq_cancel deriv_norm_ne_zero _
... < ∥F.derivative.eval a∥ : (mul_lt_iff_lt_one_right deriv_norm_pos).2 (T_pow (pow_pos (by norm_num) _))

private def calc_eval_z'  {z z' z1 : ℤ_[p]} (hz' : z' = z - z1) {n} (hz : ih n z)
  (h1 : ∥(↑(F.eval z) : ℚ_[p]) / ↑(F.derivative.eval z)∥ ≤ 1) (hzeq : z1 = ⟨_, h1⟩) :
  {q : ℤ_[p] // F.eval z' = q * z1^2} :=
have hdzne' : (↑(F.derivative.eval z) : ℚ_[p]) ≠ 0, from
  have hdzne : F.derivative.eval z ≠ 0,
    from mt (norm_eq_zero _).2 (by rw hz.1; apply deriv_norm_ne_zero; assumption),
  λ h, hdzne $ subtype.ext.2 h,
let ⟨q, hq⟩ := F.binom_expansion z (-z1) in
have ∥(↑(F.derivative.eval z) * (↑(F.eval z) / ↑(F.derivative.eval z)) : ℚ_[p])∥ ≤ 1,
  by {rw padic_norm_e.mul, apply mul_le_one, apply padic_norm_z.le_one, apply norm_nonneg, apply h1},
have F.derivative.eval z * (-z1) = -F.eval z, from calc
  F.derivative.eval z * (-z1)
    = (F.derivative.eval z) * -⟨↑(F.eval z) / ↑(F.derivative.eval z), h1⟩ : by rw [hzeq]
... = -((F.derivative.eval z) * ⟨↑(F.eval z) / ↑(F.derivative.eval z), h1⟩) : by simp
... = -(⟨↑(F.derivative.eval z) * (↑(F.eval z) / ↑(F.derivative.eval z)), this⟩) : subtype.ext.2 $ by simp
... = -(F.eval z) : by simp [mul_div_cancel' _ hdzne'],
have heq : F.eval z' = q * z1^2, by simpa [this, hz'] using hq,
⟨q, heq⟩

private def calc_eval_z'_norm {z z' z1 : ℤ_[p]} {n} (hz : ih n z) {q}
  (heq : F.eval z' = q * z1^2) (h1 : ∥(↑(F.eval z) : ℚ_[p]) / ↑(F.derivative.eval z)∥ ≤ 1)
  (hzeq : z1 = ⟨_, h1⟩) : ∥F.eval z'∥ ≤ ∥F.derivative.eval a∥^2 * T^(2^(n+1)) :=
calc ∥F.eval z'∥
    = ∥q∥ * ∥z1∥^2 : by simp [heq]
... ≤ 1 * ∥z1∥^2 : mul_le_mul_of_nonneg_right (padic_norm_z.le_one _) (pow_nonneg (norm_nonneg _) _)
... = ∥F.eval z∥^2 / ∥F.derivative.eval a∥^2 :
  by simp [hzeq, hz.1, div_pow _ (deriv_norm_ne_zero hnorm)]
... ≤ (∥F.derivative.eval a∥^2 * T^(2^n))^2 / ∥F.derivative.eval a∥^2 :
  (div_le_div_right deriv_sq_norm_pos).2 (pow_le_pow_of_le_left (norm_nonneg _) hz.2 _)
... = (∥F.derivative.eval a∥^2)^2 * (T^(2^n))^2 / ∥F.derivative.eval a∥^2 : by simp only [_root_.mul_pow]
... = ∥F.derivative.eval a∥^2 * (T^(2^n))^2 : div_sq_cancel deriv_sq_norm_ne_zero _
... = ∥F.derivative.eval a∥^2 * T^(2^(n + 1)) : by rw [←pow_mul]; refl

set_option eqn_compiler.zeta true

-- we need (ih k) in order to construct the value for k+1, otherwise it might not be an integer.
private def ih_n {n : ℕ} {z : ℤ_[p]} (hz : ih n z) : {z' : ℤ_[p] // ih (n+1) z'} :=
have h1 : ∥(↑(F.eval z) : ℚ_[p]) / ↑(F.derivative.eval z)∥ ≤ 1, from calc_norm_le_one hz,
let z1 : ℤ_[p] := ⟨_, h1⟩,
    z' : ℤ_[p] := z - z1 in
⟨ z',
  have hdist : ∥F.derivative.eval z' - F.derivative.eval z∥ < ∥F.derivative.eval a∥,
    from calc_deriv_dist rfl (by simp [z1, hz.1]) hz,
  have hfeq : ∥F.derivative.eval z'∥ = ∥F.derivative.eval a∥,
    begin
      rw [sub_eq_add_neg, ← hz.1, ←norm_neg (F.derivative.eval z)] at hdist,
      have := padic_norm_z.eq_of_norm_add_lt_right hdist,
      rwa [norm_neg, hz.1] at this
    end,
  let ⟨q, heq⟩ := calc_eval_z' rfl hz h1 rfl in
  have hnle : ∥F.eval z'∥ ≤ ∥F.derivative.eval a∥^2 * T^(2^(n+1)),
    from calc_eval_z'_norm hz heq h1 rfl,
  ⟨hfeq, hnle⟩⟩

set_option eqn_compiler.zeta false

-- why doesn't "noncomputable theory" stick here?
private noncomputable def newton_seq_aux : Π n : ℕ, {z : ℤ_[p] // ih n z}
| 0 := ⟨a, ih_0⟩
| (k+1) := ih_n (newton_seq_aux k).2

private def newton_seq (n : ℕ) : ℤ_[p] := (newton_seq_aux n).1

private lemma newton_seq_deriv_norm (n : ℕ) :
  ∥F.derivative.eval (newton_seq n)∥ = ∥F.derivative.eval a∥ :=
(newton_seq_aux n).2.1

private lemma newton_seq_norm_le (n : ℕ) :
  ∥F.eval (newton_seq n)∥ ≤ ∥F.derivative.eval a∥^2 * T ^ (2^n) :=
(newton_seq_aux n).2.2

private lemma newton_seq_norm_eq (n : ℕ) :
  ∥newton_seq (n+1) - newton_seq n∥ = ∥F.eval (newton_seq n)∥ / ∥F.derivative.eval (newton_seq n)∥ :=
by induction n; simp [newton_seq, newton_seq_aux, ih_n]

private lemma newton_seq_succ_dist (n : ℕ) :
  ∥newton_seq (n+1) - newton_seq n∥ ≤ ∥F.derivative.eval a∥ * T^(2^n) :=
calc ∥newton_seq (n+1) - newton_seq n∥
    = ∥F.eval (newton_seq n)∥ / ∥F.derivative.eval (newton_seq n)∥ : newton_seq_norm_eq _
... = ∥F.eval (newton_seq n)∥ / ∥F.derivative.eval a∥ : by rw newton_seq_deriv_norm
... ≤ ∥F.derivative.eval a∥^2 * T ^ (2^n) / ∥F.derivative.eval a∥ :
  (div_le_div_right deriv_norm_pos).2 (newton_seq_norm_le _)
... = ∥F.derivative.eval a∥ * T^(2^n) : div_sq_cancel (ne_of_gt deriv_norm_pos) _

include hnsol
private lemma T_pos : T > 0 :=
begin
  rw T_def,
  apply div_pos_of_pos_of_pos,
  { apply (norm_pos_iff _).2,
    apply hnsol },
  { exact deriv_sq_norm_pos hnorm }
end

private lemma newton_seq_succ_dist_weak (n : ℕ) :
  ∥newton_seq (n+2) - newton_seq (n+1)∥ < ∥F.eval a∥ / ∥F.derivative.eval a∥ :=
have 2 ≤ 2^(n+1),
  from have _, from pow_le_pow (by norm_num : 1 ≤ 2) (nat.le_add_left _ _ : 1 ≤ n + 1),
    by simpa using this,
calc ∥newton_seq (n+2) - newton_seq (n+1)∥
    ≤ ∥F.derivative.eval a∥ * T^(2^(n+1)) : newton_seq_succ_dist _
... ≤ ∥F.derivative.eval a∥ * T^2 : mul_le_mul_of_nonneg_left
                                      (pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt T_lt_one) this)
                                      (norm_nonneg _)
... < ∥F.derivative.eval a∥ * T^1 : mul_lt_mul_of_pos_left (pow_lt_pow_of_lt_one T_pos T_lt_one (by norm_num))
                                                           deriv_norm_pos
... = ∥F.eval a∥ / ∥F.derivative.eval a∥ :
  begin
    rw [T, _root_.pow_two, _root_.pow_one, norm_div, ←mul_div_assoc, padic_norm_e.mul],
    apply mul_div_mul_left',
    apply deriv_norm_ne_zero; assumption
  end

private lemma newton_seq_dist_aux (n : ℕ) :
  ∀ k : ℕ, ∥newton_seq (n + k) - newton_seq n∥ ≤ ∥F.derivative.eval a∥ * T^(2^n)
| 0 := begin simp, apply mul_nonneg, {apply norm_nonneg}, {apply T_pow_nonneg} end
| (k+1) :=
  have 2^n ≤ 2^(n+k),
    by {rw [←nat.pow_eq_pow, ←nat.pow_eq_pow], apply pow_le_pow, norm_num, apply nat.le_add_right},
  calc
  ∥newton_seq (n + (k + 1)) - newton_seq n∥
    = ∥newton_seq ((n + k) + 1) - newton_seq n∥ : by simp
... = ∥(newton_seq ((n + k) + 1) - newton_seq (n+k)) + (newton_seq (n+k) - newton_seq n)∥ : by rw ←sub_add_sub_cancel
... ≤ max (∥newton_seq ((n + k) + 1) - newton_seq (n+k)∥) (∥newton_seq (n+k) - newton_seq n∥) : padic_norm_z.nonarchimedean _ _
... ≤ max (∥F.derivative.eval a∥ * T^(2^((n + k)))) (∥F.derivative.eval a∥ * T^(2^n)) :
  max_le_max (newton_seq_succ_dist _) (newton_seq_dist_aux _)
... = ∥F.derivative.eval a∥ * T^(2^n) :
  max_eq_right $ mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt T_lt_one) this) (norm_nonneg _)

private lemma newton_seq_dist {n k : ℕ} (hnk : n ≤ k) :
  ∥newton_seq k - newton_seq n∥ ≤ ∥F.derivative.eval a∥ * T^(2^n) :=
have hex : ∃ m, k = n + m, from exists_eq_add_of_le hnk,
--  ⟨k - n, by rw [←nat.add_sub_assoc hnk, add_comm, nat.add_sub_assoc (le_refl n), nat.sub_self, nat.add_zero]⟩,
let ⟨_, hex'⟩ := hex in
by rw hex'; apply newton_seq_dist_aux; assumption

private lemma newton_seq_dist_to_a : ∀ n : ℕ, 0 < n → ∥newton_seq n - a∥ = ∥F.eval a∥ / ∥F.derivative.eval a∥
| 1 h := by simp [newton_seq, newton_seq_aux, ih_n]; apply norm_div
| (k+2) h :=
  have hlt : ∥newton_seq (k+2) - newton_seq (k+1)∥ < ∥newton_seq (k+1) - a∥,
    by rw newton_seq_dist_to_a (k+1) (succ_pos _); apply newton_seq_succ_dist_weak; assumption,
  have hne' : ∥newton_seq (k + 2) - newton_seq (k+1)∥ ≠ ∥newton_seq (k+1) - a∥, from ne_of_lt hlt,
  calc  ∥newton_seq (k + 2) - a∥
    = ∥(newton_seq (k + 2) - newton_seq (k+1)) + (newton_seq (k+1) - a)∥ : by rw ←sub_add_sub_cancel
... = max (∥newton_seq (k + 2) - newton_seq (k+1)∥) (∥newton_seq (k+1) - a∥) : padic_norm_z.add_eq_max_of_ne hne'
... = ∥newton_seq (k+1) - a∥ : max_eq_right_of_lt hlt
... = ∥polynomial.eval a F∥ / ∥polynomial.eval a (polynomial.derivative F)∥ : newton_seq_dist_to_a (k+1) (succ_pos _)

private lemma bound' : tendsto (λ n : ℕ, ∥F.derivative.eval a∥ * T^(2^n)) at_top (nhds 0) :=
begin
  rw ←mul_zero (∥F.derivative.eval a∥),
  exact tendsto_mul (tendsto_const_nhds)
                    (tendsto.comp (tendsto_pow_at_top_at_top_of_gt_1_nat (by norm_num))
                                   (tendsto_pow_at_top_nhds_0_of_lt_1 (norm_nonneg _)
                                                                      (T_lt_one hnorm)))
end

private lemma bound : ∀ {ε}, ε > 0 → ∃ N : ℕ, ∀ {n}, n ≥ N → ∥F.derivative.eval a∥ * T^(2^n) < ε :=
have mtn : ∀ n : ℕ, ∥polynomial.eval a (polynomial.derivative F)∥ * T ^ (2 ^ n) ≥ 0,
  from λ n, mul_nonneg (norm_nonneg _) (T_pow_nonneg _),
begin
  have := bound' hnorm hnsol,
  simp [tendsto, nhds] at this,
  intros ε hε,
  cases this (ball 0 ε) (mem_ball_self hε) (is_open_ball) with N hN,
  existsi N, intros n hn,
  simpa [normed_field.norm_mul, real.norm_eq_abs, abs_of_nonneg (mtn n)] using hN _ hn
end

private lemma bound'_sq : tendsto (λ n : ℕ, ∥F.derivative.eval a∥^2 * T^(2^n)) at_top (nhds 0) :=
begin
  rw [←mul_zero (∥F.derivative.eval a∥), _root_.pow_two],
  simp only [mul_assoc],
  apply tendsto_mul,
  { apply tendsto_const_nhds },
  { apply bound', assumption }
end

private theorem newton_seq_is_cauchy : is_cau_seq norm newton_seq :=
begin
  intros ε hε,
  cases bound hnorm hnsol hε with N hN,
  existsi N,
  intros j hj,
  apply lt_of_le_of_lt,
  { apply newton_seq_dist _ _ hj, assumption },
  { apply hN, apply le_refl }
end

private def newton_cau_seq : cau_seq ℤ_[p] norm := ⟨_, newton_seq_is_cauchy⟩

private def soln : ℤ_[p] := newton_cau_seq.lim

private lemma soln_spec {ε : ℝ} (hε : ε > 0) :
  ∃ (N : ℕ), ∀ {i : ℕ}, i ≥ N → ∥soln - newton_cau_seq i∥ < ε :=
setoid.symm (cau_seq.equiv_lim newton_cau_seq) _ hε

private lemma soln_deriv_norm : ∥F.derivative.eval soln∥ = ∥F.derivative.eval a∥ :=
norm_deriv_eq newton_seq_deriv_norm

private lemma newton_seq_norm_tendsto_zero : tendsto (λ i, ∥F.eval (newton_cau_seq i)∥) at_top (nhds 0) :=
squeeze_zero (λ _, norm_nonneg _) newton_seq_norm_le bound'_sq

private lemma newton_seq_dist_tendsto :
  tendsto (λ n, ∥newton_cau_seq n - a∥) at_top (nhds (∥F.eval a∥ / ∥F.derivative.eval a∥)) :=
tendsto_cong (tendsto_const_nhds) $
  suffices ∃ k, ∀ n ≥ k,  ∥F.eval a∥ / ∥F.derivative.eval a∥ = ∥newton_cau_seq n - a∥, by simpa,
  ⟨1, λ _ hx, (newton_seq_dist_to_a _ hx).symm⟩

private lemma newton_seq_dist_tendsto' :
  tendsto (λ n, ∥newton_cau_seq n - a∥) at_top (nhds ∥soln - a∥) :=
tendsto.comp (tendsto_sub (tendsto_limit _) tendsto_const_nhds)
             (continuous_iff_continuous_at.1 continuous_norm _)

private lemma soln_dist_to_a : ∥soln - a∥ = ∥F.eval a∥ / ∥F.derivative.eval a∥ :=
tendsto_nhds_unique at_top_ne_bot newton_seq_dist_tendsto' newton_seq_dist_tendsto

private lemma soln_dist_to_a_lt_deriv : ∥soln - a∥ < ∥F.derivative.eval a∥ :=
begin
  rw soln_dist_to_a,
  apply div_lt_of_mul_lt_of_pos,
  { apply deriv_norm_pos; assumption },
  { rwa _root_.pow_two at hnorm }
end

private lemma eval_soln : F.eval soln = 0 :=
limit_zero_of_norm_tendsto_zero newton_seq_norm_tendsto_zero

private lemma soln_unique (z : ℤ_[p]) (hev : F.eval z = 0) (hnlt : ∥z - a∥ < ∥F.derivative.eval a∥) :
  z = soln :=
have soln_dist : ∥z - soln∥ < ∥F.derivative.eval a∥, from calc
  ∥z - soln∥ = ∥(z - a) + (a - soln)∥ : by rw sub_add_sub_cancel
        ... ≤ max (∥z - a∥) (∥a - soln∥) : padic_norm_z.nonarchimedean _ _
        ... < ∥F.derivative.eval a∥ : max_lt hnlt (by rw norm_sub_rev; apply soln_dist_to_a_lt_deriv),
let h := z - soln,
    ⟨q, hq⟩ := F.binom_expansion soln h in
have (F.derivative.eval soln + q * h) * h = 0, from eq.symm (calc
  0 = F.eval (soln + h) : by simp [hev, h]
... = F.derivative.eval soln * h + q * h^2 : by rw [hq, eval_soln, zero_add]
... = (F.derivative.eval soln + q * h) * h : by rw [_root_.pow_two, right_distrib, mul_assoc]),
have h = 0, from by_contradiction $ λ hne,
  have F.derivative.eval soln + q * h = 0, from (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right hne,
  have F.derivative.eval soln = (-q) * h, by simpa using eq_neg_of_add_eq_zero this,
  lt_irrefl ∥F.derivative.eval soln∥ (calc
  ∥F.derivative.eval soln∥ = ∥(-q) * h∥ : by rw this
... ≤ 1 * ∥h∥ : by rw [padic_norm_z.mul]; exact mul_le_mul_of_nonneg_right (padic_norm_z.le_one _) (norm_nonneg _)
... = ∥z - soln∥ : by simp [h]
... < ∥F.derivative.eval soln∥ : by rw soln_deriv_norm; apply soln_dist),
eq_of_sub_eq_zero (by rw ←this; refl)

end hensel

variables {p : ℕ} [nat.prime p] {F : polynomial ℤ_[p]} {a : ℤ_[p]}

private lemma a_soln_is_unique (ha : F.eval a = 0) (z' : ℤ_[p]) (hz' : F.eval z' = 0)
  (hnormz' : ∥z' - a∥ < ∥F.derivative.eval a∥) : z' = a :=
let h := z' - a,
    ⟨q, hq⟩ := F.binom_expansion a h in
have (F.derivative.eval a + q * h) * h = 0, from eq.symm (calc
  0 = F.eval (a + h) : show 0 = F.eval (a + (z' - a)), by rw add_comm; simp [hz']
... = F.derivative.eval a * h + q * h^2 : by rw [hq, ha, zero_add]
... = (F.derivative.eval a + q * h) * h : by rw [_root_.pow_two, right_distrib, mul_assoc]),
have h = 0, from by_contradiction $ λ hne,
  have F.derivative.eval a + q * h = 0, from (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right hne,
  have F.derivative.eval a = (-q) * h, by simpa using eq_neg_of_add_eq_zero this,
  lt_irrefl ∥F.derivative.eval a∥ (calc
    ∥F.derivative.eval a∥ = ∥q∥*∥h∥ : by simp [this]
    ... ≤ 1*∥h∥ : mul_le_mul_of_nonneg_right (padic_norm_z.le_one _) (norm_nonneg _)
    ... < ∥F.derivative.eval a∥ : by simpa [h]),
eq_of_sub_eq_zero (by rw ←this; refl)

variable (hnorm : ∥F.eval a∥ < ∥F.derivative.eval a∥^2)
include hnorm

private lemma a_is_soln (ha : F.eval a = 0) :
  F.eval a = 0 ∧ ∥a - a∥ < ∥F.derivative.eval a∥ ∧ ∥F.derivative.eval a∥ = ∥F.derivative.eval a∥ ∧
  ∀ z', F.eval z' = 0 → ∥z' - a∥ < ∥F.derivative.eval a∥ → z' = a :=
⟨ha, by simp; apply deriv_norm_pos; apply hnorm, rfl, a_soln_is_unique ha⟩

lemma hensels_lemma : ∃ z : ℤ_[p], F.eval z = 0 ∧ ∥z - a∥ < ∥F.derivative.eval a∥ ∧
  ∥F.derivative.eval z∥ = ∥F.derivative.eval a∥ ∧
  ∀ z', F.eval z' = 0 → ∥z' - a∥ < ∥F.derivative.eval a∥ → z' = z :=
if ha : F.eval a = 0 then ⟨a, a_is_soln hnorm ha⟩ else
by refine ⟨soln _ _, eval_soln _ _, soln_dist_to_a_lt_deriv _ _, soln_deriv_norm _ _, soln_unique _ _⟩;
   assumption
