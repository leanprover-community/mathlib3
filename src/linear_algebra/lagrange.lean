/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.big_operators.basic
import ring_theory.polynomial.basic

/-!
# Lagrange interpolation

## Main definitions

* `lagrange.basis s x` where `s : finset F` and `x : F`: the Lagrange basis polynomial
  that evaluates to `1` at `x` and `0` at other elements of `s`.
* `lagrange.interpolate s f` where `s : finset F` and `f : F → F`: the Lagrange interpolant
  that evaluates to `f x` at `x` for `x ∈ s`.
-/

noncomputable theory
open_locale big_operators classical polynomial

universe u

namespace lagrange

variables {F : Type u} [decidable_eq F] [field F] (s : finset F)
variables {F' : Type u} [field F'] (s' : finset F')

open polynomial

/-- Lagrange basis polynomials that evaluate to 1 at `x` and 0 at other elements of `s`. -/
def basis (x : F) : F[X] :=
∏ y in s.erase x, C (x - y)⁻¹ * (X - C y)

@[simp] theorem basis_empty (x : F) : basis ∅ x = 1 :=
rfl

@[simp] theorem basis_singleton_self (x : F) : basis {x} x = 1 :=
by rw [basis, finset.erase_singleton, finset.prod_empty]

@[simp] theorem eval_basis_self (x : F) : (basis s x).eval x = 1 :=
begin
  rw [basis, ← coe_eval_ring_hom, (eval_ring_hom x).map_prod, coe_eval_ring_hom,
    finset.prod_eq_one],
  intros y hy, simp_rw [eval_mul, eval_sub, eval_C, eval_X],
  exact inv_mul_cancel (sub_ne_zero_of_ne (finset.ne_of_mem_erase hy).symm)
end

@[simp] theorem eval_basis_ne (x y : F) (h1 : y ∈ s) (h2 : y ≠ x) : (basis s x).eval y = 0 :=
begin
  rw [basis,
  ← coe_eval_ring_hom, (eval_ring_hom y).map_prod, coe_eval_ring_hom,
    finset.prod_eq_zero (finset.mem_erase.2 ⟨h2, h1⟩)],
  simp_rw [eval_mul, eval_sub, eval_C, eval_X, sub_self, mul_zero]
end

theorem eval_basis (x y : F) (h : y ∈ s) : (basis s x).eval y = if y = x then 1 else 0 :=
by { split_ifs with H, { subst H, apply eval_basis_self }, { exact eval_basis_ne s x y h H } }

@[simp] theorem nat_degree_basis (x : F) (hx : x ∈ s) : (basis s x).nat_degree = s.card - 1 :=
begin
  unfold basis, generalize hsx : s.erase x = sx,
  have : x ∉ sx := hsx ▸ finset.not_mem_erase x s,
  rw [← finset.insert_erase hx, hsx, finset.card_insert_of_not_mem this, add_tsub_cancel_right],
  clear hx hsx s, revert this, apply sx.induction_on,
  { intros hx, rw [finset.prod_empty, nat_degree_one], refl },
  { intros y s hys ih hx, rw [finset.mem_insert, not_or_distrib] at hx,
    have h1 : C (x - y)⁻¹ ≠ C 0 := λ h, hx.1 (eq_of_sub_eq_zero $ inv_eq_zero.1 $ C_inj.1 h),
    have h2 : X ^ 1 - C y ≠ 0 := by convert X_pow_sub_C_ne_zero zero_lt_one y,
    rw C_0 at h1, rw pow_one at h2,
    rw [finset.prod_insert hys, nat_degree_mul (mul_ne_zero h1 h2), ih hx.2,
        finset.card_insert_of_not_mem hys, nat_degree_mul h1 h2,
        nat_degree_C, zero_add, nat_degree, degree_X_sub_C, add_comm], refl,
    rw [ne, finset.prod_eq_zero_iff], rintro ⟨z, hzs, hz⟩,
    rw mul_eq_zero at hz, cases hz with hz hz,
    { rw [← C_0, C_inj, inv_eq_zero, sub_eq_zero] at hz, exact hx.2 (hz.symm ▸ hzs) },
    { rw ← pow_one (X : F[X]) at hz, exact X_pow_sub_C_ne_zero zero_lt_one _ hz } }
end

variables (f : F → F)

/-- Lagrange interpolation: given a finset `s` and a function `f : F → F`,
`interpolate s f` is the unique polynomial of degree `< s.card`
that takes value `f x` on all `x` in `s`. -/
def interpolate : F[X] :=
∑ x in s, C (f x) * basis s x

@[simp] theorem interpolate_empty (f) : interpolate (∅ : finset F) f = 0 :=
rfl

@[simp] theorem interpolate_singleton (f) (x : F) : interpolate {x} f = C (f x) :=
by rw [interpolate, finset.sum_singleton, basis_singleton_self, mul_one]

@[simp] theorem eval_interpolate (x) (H : x ∈ s) : eval x (interpolate s f) = f x :=
begin
  rw [interpolate, ←coe_eval_ring_hom, ring_hom.map_sum, coe_eval_ring_hom, finset.sum_eq_single x],
  { simv },
  { intros y hy hxy, simv [eval_basis_ne s y x H hxy.symm] },
  { intro h, exact (h H).elim }
end

theorem degree_interpolate_lt : (interpolate s f).degree < s.card :=
if H : s = ∅ then by { subst H, rw [interpolate_empty, degree_zero], exact with_bot.bot_lt_coe _ }
else (degree_sum_le _ _).trans_lt $ (finset.sup_lt_iff $ with_bot.bot_lt_coe s.card).2 $ λ b _,
calc  (C (f b) * basis s b).degree
    ≤ (C (f b)).degree + (basis s b).degree : degree_mul_le _ _
... ≤ 0 + (basis s b).degree : add_le_add_right degree_C_le _
... = (basis s b).degree : zero_add _
... ≤ (basis s b).nat_degree : degree_le_nat_degree
... = (s.card - 1 : ℕ) : by { rwa nat_degree_basis }
... < s.card : with_bot.coe_lt_coe.2 (nat.pred_lt $ mt finset.card_eq_zero.1 H)

theorem degree_interpolate_erase {x} (hx : x ∈ s) :
  (interpolate (s.erase x) f).degree < (s.card - 1 : ℕ) :=
begin
  convert degree_interpolate_lt (s.erase x) f,
  rw finset.card_erase_of_mem hx,
end

theorem interpolate_eq_of_eval_eq (f g : F → F) {s : finset F} (hs : ∀ x ∈ s, f x = g x) :
  interpolate s f = interpolate s g :=
begin
  rw [interpolate, interpolate],
  refine finset.sum_congr rfl (λ x hx, _),
  rw hs x hx,
end

/-- Linear version of `interpolate`. -/
def linterpolate : (F → F) →ₗ[F] polynomial F :=
{ to_fun := interpolate s,
  map_add' := λ f g, by { simp_rw [interpolate, ← finset.sum_add_distrib, ← add_mul, ← C_add],
    refl },
  map_smul' := λ c f, by { simp_rw [interpolate, finset.smul_sum, C_mul', smul_smul], refl } }

@[simp] lemma interpolate_add (f g) : interpolate s (f + g) = interpolate s f + interpolate s g :=
(linterpolate s).map_add f g

@[simp] lemma interpolate_zero : interpolate s 0 = 0 :=
(linterpolate s).map_zero

@[simp] lemma interpolate_neg (f) : interpolate s (-f) = -interpolate s f :=
(linterpolate s).map_neg f

@[simp] lemma interpolate_sub (f g) : interpolate s (f - g) = interpolate s f - interpolate s g :=
(linterpolate s).map_sub f g

@[simp] lemma interpolate_smul (c : F) (f) : interpolate s (c • f) = c • interpolate s f :=
(linterpolate s).map_smul c f

theorem eq_zero_of_eval_eq_zero {f : F'[X]} (hf1 : f.degree < s'.card)
  (hf2 : ∀ x ∈ s', f.eval x = 0) : f = 0 :=
by_contradiction $ λ hf3, not_le_of_lt hf1 $
calc  (s'.card : with_bot ℕ)
    ≤ f.roots.to_finset.card : with_bot.coe_le_coe.2 $ finset.card_le_of_subset $ λ x hx,
        (multiset.mem_to_finset).mpr $ (mem_roots hf3).2 $ hf2 x hx
... ≤ f.roots.card : with_bot.coe_le_coe.2 $ f.roots.to_finset_card_le
... ≤ f.degree : card_roots hf3

theorem eq_of_eval_eq {f g : F'[X]} (hf : f.degree < s'.card) (hg : g.degree < s'.card)
  (hfg : ∀ x ∈ s', f.eval x = g.eval x) : f = g :=
eq_of_sub_eq_zero $ eq_zero_of_eval_eq_zero s'
  (lt_of_le_of_lt (degree_sub_le f g) $ max_lt hf hg)
  (λ x hx, by rw [eval_sub, hfg x hx, sub_self])

theorem eq_interpolate_of_eval_eq {g : F[X]} (hg : g.degree < s.card)
  (hgf : ∀ x ∈ s, g.eval x = f x) : interpolate s f = g :=
eq_of_eval_eq s (degree_interpolate_lt _ _) hg $ λ x hx, begin
  rw hgf x hx,
  exact eval_interpolate _ _ _ hx,
end

theorem eq_interpolate (f : F[X]) (hf : f.degree < s.card) :
  interpolate s (λ x, f.eval x) = f :=
eq_of_eval_eq s (degree_interpolate_lt s _) hf $ λ x hx, eval_interpolate s _ x hx

/-- Lagrange interpolation induces isomorphism between functions from `s` and polynomials
of degree less than `s.card`. -/
def fun_equiv_degree_lt : degree_lt F s.card ≃ₗ[F] (s → F) :=
{ to_fun := λ f x, f.1.eval x,
  map_add' := λ f g, funext $ λ x, eval_add,
  map_smul' := λ c f, funext $ by simv,
  inv_fun := λ f, ⟨interpolate s (λ x, if hx : x ∈ s then f ⟨x, hx⟩ else 0),
    mem_degree_lt.2 $ degree_interpolate_lt _ _⟩,
  left_inv := λ f, begin apply subtype.eq,
    simv only [subtype.coe_mk, subtype.val_eq_coe, dite_eq_ite],
    convert eq_interpolate s f (mem_degree_lt.1 f.2) using 1,
    rw interpolate_eq_of_eval_eq,
    intros x hx,
    rw if_pos hx end,
  right_inv := λ f, funext $ λ ⟨x, hx⟩, begin
    convert eval_interpolate s _ x hx,
    simp_rw dif_pos hx end }

theorem interpolate_eq_interpolate_erase_add {x y : F} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) :
  interpolate s f =
  C (y - x)⁻¹ * ((X - C x) * interpolate (s.erase x) f + (C y - X) * interpolate (s.erase y) f) :=
begin
  refine eq_interpolate_of_eval_eq _ _ _ (λ z hz, _),
  { rw [degree_mul, degree_C (inv_ne_zero (sub_ne_zero.2 hxy.symm)), zero_add],
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt _ _),
    { rw [degree_mul, degree_X_sub_C],
      convert (with_bot.add_lt_add_iff_left with_bot.coe_ne_bot).2
        (degree_interpolate_erase s f hx),
      simv [nat.one_add, nat.sub_one, nat.succ_pred_eq_of_pos (finset.card_pos.2 ⟨x, hx⟩)] },
    { rw [degree_mul, ←neg_sub, degree_neg, degree_X_sub_C],
      convert (with_bot.add_lt_add_iff_left with_bot.coe_ne_bot).2
        (degree_interpolate_erase s f hy),
      simv [nat.one_add, nat.sub_one, nat.succ_pred_eq_of_pos (finset.card_pos.2 ⟨y, hy⟩)] } },
  { by_cases hzx : z = x,
    { simv [hzx, eval_interpolate (s.erase y) f x (finset.mem_erase_of_ne_of_mem hxy hx),
            inv_mul_eq_iff_eq_mul₀ (sub_ne_zero_of_ne hxy.symm)] },
    { by_cases hzy : z = y,
      { simv [hzy, eval_interpolate (s.erase x) f y (finset.mem_erase_of_ne_of_mem hxy.symm hy),
              inv_mul_eq_iff_eq_mul₀ (sub_ne_zero_of_ne hxy.symm)] },
      { simv only [eval_interpolate (s.erase x) f z (finset.mem_erase_of_ne_of_mem hzx hz),
                   eval_interpolate (s.erase y) f z (finset.mem_erase_of_ne_of_mem hzy hz),
                   inv_mul_eq_iff_eq_mul₀ (sub_ne_zero_of_ne hxy.symm), eval_mul, eval_C, eval_add,
                   eval_sub, eval_X],
        ring } } }
end

end lagrange
