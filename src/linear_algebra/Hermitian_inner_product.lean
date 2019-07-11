/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Andreas Swerdlow
-/

import analysis.normed_space.basic linear_algebra.sesquilinear_form topology.instances.complex
import tactic.find
open complex real

lemma im_eq_zero_iff_conj_eq (x : ℂ) : x.im = 0 ↔ conj(x) = x :=
begin
  dunfold conj,
  split; intro H,
  { rw [H, neg_zero, ←H, complex.eta] },

  { rw complex.ext_iff at H,
    have : -x.im = x.im,
    { exact H.right },
    rw ←add_eq_zero_iff_neg_eq at this,
    exact add_self_eq_zero.mp this}
end

lemma ne_zero_im_zero_imp_re_ne_zero {x : ℂ} : x ≠ 0 → x.im = 0 → x.re ≠ 0 :=
begin
  intros H1 H2,
  have Hx : x = ↑x.re,
  { rw [←re_add_im x, H2, of_real_zero, 
        zero_mul, field.add_zero, of_real_re] },
  rw Hx at H1,
  exact of_real_ne_zero.mp H1,
end

lemma re_of_real {x : ℂ} : x.im = 0 → ↑(x.re) = x :=
begin
  intros H,
  rw [←re_add_im x, H, of_real_zero, zero_mul, field.add_zero, of_real_inj, of_real_re],
end

lemma of_real_pow (x : ℝ) (a : ℕ) : (↑(x^a) : ℂ) = (↑x)^a :=
begin
  induction a with d Hd,
  { simp },
  { rw [pow_succ, pow_succ],
    rw of_real_mul,
    rw Hd },
end

def conj.equiv : equiv ℂ ℂ := 
⟨conj, conj, begin dunfold function.left_inverse, intros, simp, end, begin dunfold function.right_inverse, dunfold function.left_inverse, intros, simp, end⟩

noncomputable def conj.ring_equiv : ℂ ≃r ℂ := 
⟨conj.equiv, conj_one, conj_mul, conj_add⟩ 

noncomputable def conj.ring_invo : ring_invo ℂ :=
⟨comm_ring.isom_to_anti_isom conj.ring_equiv, begin apply conj_conj end⟩

class herm_inner_product_space (α : Type*) [add_comm_group α] [vector_space ℂ α] extends sesq_form ℂ α conj.ring_invo :=
(to_sym_sesq_form : sym_sesq_form.is_sym to_sesq_form)
(sesq_self_re_nonneg : ∀ (x : α), 0 ≤ (sesq x x).re)
(sesq_self_eq_zero_iff : ∀ (x : α), sesq x x = 0 ↔ x = 0)

namespace herm_inner_product_space

open ring_invo

variables {α : Type*} [add_comm_group α] [vector_space ℂ α] [herm_inner_product_space α]

noncomputable def inner_product : α → α → ℂ := (herm_inner_product_space.to_sesq_form α).sesq

local notation `ₕ⟨` : 1 x `|` : 1 y `⟩` : 1 := inner_product x y

namespace inner_product

lemma conj_sym (x y : α) : conj (ₕ⟨x|y⟩) = ₕ⟨y|x⟩ := to_sym_sesq_form α x y   

lemma self_re_nonneg (x : α) : 0 ≤ (ₕ⟨x|x⟩).re := sesq_self_re_nonneg x   

lemma self_eq_zero_iff {x : α} : (inner_product x x) = 0 ↔ x = (0 : α) := sesq_self_eq_zero_iff x

@[simp] lemma add_left (x y z : α) : 
ₕ⟨(x + y)|z⟩ = ₕ⟨x|z⟩ + ₕ⟨y|z⟩ := sesq_form.sesq_add_left _ _ _ _
 
@[simp] lemma add_right (x y z : α) : 
ₕ⟨x|(y + z)⟩ = ₕ⟨x|y⟩ + ₕ⟨x|z⟩ := sesq_form.sesq_add_right _ _ _ _

@[simp] lemma smul_left (a : ℂ) (x y : α) :
ₕ⟨(a • x)|y⟩ = a * (ₕ⟨x|y⟩) := sesq_form.sesq_smul_left _ _ _ _

@[simp] lemma smul_right (a : ℂ) (x y : α) :
ₕ⟨x|(a • y)⟩ = conj(a) * (ₕ⟨x|y⟩) := sesq_form.sesq_smul_right _ _ _ _

open sym_sesq_form sesq_form

@[simp] lemma zero_left (x : α) :
ₕ⟨0|x⟩ = 0 := zero_left x  

@[simp] lemma zero_right (x : α) :
ₕ⟨x|0⟩ = 0 := zero_right x 

@[simp] lemma neg_left (x y : α) : 
ₕ⟨-x|y⟩ = -(ₕ⟨x|y⟩) := neg_left x y 

@[simp] lemma neg_right (x y : α) : 
ₕ⟨x| -y⟩ = -(ₕ⟨x|y⟩) := neg_right x y   

@[simp] lemma sub_left (x y z : α) : 
ₕ⟨(x - y)|z⟩ = (ₕ⟨x|z⟩) - (ₕ⟨y|z⟩) := sub_left x y z

@[simp] lemma sub_right (x y z : α) : 
ₕ⟨x|(y - z)⟩ = (ₕ⟨x|y⟩) - (ₕ⟨x|z⟩) := sub_right x y z

lemma self_add (x y : α) :
ₕ⟨x + y|x + y⟩ = (ₕ⟨x|x⟩) + (ₕ⟨y|y⟩) + (ₕ⟨x|y⟩) + (ₕ⟨y|x⟩) :=
begin
  rw [inner_product.add_left, inner_product.add_right, inner_product.add_right],
  simpa [field.add_assoc, field.add_comm],
end

theorem self_im (x : α) :
(ₕ⟨x|x⟩).im = 0 :=
(im_eq_zero_iff_conj_eq (ₕ⟨x|x⟩)).mpr (inner_product.conj_sym x x)

lemma self_re_eq_zero_iff {x : α} : 
(ₕ⟨x|x⟩).re = 0 ↔ x = 0 := 
begin
  split; intros H,
  { suffices : ₕ⟨x|x⟩ = 0,
    { exact inner_product.self_eq_zero_iff.mp this },
    { apply complex.ext,
      { simpa },

      { rw [self_im, zero_im] }}},

  { rw H,
    simp }
end

lemma self_ne_zero_iff {x : α} : 
ₕ⟨x|x⟩ ≠ 0 ↔ x ≠ 0 := 
⟨ λ H, (iff_false_left H).mp inner_product.self_eq_zero_iff, 
  λ H, (iff_false_right H).mp inner_product.self_eq_zero_iff⟩ 

lemma self_re_ne_zero_iff {x : α} : 
(ₕ⟨x|x⟩).re ≠ 0 ↔ x ≠ 0 :=
begin
  split; intros H,
  { have Ho : (ₕ⟨x|x⟩) ≠ 0,
    { intros Hx,
      rw [Hx, zero_re] at H,
      trivial },
    exact self_ne_zero_iff.mp Ho },

  { have Ho : (ₕ⟨x|x⟩) ≠ 0,
    { exact self_ne_zero_iff.mpr H },
    exact ne_zero_im_zero_imp_re_ne_zero Ho (self_im x) } 
end

lemma re (x y : α) : (ₕ⟨x|y⟩).re = (ₕ⟨y|x⟩).re := 
by rw [←inner_product.conj_sym, conj_re]

lemma im (x y : α) : (ₕ⟨x|y⟩).im = -(ₕ⟨y|x⟩).im :=
by rw [←inner_product.conj_sym, conj_im]

lemma abs_self (x : α) : abs ₕ⟨x|x⟩ = ₕ⟨x|x⟩.re := 
by {rw [complex.abs, norm_sq, self_im, mul_zero,
      add_zero, sqrt_mul_self (self_re_nonneg x)]}

lemma re_le_abs (x y : α) :  ₕ⟨x|y⟩.re ≤ abs (ₕ⟨x|y⟩) :=
begin 
cases le_or_lt 0 (ₕ⟨x|y⟩.re),
  { rw [complex.abs, norm_sq, ←pow_two], 
  rw le_sqrt h (add_nonneg (pow_two_nonneg ((ₕ⟨x|y⟩.re))) (mul_self_nonneg ((ₕ⟨x|y⟩.im)))),
  exact le_add_of_nonneg_right (mul_self_nonneg (ₕ⟨x|y⟩.im)) },

  { exact le_of_lt (lt_of_lt_of_le h (abs_nonneg ₕ⟨x|y⟩))},
end

lemma self_eq_of_real_re (x : α) : ₕ⟨x|x⟩ = ↑ₕ⟨x|x⟩.re :=
ext (of_real_re _) (by rw [of_real_im, self_im])

end inner_product

def orthogonal (x y : α) : Prop := ₕ⟨x|y⟩ = 0 

local notation a ⊥ b := orthogonal a b 

lemma orthogonal_sym (x y : α) :
(x ⊥ y) ↔ (y ⊥ x) := sym_sesq_form.ortho_sym (to_sym_sesq_form α)
 
lemma orthogonal_refl_iff_zero (x : α) : 
(x ⊥ x) ↔ x = 0 := inner_product.self_eq_zero_iff  

def orthogonal_smul_left (x y : α) (a : ℂ) (ha : a ≠ 0) : 
(x ⊥ y) ↔ ((a • x) ⊥ y) := sesq_form.ortho_smul_left ha

def orthogonal_smul_right (x y : α) (a : ℂ) (ha : a ≠ 0) : 
(x ⊥ y) ↔ (x ⊥ (a • y)) := sesq_form.ortho_smul_right ha

theorem orthogonal_imp_not_lindep (x y : α) (hx : x ≠ 0) (hy : y ≠ 0) : 
(x ⊥ y) → ¬∃ (a : ℂ), (a ≠ 0) ∧ (x = a • y ∨ a • x = y) :=
begin
  intros H1,
  apply not_exists.mpr,
  intros a,
  intros H2,
  unfold orthogonal at H1,
  cases H2 with ha H2,
  cases H2,  
  { rw H2 at H1,
    rw [inner_product.smul_left, mul_eq_zero] at H1,
    cases H1,
    { trivial }, 

    { exact hy ((inner_product.self_eq_zero_iff).mp H1) }},
    
  { rw ←H2 at H1,
    rw [inner_product.smul_right, mul_eq_zero] at H1,
    cases H1,
    { exact ha ((conj_eq_zero).mp H1) },

    { exact hx ((inner_product.self_eq_zero_iff).mp H1) }}
end 

noncomputable def herm_norm (x : α) := sqrt((ₕ⟨x|x⟩).re)

lemma herm_norm_zero : herm_norm (0 : α) = 0 := 
by {dunfold herm_norm, rw [inner_product.zero_left, zero_re, sqrt_zero]}

lemma herm_norm_sqr (x : α) : (herm_norm x)^2 = (ₕ⟨x|x⟩).re := 
sqr_sqrt (inner_product.self_re_nonneg x)

lemma sq_herm_norm_add {x y : α} (H : x ⊥ y) :
herm_norm (x + y) ^2 = herm_norm(x)^2 + herm_norm(y)^2 :=
begin
  dunfold herm_norm,
  rw [sqr_sqrt (inner_product.self_re_nonneg (x + y)), sqr_sqrt (inner_product.self_re_nonneg x),
    sqr_sqrt (inner_product.self_re_nonneg y), inner_product.self_add],
  unfold orthogonal at H,
  rw [←inner_product.conj_sym x y, H, conj_zero,
    field.add_zero, field.add_zero, add_re],
end

lemma herm_norm_smul (a : ℂ) (x : α) : 
herm_norm (a • x) = abs(a)* herm_norm x := 
begin 
  intros, 
  dunfold herm_norm,
  rw [inner_product.smul_left, inner_product.smul_right, ←field.mul_assoc,
    mul_conj, mul_re, of_real_im, zero_mul,
    sub_zero, of_real_re, sqrt_mul (norm_sq_nonneg a)],
  refl,
end

lemma herm_norm_nonneg (x : α) : 0 ≤ herm_norm x := sqrt_nonneg ₕ⟨x|x⟩.re

lemma abs_herm_norm_sq (x : α) : complex.abs (↑(herm_norm x)^2 ) = herm_norm x ^2 := 
by {rw ←complex.of_real_pow,  exact complex.abs_of_nonneg (pow_two_nonneg (herm_norm x))}

theorem abs_inner_product_le_mul_herm_norm (x y : α) : 
abs((ₕ⟨x|y⟩)) ≤ herm_norm x * herm_norm y := 
begin
  classical, by_cases hy : y = 0,
  { rw [hy, herm_norm_zero],
    simp },
    
  { have H1 : ((↑(herm_norm y) : ℂ)^2 • x - ₕ⟨x|y⟩ • y) ⊥ (ₕ⟨x|y⟩ • y),
    { dunfold orthogonal,
      rw [←complex.of_real_pow, herm_norm_sqr, re_of_real (inner_product.self_im y),
        inner_product.sub_left, inner_product.smul_left, inner_product.smul_left,
        inner_product.smul_right, inner_product.smul_right, mul_comm, ←mul_assoc,
        mul_comm (ₕ⟨x|y⟩), sub_self]}, 
    have H2 : ((↑(herm_norm y) : ℂ)^2 • x - ₕ⟨x|y⟩ • y) + (ₕ⟨x|y⟩ • y) = (↑(herm_norm y)^2 : ℂ) • x,
      simp,
    have H3 : herm_norm(((↑(herm_norm y) : ℂ)^2 • x - ₕ⟨x|y⟩ • y) + (ₕ⟨x|y⟩ • y))^2 = herm_norm(((↑(herm_norm y) : ℂ)^2 • x - ₕ⟨x|y⟩ • y))^2 + herm_norm((ₕ⟨x|y⟩ • y))^2,
      exact sq_herm_norm_add H1,
    rw H2 at H3,
    repeat {rw herm_norm_smul at H3},
    suffices : (abs ₕ⟨x|y⟩ * herm_norm y ) ^ 2 ≤ (complex.abs (↑(herm_norm y) ^ 2) * herm_norm x ) ^ 2,
    { rw [abs_herm_norm_sq, mul_pow, mul_pow,
        pow_two ((herm_norm y)^2), mul_comm, mul_assoc] at this,
      have H4 : 0 < herm_norm y^2,
      { exact lt_of_le_of_ne 
                (pow_two_nonneg (herm_norm y)) 
                (by {apply ne.symm, rw [herm_norm_sqr, inner_product.self_re_ne_zero_iff], exact hy}) },
      rw mul_le_mul_left H4 at this,
      rw ←sqrt_le (pow_two_nonneg (abs ₕ⟨x|y⟩)) (mul_nonneg (pow_two_nonneg (herm_norm y)) (pow_two_nonneg (herm_norm x))) at this,
      rw ←mul_pow at this,
      rw sqrt_sqr (abs_nonneg ₕ⟨x|y⟩) at this,
      rw sqrt_sqr (mul_nonneg (herm_norm_nonneg y) (herm_norm_nonneg x)) at this,
      rw mul_comm at this, 
      exact this },
    { rw H3, 
      exact le_add_of_nonneg_left (pow_two_nonneg (herm_norm (↑(herm_norm y) ^ 2 • x - ₕ⟨x|y⟩ • y))) }}
end

noncomputable instance : metric_space α := 
{ dist := λ x y, herm_norm (x - y), 
  dist_self := 
    begin
      intros,
      unfold dist, 
      rw [sub_self, herm_norm_zero],
    end,
  eq_of_dist_eq_zero :=
    begin
    unfold dist herm_norm,
    intros x y H,
    rw [sqrt_eq_zero (inner_product.self_re_nonneg (x - y))] at H,
    exact sub_eq_zero.1 ((inner_product.self_re_eq_zero_iff).1 H),
    end,
  dist_comm := 
    begin
      intros,
      unfold dist herm_norm,
      rw [sqrt_inj (inner_product.self_re_nonneg (x - y)) (inner_product.self_re_nonneg (y - x)),
        ←neg_sub, inner_product.neg_left, inner_product.neg_right, neg_neg],
    end,
  dist_triangle := 
    begin
      intros x y z,
      unfold dist, 
      suffices : ∀ (a b : α), herm_norm (a + b) ≤ herm_norm a + herm_norm b,
      { rw [sub_eq_sub_add_sub x z y, add_comm],
        exact this (x - y) (y - z) },  
      { intros a b,
        suffices : herm_norm (a + b)^2 ≤ (herm_norm a + herm_norm b)^2,
        { rw ←sqrt_le (pow_two_nonneg (herm_norm (a + b))) (pow_two_nonneg (herm_norm a + herm_norm b)) at this,
          rw sqrt_sqr (herm_norm_nonneg (a + b)) at this,
          rw sqrt_sqr (add_nonneg (herm_norm_nonneg a) (herm_norm_nonneg b)) at this,
          exact this},
        { rw [pow_two (herm_norm a + herm_norm b), mul_add,
            add_mul, add_mul, ←pow_two, ←pow_two],
          repeat {rw herm_norm_sqr},
          rw inner_product.self_add,
          repeat {rw add_re},
          repeat {rw add_assoc},
          rw [add_le_add_iff_left, add_comm, ←add_assoc,
            add_le_add_iff_right, inner_product.re b a, mul_comm],
          exact add_le_add
            (le_trans (inner_product.re_le_abs a b) (abs_inner_product_le_mul_herm_norm a b))
            (le_trans (inner_product.re_le_abs a b) (abs_inner_product_le_mul_herm_norm a b)) }}
    end}

noncomputable instance : normed_group α := 
{ norm := herm_norm,
  dist_eq := by {intros, refl}}

noncomputable instance : normed_space ℂ α :=  
{ norm_smul := 
    begin 
      intros, 
      unfold norm,
      dunfold herm_norm, 
      rw [inner_product.smul_left, inner_product.smul_right, ←field.mul_assoc,
        mul_conj, mul_re, of_real_im, zero_mul,
        sub_zero, of_real_re, sqrt_mul (norm_sq_nonneg a)],
        refl,
    end}

lemma norm_sqr (x : α) : ∥x∥^2 = (ₕ⟨x|x⟩).re := 
herm_norm_sqr x

lemma mul_self_norm (x : α) : ∥x∥ * ∥x∥ = (ₕ⟨x|x⟩).re :=
by {rw ←pow_two, exact norm_sqr x}

@[simp] lemma of_real_norm_sqr (x : α) : 
↑( ∥x∥^2 ) = ₕ⟨x|x⟩ := by rw [norm_sqr, re_of_real (inner_product.self_im x)]

@[simp] lemma of_real_norm_sqr' (x : α) : 
↑ ∥x∥^2  = ₕ⟨x|x⟩ := by rw [←complex.of_real_pow, of_real_norm_sqr]

@[simp] lemma of_real_norm_mul_self (x : α) : 
↑( ∥x∥*∥x∥ ) = ₕ⟨x|x⟩ := by rw [mul_self_norm, re_of_real (inner_product.self_im x)]

/-- Pythagorean Theorem -/
lemma sq_norm_add {x y : α} (H : x ⊥ y) :
∥x + y∥^2 = ∥x∥^2 + ∥y∥^2 := sq_herm_norm_add H 

lemma abs_of_real_norm (x : α) : complex.abs (↑∥x∥) = ∥x∥ := 
complex.abs_of_nonneg (norm_nonneg x)

lemma abs_of_real_norm_sq (x : α) : complex.abs (↑∥x∥^2 ) = ∥x∥^2 := 
abs_herm_norm_sq x

/-- Cauchy-Schwarz Inequality -/
theorem abs_inner_product_le_mul_norm (x y : α) : 
abs ₕ⟨x|y⟩  ≤ ∥x∥ * ∥y∥ := abs_inner_product_le_mul_herm_norm x y

lemma norm_add (x y : α) :
∥x + y∥^2 = ∥x∥^2 + ₕ⟨x|y⟩.re + ₕ⟨y|x⟩.re + ∥y∥^2 :=
begin
  unfold norm,
  repeat {rw herm_norm_sqr},
  rw inner_product.add_left,
  repeat {rw inner_product.add_right},
  repeat {rw add_re},
  simp,
end

lemma norm_sub (x y : α) :
∥x - y∥^2 = ∥x∥^2 - ₕ⟨x|y⟩.re - ₕ⟨y|x⟩.re + ∥y∥^2 :=
begin
  unfold norm,
  repeat {rw herm_norm_sqr},
  rw inner_product.sub_left,
  repeat {rw inner_product.sub_right},
  repeat {rw sub_re},
  simp,
end

theorem parallelogram_law (x y : α) :
∥x + y∥^2 + ∥x - y∥^2 = 2*∥x∥^2 + 2*∥y∥^2 :=
begin
  rw norm_add,
  rw norm_sub,
  simp [two_mul],
end

def is_normalized (x : α) := ∥x∥ = 1

noncomputable def normalize (x : α) := (↑∥x∥⁻¹ : ℂ) • x 

lemma norm_normalize {x : α} (ho : x ≠ 0) : 
∥normalize x∥ = 1 := 
begin 
  rw [normalize, norm_smul, of_real_inv, norm_inv],
  unfold norm,
  rw [complex.abs_of_nonneg (herm_norm_nonneg x), inv_mul_cancel],
  have H : herm_norm x = ∥x∥,
    refl,
  rw [H, ne, norm_eq_zero],
  exact ho,
end

lemma normalize.is_normalized {x : α} (ho : x ≠ 0) : 
is_normalized (normalize x) := norm_normalize ho

noncomputable def proj (x y : α) :=
((ₕ⟨y|x⟩)/(ₕ⟨x|x⟩)) • x

lemma proj_eq_smul_normalize (x y : α) : proj x y  = ((ₕ⟨y|x⟩)/(∥x∥)) • (normalize x) :=
begin
  rw [proj, normalize, smul_smul, of_real_inv,
    ←div_eq_mul_inv, div_div_eq_div_mul,
    ←of_real_mul, of_real_norm_mul_self],
end

lemma zero_proj (x : α) :
proj 0 x = 0 := by {dunfold proj, simp}

lemma proj_zero (x : α) :
proj x 0 = 0 := by {dunfold proj, simp}

lemma proj_self_eq_self (x : α) :
proj x x = x :=
begin
  dunfold proj,
  classical, by_cases ho : x = 0, 
  { rw ho,
    simp },

  { rw [div_self (inner_product.self_ne_zero_iff.mpr ho), one_smul] }
end

lemma smul_proj (x y : α) {a : ℂ} : 
proj x (a • y) = a • (proj x y) :=
begin
  dunfold proj,
  rw [inner_product.smul_left, smul_smul, mul_div_assoc],
end

lemma proj_smul (x y : α) {a : ℂ} (ha : a ≠ 0) :
proj (a • x) y = proj x y := 
begin
  classical, by_cases Hx : x = 0,
  { rw [Hx, smul_zero] },

  { delta proj,
    rw [inner_product.smul_right, inner_product.smul_right,
      inner_product.smul_left],
    rw mul_div_mul_left _ 
      (mul_ne_zero ha (inner_product.self_ne_zero_iff.2 Hx))
      (by {dunfold ne, rw conj_eq_zero, exact ha}),
    rw [smul_smul, div_mul_eq_mul_div_comm, 
      div_mul_right (ₕ⟨x|x⟩) ha, ←div_eq_mul_one_div] }
end

noncomputable instance complex.normed_group : normed_group ℂ := normed_ring.to_normed_group 

lemma norm_proj_le (x y : α) : 
∥proj x y∥ ≤ ∥y∥ :=
begin
  classical, by_cases Hx : x = 0,
  { rw [Hx, zero_proj, norm_zero],
    exact norm_nonneg y },

  { rw proj_eq_smul_normalize,
    rw norm_smul,
    rw norm_normalize Hx,
    rw mul_one,
    rw norm_div,
    rw div_le_iff (lt_of_le_of_ne 
                      (norm_nonneg (↑∥x∥)) 
                      (by { rw [ne, eq_comm, norm_eq_zero, 
                              of_real_eq_zero, norm_eq_zero], 
                            exact Hx})),
    unfold norm,
    rw complex.abs_of_nonneg (herm_norm_nonneg x),
    exact abs_inner_product_le_mul_herm_norm y x}
end

lemma proj_eq_zero_of_orthogonal {x y : α} (H : x ⊥ y) :
proj y x = 0 := 
begin
  delta orthogonal at H,
  delta proj,
  simp [H]
end

lemma proj_eq_self_iff_lindep {x y : α} :
proj x y = y ↔ ∃ (a : ℂ), y = a • x :=
begin
  split,
  { dunfold proj, 
    intros H,
    exact exists.intro (ₕ⟨y|x⟩ / ₕ⟨x|x⟩) (eq_comm.mp H) },

  { intros H,
    cases H with a Ha,
    rw [Ha, smul_proj, proj_self_eq_self] }
end

end herm_inner_product_space

class Hilbert_space (α : Type*) [add_comm_group α] [vector_space ℂ α] extends herm_inner_product_space α :=
(complete : ∀{f : filter α}, cauchy f → ∃x, f ≤ nhds x) 

instance Hilbert_space.to_complete_space (α : Type*) [add_comm_group α] [vector_space ℂ α] [Hilbert_space α] : complete_space α :=
{complete := @Hilbert_space.complete _ _ _ _}   
