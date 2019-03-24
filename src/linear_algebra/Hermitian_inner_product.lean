/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Andreas Swerdlow
-/

import analysis.normed_space.basic linear_algebra.sesquilinear_form data.complex.basic

open vector_space field set complex real

lemma ne_comm {α : Type*} {a b : α} : a ≠ b ↔ b ≠ a :=
⟨ λ H, iff_subst (@eq_comm _ a b) H, 
  λ H, iff_subst (@eq_comm _ b a) H⟩ 

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

class herm_inner_product_space (α : Type*) [add_comm_group α] [vector_space ℂ α] extends sym_sesq_form ℂ α conj.ring_invo :=
(sesq_self_re_nonneg : ∀ (x : α), (sesq x x).re ≥ 0)
(sesq_self_eq_zero_iff : ∀ (x : α), sesq x x = 0 ↔ x = 0)

namespace herm_inner_product_space

open ring_invo

variables {α : Type*} [add_comm_group α] [vector_space ℂ α] [herm_inner_product_space α]

noncomputable def inner_product : α → α → ℂ := (herm_inner_product_space.to_sym_sesq_form α).to_sesq_form.sesq  

local infix `₀` : 74 := inner_product 

namespace inner_product

lemma conj_sym (x y : α) : conj (x ₀ y) = y ₀ x := sym_sesq_form.map_sesq conj.ring_invo y x 

lemma self_re_nonneg (x : α) : (x ₀ x).re ≥ 0 := sesq_self_re_nonneg x   

lemma self_eq_zero_iff {x : α} : (inner_product x x) = 0 ↔ x = (0 : α) := sesq_self_eq_zero_iff x

@[simp] lemma add_left (x y z : α) : 
(x + y) ₀ z = x ₀ z + y ₀ z := sesq_form.sesq_add_left _ _ _ _
 
@[simp] lemma add_right (x y z : α) : 
x ₀ (y + z) = x ₀ y + x ₀ z := sesq_form.sesq_add_right _ _ _ _

@[simp] lemma smul_left (a : ℂ) (x y : α) :
(a • x) ₀ y = a * (x ₀ y) := sesq_form.sesq_smul_left _ _ _ _

@[simp] lemma smul_right (a : ℂ) (x y : α) :
x ₀ (a • y) = conj(a) * (x ₀ y) := sesq_form.sesq_smul_right _ _ _ _

open sym_sesq_form sesq_form

@[simp] lemma zero_left (x : α) :
0 ₀ x = 0 := zero_sesq x  

@[simp] lemma zero_right (x : α) :
x ₀ 0 = 0 := sesq_zero x 

@[simp] lemma neg_left (x y : α) : 
-x ₀ y = -(x ₀ y) := sesq_neg_left x y 

@[simp] lemma neg_right (x y : α) : 
x ₀ -y = -(x ₀ y) := sesq_neg_right x y   

lemma sub_left (x y z : α) : 
(x - y) ₀ z = (x ₀ z) - (y ₀ z) := sesq_sub_left x y z

lemma sub_right (x y z : α) : 
x ₀ (y - z) = (x ₀ y) - (x ₀ z) := sesq_sub_right x y z

theorem self_im (x : α) :
(x ₀ x).im = 0 :=
(im_eq_zero_iff_conj_eq (x ₀ x)).mpr (inner_product.conj_sym x x)

lemma self_re_eq_zero (x : α) : 
(x ₀ x).re = 0 ↔ x = 0 := 
begin
  split; intros H,
  { suffices : x ₀ x = 0,
    { exact inner_product.self_eq_zero_iff.mp this },
    { apply complex.ext,
      { simpa },

      { rw [self_im, zero_im] }}},

  { rw H,
    simp }
end

lemma self_ne_zero_iff {x : α} : 
(x ₀ x) ≠ 0 ↔ x ≠ 0 :=
⟨ λ H, (iff_false_left H).mp inner_product.self_eq_zero_iff, 
  λ H, (iff_false_right H).mp inner_product.self_eq_zero_iff⟩ 

lemma self_re_ne_zero_iff {x : α} : 
(x ₀ x).re ≠ 0 ↔ x ≠ 0 :=
begin
  split; intros H,
  { have Ho : (x ₀ x) ≠ 0,
    { intros Hx,
      rw [Hx, zero_re] at H,
      trivial },
    exact self_ne_zero_iff.mp Ho },

  { have Ho : (x ₀ x) ≠ 0,
    { exact self_ne_zero_iff.mpr H },
    exact ne_zero_im_zero_imp_re_ne_zero Ho (self_im x) } 
end

lemma re (x y : α) : (x ₀ y).re = (y ₀ x).re := 
by rw [←inner_product.conj_sym, conj_re]

lemma im (x y : α) : (x ₀ y).im = -(y ₀ x).im :=
by rw [←inner_product.conj_sym, conj_im]

end inner_product

noncomputable def herm_norm (x : α) := sqrt((x ₀ x).re)

local notation |a| := herm_norm a 

lemma mul_self_herm_norm (x : α) : |x| * |x| = (x ₀ x).re :=
begin
  dunfold herm_norm,
  rw mul_self_sqrt (inner_product.self_re_nonneg x),
end

lemma herm_norm_sqr (x : α) : |x|^2 = (x ₀ x).re := 
by rw pow_two; exact mul_self_herm_norm x

open classical

theorem abs_inner_product_le_mul_herm_norm (x y : α) :
abs((x ₀ y)) ≤ |x|*|y| := 
begin
  intros,
  have ho : y = 0 ∨ y ≠ 0,
  { apply em },
  cases ho,
  { rw ho,
    dunfold herm_norm,
    simp },

  { have H : 0 ≤ |x - ((x ₀ y)/(↑( |y|*|y| ))) • y| * |x - ((x ₀ y)/(↑( |y|*|y| ))) • y| ,
    { dunfold herm_norm, 
      apply mul_nonneg (sqrt_nonneg (((x - (x ₀ y / ↑(sqrt ((y ₀ y).re) * sqrt ((y ₀ y).re))) • y) ₀ (x - (x ₀ y / ↑(sqrt ((y ₀ y).re) * sqrt ((y ₀ y).re))) • y)).re)) (sqrt_nonneg (((x - (x ₀ y / ↑(sqrt ((y ₀ y).re) * sqrt ((y ₀ y).re))) • y) ₀ (x - (x ₀ y / ↑(sqrt ((y ₀ y).re) * sqrt ((y ₀ y).re))) • y)).re)) }, 
    rw [sub_eq_add_neg, of_real_mul] at H,
    unfold herm_norm at H,
    rw [mul_self_sqrt (inner_product.self_re_nonneg ((x + -((x ₀ y / (↑(sqrt ((y ₀ y).re)) * ↑(sqrt ((y ₀ y).re)))) • y)))), 
      ←of_real_mul,
      of_real_inj.mpr (mul_self_sqrt (inner_product.self_re_nonneg y))] at H, 
    suffices H : 0 ≤ (x ₀ x).re + ((x ₀ -((x ₀ y / ↑((y ₀ y).re)) • y)).re + ((x ₀ -((x ₀ y / ↑((y ₀ y).re)) • y)).re + (-((x ₀ y / ↑((y ₀ y).re)) • y) ₀ -((x ₀ y / ↑((y ₀ y).re)) • y)).re)),
    { have he : (-((x ₀ y / ↑((y ₀ y).re)) • y) ₀ -((x ₀ y / ↑((y ₀ y).re)) • y)).re = -(x ₀ -((x ₀ y / ↑((y ₀ y).re)) • y)).re,
      { rw [inner_product.neg_right, inner_product.neg_right, inner_product.neg_left, inner_product.smul_left,
          inner_product.smul_right, inner_product.smul_right],
        have hr : y ₀ y = ↑((y ₀ y).re),
          rw re_of_real (inner_product.self_im y),
        rw [conj_div, conj_of_real, ←hr,
          div_mul_cancel (conj(x ₀ y)) ((iff_false_right ho).mp inner_product.self_eq_zero_iff),
          div_mul_eq_mul_div, div_mul_eq_mul_div, field.mul_comm],
        refl }, 
      rw [he, add_neg_self, field.add_zero, inner_product.neg_right, inner_product.smul_right,
        conj_div, conj_of_real] at H,
      dunfold herm_norm,
      dunfold complex.abs, 
      rw [←sqrt_mul (inner_product.self_re_nonneg x),
        sqrt_le (norm_sq_nonneg (x ₀ y)) (mul_nonneg (inner_product.self_re_nonneg x) (inner_product.self_re_nonneg y))], 
      rw [←sub_le_iff_le_add', sub_eq_neg_add, field.add_zero, div_mul_eq_mul_div,
        neg_re, neg_le_neg_iff, field.mul_comm, mul_conj, ←of_real_div, of_real_re,
        div_le_iff (lt_of_le_of_ne (inner_product.self_re_nonneg y) ((ne_comm).mp (ne_zero_im_zero_imp_re_ne_zero  (inner_product.self_ne_zero_iff.mpr ho) (inner_product.self_im y))))] at H,
      exact H },
    { rw [inner_product.add_left, inner_product.add_right, inner_product.add_right, add_re, 
      add_re, add_re, inner_product.re (-((x ₀ y / ↑((y ₀ y).re)) • y)) x, field.add_assoc] at H,
      exact H }}
end

def herm_norm_eq_zero_iff (x : α) :
|x| = 0 ↔ x = 0 := 
begin
  dunfold herm_norm,
  rw sqrt_eq_zero (inner_product.self_re_nonneg x),
  exact (inner_product.self_re_eq_zero x),
end

theorem abs_inner_product_eq_mul_herm_norm_iff (x y : α) : 
abs(x ₀ y) = |x|*|y| ↔ (∃ (a : ℂ), x = a • y) ∨ (∃ (a : ℂ), y = a • x) :=
begin
  dunfold herm_norm,
  dunfold complex.abs,
  rw [←sqrt_mul (inner_product.self_re_nonneg x),
    sqrt_inj (norm_sq_nonneg _) (mul_nonneg (inner_product.self_re_nonneg x) (inner_product.self_re_nonneg y))],  
  split; intros H,
  { have ho : y = 0 ∨ y ≠ 0,
    { apply em },
    cases ho,
    { rw ho,
      apply or.intro_right,
      apply exists.intro (0 : ℂ),
      rw zero_smul },

    { suffices : |x - ((x ₀ y)/(↑( |y|*|y| ))) • y| * |x - ((x ₀ y)/(↑( |y|*|y| ))) • y| = 0,
      { have Ht : |x - ((x ₀ y)/(↑( |y|*|y| ))) • y| = 0,
        { exact eq_zero_of_mul_self_eq_zero this },
        rw herm_norm_eq_zero_iff at Ht,
        unfold herm_norm at Ht,
        rw sub_eq_zero at Ht,
        exact or.intro_left _ (exists.intro (x ₀ y / ↑(sqrt ((y ₀ y).re) * sqrt ((y ₀ y).re))) Ht) },
      { have He : |x - ((x ₀ y)/(↑( |y|*|y| ))) • y| * |x - ((x ₀ y)/(↑( |y|*|y| ))) • y| = |x|*|x| - (abs(x ₀ y)^2)/ ( |y|*|y| ),
        { rw [sub_eq_add_neg, of_real_mul],
          dunfold herm_norm,
          rw [mul_self_sqrt (inner_product.self_re_nonneg ((x + -((x ₀ y / (↑(sqrt ((y ₀ y).re)) * ↑(sqrt ((y ₀ y).re)))) • y)))), 
            ←of_real_mul, of_real_inj.mpr (mul_self_sqrt (inner_product.self_re_nonneg y))],
          repeat {rw inner_product.add_left <|> rw inner_product.add_right <|> rw inner_product.smul_left <|> rw inner_product.smul_right},
          rw [add_re, add_re, ←inner_product.conj_sym x (-((x ₀ y / ↑((y ₀ y).re)) • y)),
            mul_self_sqrt (inner_product.self_re_nonneg x), mul_self_sqrt (inner_product.self_re_nonneg y),
            pow_two, mul_self_abs],
          have he : (-((x ₀ y / ↑((y ₀ y).re)) • y) ₀ -((x ₀ y / ↑((y ₀ y).re)) • y)).re = -(x ₀ -((x ₀ y / ↑((y ₀ y).re)) • y)).re,
          { rw [inner_product.neg_right, inner_product.neg_right, inner_product.neg_left,
              inner_product.smul_left, inner_product.smul_right, inner_product.smul_right],
            have hr : y ₀ y = ↑((y ₀ y).re),
            { rw re_of_real (inner_product.self_im y) },
            rw [conj_div, conj_of_real, ←hr,
              div_mul_cancel (conj(x ₀ y)) ((iff_false_right ho).mp inner_product.self_eq_zero_iff),
              div_mul_eq_mul_div, div_mul_eq_mul_div, field.mul_comm],
            refl },
          rw [add_re, he, re_of_real (inner_product.self_im y), conj_re, field.add_assoc,
            add_neg_self, field.add_zero, ←neg_smul, inner_product.smul_right, mul_re,
            conj_re, conj_im, neg_re, neg_im, neg_neg, sub_eq_add_neg, neg_mul_eq_neg_mul_symm,
            ←neg_add, div_eq_inv_mul, mul_re, mul_im, inv_re, inv_im, inner_product.self_im,
            neg_zero, zero_div, zero_mul, zero_mul, sub_zero, field.add_zero, field.mul_assoc,
            field.mul_assoc, ←field.left_distrib],
          dunfold norm_sq,
          rw [inner_product.self_im, mul_zero, field.add_zero, ←mul_div_right_comm,
            mul_div_mul_left _ (inner_product.self_re_ne_zero_iff.mpr ho) (inner_product.self_re_ne_zero_iff.mpr ho)],
          ring },  
        rw [He, sub_eq_zero, eq_comm, div_eq_iff_mul_eq, pow_two, mul_self_abs,
          mul_self_herm_norm, mul_self_herm_norm, H],
          rw mul_self_herm_norm,
          exact inner_product.self_re_ne_zero_iff.mpr ho }}},

  { dunfold complex.norm_sq,    
    cases H; cases H with a Ha; 
    rw Ha;
    repeat {rw inner_product.smul_left};
    rw inner_product.smul_right;
    repeat {rw mul_re};
    repeat {rw mul_im};
    rw [conj_im, conj_re, inner_product.self_im];
    ring }
end

noncomputable instance : metric_space α := 
{ dist := λ x y, |x - y|, 
  dist_self := 
    begin
      intros,
      unfold dist, 
      rw [sub_self, herm_norm_eq_zero_iff],
    end,
  eq_of_dist_eq_zero :=
    begin
      unfold dist,
      dunfold herm_norm,
      intros x y H,
      rw [sqrt_eq_zero (inner_product.self_re_nonneg (x - y)),
        ←zero_re] at H,
      have H1 : (x - y) ₀ (x - y) = 0,
      { exact complex.ext H (inner_product.self_im (x - y)) },
      rw inner_product.self_eq_zero_iff at H1,
      exact sub_eq_zero.mp H1,
    end,
  dist_comm := 
    begin
      intros,
      unfold dist, 
      dunfold herm_norm,
      rw [sqrt_inj (inner_product.self_re_nonneg (x - y)) (inner_product.self_re_nonneg (y - x)),
        ←neg_sub, inner_product.neg_left, inner_product.neg_right, neg_neg],
    end,
  dist_triangle := 
    begin 
      unfold dist,
      suffices : ∀ (x y : α), |x + y| ≤ |x| + |y|,
      { intros,
        have H : x - z = (x - y) + (y - z),
          simp,
        rw H, 
        exact this (x - y) (y - z) },
    
      { intros,
        have H : |x + y|*|x + y| = ((x + y) ₀ (x + y)).re,
        { dunfold herm_norm,
          rw mul_self_sqrt (inner_product.self_re_nonneg (x + y)) },
        rw [inner_product.add_left, inner_product.add_right, inner_product.add_right,
          ←inner_product.conj_sym x y, field.add_assoc, ←field.add_assoc (x ₀ y),
          add_conj, add_re, add_re, of_real_re] at H, 
        have hle : 2*(x ₀ y).re ≤ 2*abs(x ₀ y),
        { exact (mul_le_mul_left (lt_trans zero_lt_one (begin exact two_gt_one, end))).mpr (re_le_abs (x ₀ y)) },
        rw [←sub_zero (2 * abs (x ₀ y)), le_sub] at hle,
        suffices Hle :  |x + y| * |x + y| ≤ (x ₀ x).re + (y ₀ y).re + 2 * abs (x ₀ y),
        { have Hcs : 2*abs(x ₀ y) ≤ 2*|x|*|y|,
          { rw field.mul_assoc,
            exact (mul_le_mul_left (lt_trans zero_lt_one (begin exact two_gt_one, end))).mpr (abs_inner_product_le_mul_herm_norm x y) },
          have hz : 2*abs(x ₀ y) ≥ 0,
          { rw two_mul,
            have ha : abs(x ₀ y) ≥ 0,
            { exact abs_nonneg (x ₀ y) },
            exact le_add_of_le_of_nonneg ha ha },
          unfold herm_norm at Hcs,
          rw [←sub_zero (2 * sqrt ((x ₀ x).re) * sqrt ((y ₀ y).re)), le_sub] at Hcs,
          have Hs : |x + y|*|x + y| ≤ 2 * sqrt ((x ₀ x).re) * sqrt ((y ₀ y).re) - 2 * abs (x ₀ y) + ((x ₀ x).re + (y ₀ y).re + 2 * abs (x ₀ y)),
          { apply le_add_of_nonneg_of_le Hcs Hle },
          rw [sub_eq_add_neg, field.add_comm (2 * sqrt ((x ₀ x).re) * sqrt ((y ₀ y).re)), 
            field.add_assoc ((x ₀ x).re), field.add_comm, field.add_assoc,
            field.add_assoc, add_neg_cancel_left] at Hs, 
          have Hs' : |x + y| * |x + y| ≤ (x ₀ x).re + ((y ₀ y).re + 2 * sqrt ((x ₀ x).re) * sqrt ((y ₀ y).re)),
          { exact Hs },
          have He : (x ₀ x).re + ((y ₀ y).re + 2 * sqrt ((x ₀ x).re) * sqrt ((y ₀ y).re)) = (herm_norm(x) + herm_norm(y))*(herm_norm(x) + herm_norm(y)),
          { dunfold herm_norm,
            rw [field.right_distrib, field.left_distrib, field.left_distrib,
              ←sqrt_mul ((inner_product.self_re_nonneg x)), sqrt_mul_self ((inner_product.self_re_nonneg x)),
              ←pow_two, sqr_sqrt (inner_product.self_re_nonneg y)],
            ring },  
          rw He at Hs',
          apply (mul_self_le_mul_self_iff (begin intros, exact sqrt_nonneg (((x + y) ₀ (x + y)).re), end) (add_nonneg (begin intros, exact sqrt_nonneg ((x ₀ x).re), end) (begin intros, exact sqrt_nonneg ((y ₀ y).re), end))).mpr Hs'} ,    
      
        { suffices : |x + y| * |x + y| + 0 ≤ (x ₀ x).re + (2 * (x ₀ y).re + (y ₀ y).re) + (2 * abs (x ₀ y) - 2 * (x ₀ y).re),
          { simpa using this} ,
          { apply add_le_add (le_of_eq H) hle }}}
    end}

@[simp] lemma herm_norm_smul (a : ℂ) (x : α) : 
|a • x| = abs(a)*|x| := 
begin 
  intros, 
  dunfold herm_norm, 
  rw [inner_product.smul_left, inner_product.smul_right, ←field.mul_assoc,
    mul_conj, mul_re, of_real_im, zero_mul,
    sub_zero, of_real_re, sqrt_mul (norm_sq_nonneg a)],
  refl,
end

@[simp] lemma of_real_herm_norm_sqr (x : α) : 
↑( |x|^2 ) = x ₀ x :=
begin
  dunfold herm_norm,
  rw [sqr_sqrt (inner_product.self_re_nonneg x), re_of_real (inner_product.self_im x)],
end

@[simp] lemma of_real_herm_norm_mul_self (x : α) : 
↑( |x|*|x| ) = x ₀ x :=
begin
  dunfold herm_norm,
  rw [mul_self_sqrt (inner_product.self_re_nonneg x), re_of_real (inner_product.self_im x)],
end

noncomputable instance complex.metric_space : metric_space ℂ :=
{ dist := λ x y, abs(x - y),
  dist_self := by simp,
  eq_of_dist_eq_zero := assume x y H, sub_eq_zero.mp (complex.abs_eq_zero.mp H),
  dist_comm := begin intros, unfold dist, rw ←neg_sub, rw complex.abs_neg, end,
  dist_triangle := abs_sub_le}

noncomputable instance complex.normed_field : normed_field ℂ :=
{ norm := abs,
  dist_eq := by intros; refl, 
  norm_mul := abs_mul,}

noncomputable instance : normed_space ℂ α := 
{ norm := herm_norm,
  dist_eq := by intros; refl,
  norm_smul := herm_norm_smul}

@[simp] lemma herm_norm_zero : 
|(0 : α)| = 0 := @norm_zero α _

lemma norm_I_smul {W : Type*} [normed_space ℂ W] (x : W) :
∥I • x∥ = ∥x∥ :=
begin
  rw norm_smul,
  unfold norm,
  rw [abs_I, field.one_mul], 
end

@[simp] lemma herm_norm_I_smul (x : α) :
|I • x| = |x| := norm_I_smul x 

lemma norm_ne_zero_iff_ne_zero {G : Type*} [normed_group G] {g : G} : 
∥g∥ ≠ 0 ↔ g ≠ 0 := 
⟨ λ H, (iff_false_left H).mp (norm_eq_zero g), 
  λ H, (iff_false_right H).mp (norm_eq_zero g)⟩ 

theorem parallelogram_law (x y : α) :
|x + y|^2 + |x - y|^2 = 2*|x|^2 + 2*|y|^2 :=
begin
  dunfold herm_norm,
  rw [sqr_sqrt (inner_product.self_re_nonneg (x + y)), sqr_sqrt (inner_product.self_re_nonneg (x - y)),
    sqr_sqrt (inner_product.self_re_nonneg x), sqr_sqrt (inner_product.self_re_nonneg y)],
  suffices : (x ₀ x).re + ((x ₀ x).re + ((y ₀ y).re + (y ₀ y).re)) = 2 * (x ₀ x).re + 2 * (y ₀ y).re,
  { rw [inner_product.add_left, inner_product.add_right, inner_product.add_right,
      inner_product.sub_left, inner_product.sub_right, inner_product.sub_right,
      add_re, add_re, sub_re, sub_re, sub_re],
    simpa },
  { rw [←inner_product.conj_sym y, conj_re],
    ring }
end

lemma inner_product.self_add (x y : α) :
(x + y) ₀ (x + y) = (x ₀ x) + (y ₀ y) + (x ₀ y) + (y ₀ x) :=
begin
  rw [inner_product.add_left, inner_product.add_right, inner_product.add_right],
  simpa [field.add_assoc, field.add_comm],
end

def is_normalized (x : α) := |x| = 1

noncomputable def normalize (x : α) := (↑|x|⁻¹ : ℂ) • x 

lemma normalize.is_normalized (x : α) (ho : x ≠ 0) : 
is_normalized (normalize x) :=
begin
  dunfold is_normalized,
  dunfold normalize,
  dunfold herm_norm,
  rw [inner_product.smul_left, inner_product.smul_right, conj_of_real,
    mul_re, mul_re, of_real_im, zero_mul, zero_mul,
    sub_zero, sub_zero, of_real_re, ←sqrt_one,
    sqrt_inj (mul_nonneg (inv_nonneg.mpr (sqrt_nonneg (x ₀ x).re)) (mul_nonneg (inv_nonneg.mpr (sqrt_nonneg (x ₀ x).re)) (inner_product.self_re_nonneg x))) (zero_le_one), 
    ←sqrt_inv, ←field.mul_assoc],
  rw mul_self_sqrt,
  rw field.inv_mul_cancel, 
    exact (ne_zero_im_zero_imp_re_ne_zero (inner_product.self_ne_zero_iff.mpr ho) (inner_product.self_im x)),
    exact (inv_nonneg.mpr (inner_product.self_re_nonneg x)),
end

def normalize_set :
set α → set α := image(λ x, (↑|x|⁻¹ : ℂ) • x)

lemma normalize_set.is_normalized 
(A : set α) (Ho : (0 : α) ∉ A) : 
∀ x ∈ normalize_set(A), is_normalized x :=
begin
  dunfold normalize_set,
  dunfold image, 
  intros,
  have Ha : ∃ (a : α), a ∈ A ∧ normalize a = x,
  { rw mem_set_of_eq at H, 
    exact H },
  cases Ha with a Hl,
  rw ←Hl.right,
  have ho : a ≠ 0,
  { intros h,
    rw h at Hl,
    exact Ho Hl.left },
  exact normalize.is_normalized a ho,
end

def orthogonal (x y : α) : Prop := x ₀ y = 0 

local notation a ⊥ b := orthogonal a b 

def orthogonal_sym (x y : α) :
(x ⊥ y) ↔ (y ⊥ x) := @sym_sesq_form.ortho_sym ℂ α _ conj.ring_invo _ _ (to_sym_sesq_form α) _ _ 
 
lemma orthogonal_refl_iff_zero (x : α) : 
(x ⊥ x) ↔ x = 0 := inner_product.self_eq_zero_iff  

def orthogonal_smul_left (x y : α) (a : ℂ) (ha : a ≠ 0) : 
(x ⊥ y) ↔ ((a • x) ⊥ y) := @sesq_form.ortho_smul_left _ _ _ _ _ _ (herm_inner_product_space.to_sym_sesq_form α).to_sesq_form _ _ _ ha

def orthogonal_smul_right (x y : α) (a : ℂ) (ha : a ≠ 0) : 
(x ⊥ y) ↔ (x ⊥ (a • y)) := @sesq_form.ortho_smul_right _ _ _ _ _ _ (herm_inner_product_space.to_sym_sesq_form α).to_sesq_form _ _ _ ha

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

/-- Pythagorean Theorem -/
theorem sq_norm_add (x y : α) (H : x ⊥ y) :
|x + y|^2 = |x|^2 + |y|^2 :=
begin
  dunfold herm_norm,
  rw [sqr_sqrt (inner_product.self_re_nonneg (x + y)), sqr_sqrt (inner_product.self_re_nonneg x),
    sqr_sqrt (inner_product.self_re_nonneg y), inner_product.self_add],
  unfold orthogonal at H,
  rw [←inner_product.conj_sym x y, H, conj_zero,
    field.add_zero, field.add_zero, add_re],
end

def is_orthogonal_set (s : set α) :=
∀ x y ∈ s, (x ⊥ y) ↔ x ≠ y 

def is_orthonormal_set (s : set α) :=
is_orthogonal_set s ∧ ∀ x ∈ s, is_normalized x

noncomputable def proj (x y : α) :=
((y ₀ x)/( ↑|x|*|x| )) • x

lemma zero_proj (x : α) :
proj 0 x = 0 := by dunfold proj; simp

lemma proj_zero (x : α) :
proj x 0 = 0 := by dunfold proj; simp

lemma proj_self_eq_self (x : α) :
proj x x = x :=
begin
  have ho : x = 0 ∨ x ≠ 0,
  { apply em },
  dunfold proj,
  cases ho,
  { rw ho,
    simp },

  { rw [←of_real_mul, of_real_herm_norm_mul_self,
      div_self (inner_product.self_ne_zero_iff.mpr ho), one_smul] }
end

lemma smul_proj (x y : α) {a : ℂ} : 
proj x (a • y) = a • (proj x y) :=
begin
  dunfold proj,
  rw [inner_product.smul_left, smul_smul],
  ring,
end

lemma proj_smul (x y : α) {a : ℂ} (ha : a ≠ 0) :
proj (a • x) y = proj x y := 
begin
  have Hx : x = 0 ∨ x ≠ 0,
  { apply em },
  cases Hx,
  { rw [Hx, smul_zero] },

  { dunfold proj,
    rw [inner_product.smul_right, herm_norm_smul, of_real_mul, smul_smul],
    suffices :  ((↑(abs a) * ↑|x| * (↑(abs a) * ↑|x| ))⁻¹ * y ₀ x * conj a * a) • x = ((↑|x| * ↑|x| )⁻¹ * y ₀ x) • x,
    { rw [div_eq_inv_mul, div_eq_inv_mul,
        field.mul_comm (conj a), ←field.mul_assoc],
      exact this },
    { rw [field.mul_assoc, ←field.mul_comm a, mul_conj, 
        ←field.mul_assoc ( ↑(abs a) * ↑|x| ), field.mul_comm (↑(abs a)),
        field.mul_assoc ( ↑|x| ), ←of_real_mul, mul_self_abs,
        field.mul_comm ( ↑|x| ), field.mul_comm, field.mul_assoc,
        mul_inv_eq, field.mul_comm, field.mul_assoc ((↑|x| * ↑|x| )⁻¹),
        field.mul_comm (↑(norm_sq a))⁻¹, field.mul_assoc, field.mul_assoc (y ₀ x),
        field.inv_mul_cancel, field.mul_one],
      refl,
      
      exact of_real_ne_zero.mpr ((iff_false_right ha).mp (norm_sq_eq_zero)),
      exact (mul_ne_zero (of_real_ne_zero.mpr ((norm_ne_zero_iff_ne_zero).mpr Hx)) (of_real_ne_zero.mpr ((norm_ne_zero_iff_ne_zero).mpr Hx))),
      exact of_real_ne_zero.mpr ((iff_false_right ha).mp (norm_sq_eq_zero)) }}
end

lemma norm_proj_le (x y : α) : 
|proj x y| ≤ |y| :=
begin
  have Hx : x = 0 ∨ x ≠ 0,
  { apply em },
  cases Hx,
  { rw [Hx, zero_proj, herm_norm_zero],
    exact @norm_nonneg _ _ y },

  { dunfold proj,
    rw [herm_norm_smul, complex.abs_div, ←of_real_mul,
      abs_of_real, abs_mul_self, div_mul_comm, division_def,
      mul_inv', ←field.mul_assoc, field.mul_inv_cancel,
      field.one_mul, field.mul_comm, ←division_def, div_le_iff],
     
      exact abs_inner_product_le_mul_herm_norm y x,
      exact (norm_pos_iff x).mpr Hx,
      exact norm_ne_zero_iff_ne_zero.mpr Hx }
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
    exact exists.intro (y ₀ x / (↑|x| * ↑|x| )) (eq_comm.mp H) },

  { intros H,
    cases H with a Ha,
    rw [Ha, smul_proj, proj_self_eq_self] }
end

end herm_inner_product_space

class Hilbert_space (α : Type*) [add_comm_group α] [vector_space ℂ α] extends herm_inner_product_space α :=
(complete : ∀{f : filter α}, cauchy f → ∃x, f ≤ nhds x) 

instance Hilbert_space.to_complete_space (α : Type*) [add_comm_group α] [vector_space ℂ α] [Hilbert_space α] : complete_space α :=
{complete := @Hilbert_space.complete _ _ _ _}
