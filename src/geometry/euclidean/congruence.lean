/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/

import topology.metric_space.congruence
import geometry.euclidean.triangle
import linear_algebra.affine_space.finite_dimensional

import tactic.swap_var

/-!
# Congruences in Euclidean geometry

In any real affine space, we show that congruence follows from SSS, SAS, and AAS congruence.

To show SSS and SAS, we expand the definition of an angle to write the cosine of it in terms of
the triangle side lengths (which is basically the same as using the cosine rule).
Then we show the sine rule, by epressing sin (∠ a b c) as sqrt (1 - cos (∠ a b c)^2), and
expanding the terms.
Then we use the sine rule to show AAS congruence.

-/

noncomputable theory
open_locale euclidean_geometry congruence
open euclidean_geometry congruence real
namespace congruence

variables {ι V₁ V₂ P₁ P₂ : Type*}
  [inner_product_space ℝ  V₁] [inner_product_space ℝ V₂]
  [metric_space P₁]           [metric_space P₂]
  [normed_add_torsor V₁ P₁]   [normed_add_torsor V₂ P₂]
  {v₁ : ι → P₁} {v₂ : ι → P₂}
  {a b c : P₁} {d e f : P₂}






include V₁ V₂

lemma angle_eq (h : v₁ ≅ v₂) (i₁ i₂ i₃ : ι) :
  ∠ (v₁ i₁) (v₁ i₂) (v₁ i₃) = ∠ (v₂ i₁) (v₂ i₂) (v₂ i₃) :=
begin
  unfold euclidean_geometry.angle, unfold inner_product_geometry.angle,
  have key := abs_le.1 (abs_real_inner_div_norm_mul_norm_le_one _ _),
  have key':= abs_le.1 (abs_real_inner_div_norm_mul_norm_le_one _ _),
  rw arccos_inj key.1 key.2 key'.1 key'.2,
  simp [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    ← normed_add_torsor.dist_eq_norm', h.dist_eq],
end




omit V₂

lemma sin_pos_of_not_collinear (h : ¬ collinear ℝ ({a, b, c} : set P₁)) :
  0 < sin (∠ a b c) :=
begin
  apply sin_pos_of_pos_of_lt_pi,
  apply angle_pos_of_not_collinear h,
  apply angle_lt_pi_of_not_collinear h,
end


include V₂


lemma angle_angle_side (ha₁ : ∠ a b c = ∠ d e f) (ha₂ : ∠ b a c = ∠ e d f)
  (hs : dist b c = dist e f)
  (habc : ¬ collinear ℝ ({a, b, c} : set P₁)) (hdef : ¬ collinear ℝ ({d, e, f} : set P₂)) :
    ![a,b,c] ≅ ![d,e,f] :=
begin
  swap_var [b ↔ c, e ↔ f],
  have ha₃ := angle_add_angle_add_angle_eq_pi
    (ne₁₃_of_not_collinear habc) (ne₂₃_of_not_collinear habc),
  rw ← angle_add_angle_add_angle_eq_pi
    (ne₁₃_of_not_collinear hdef) (ne₂₃_of_not_collinear hdef) at ha₃,
  simp [angle_comm] at ha₃,
  rw [ha₁, ha₂, add_left_cancel_iff] at ha₃,

  have s := sine_rule (ne₁₃_of_not_collinear habc) (ne₂₃_of_not_collinear habc),
  have s':= sine_rule (ne₁₃_of_not_collinear hdef) (ne₂₃_of_not_collinear hdef),
  rw [ha₁, ha₂, hs] at s,
  rw ← s' at s,
  rw [div_eq_mul_inv, div_eq_mul_inv] at s,
  rw mul_right_inj' at s, swap,
  { apply ne_of_gt,
    apply sin_pos_of_pos_of_lt_pi,
    apply angle_pos_of_not_collinear hdef,
    apply angle_lt_pi_of_not_collinear hdef },
  rw inv_inj at s,
  have : ![a,c,b] = ![a,b,c] ∘ (equiv.swap 1 2), { ext x, fin_cases x; refl }, rw this,
  have : ![d,f,e] = ![d,e,f] ∘ (equiv.swap 1 2), { ext x, fin_cases x; refl }, rw this,
  rw index_equiv,
  rw [dist_comm c b, dist_comm f e] at hs,
  apply side_angle_side ha₃ s hs,
end


end congruence
