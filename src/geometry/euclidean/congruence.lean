/-
Copyright (c) 2023 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/

import topology.metric_space.isometry
import geometry.euclidean.triangle
import linear_algebra.affine_space.finite_dimensional

import tactic.swap_var

/-!
# Congruences

We define congruence, i.e., the equivalence between sets of points in a metric space where
all corresponding pairwise distances are the same. The motivating example is triangles in the plane.

## Main results

In the general case we show an `isometry_equiv` between the points: set.range v₁ ≃ᵢ set.range v₂.

In any real affine space, we show that congruence follows from SSS, SAS, and AAS congruence.

To show SSS and SAS, we expand the definition of an angle to write the cosine of it in terms of
the triangle side lengths (which is basically the same as using the cosine rule).
Then we show the sine rule, by epressing sin (∠ a b c) as sqrt (1 - cos (∠ a b c)^2), and
expanding the terms.
Then we use the sine rule to show AAS congruence.

## Notation

- (![a,b,c] : fin 3) → P represents triangle a b c.
- (v₁ ≅ v₂ : Prop) represents that (v₁ : ι → P₁) and (v₂ : ι → P₂) are congruent.

-/

noncomputable theory


def congruence {ι P₁ P₂ : Type*} (v₁ : ι → P₁) (v₂ : ι → P₂)
  [metric_space P₁] [metric_space P₂] : Prop :=
∀ (i₁ i₂ : ι), (dist (v₁ i₁) (v₁ i₂) = dist (v₂ i₁) (v₂ i₂))

infix `≅`:25 := congruence


variables {ι : Type*}
variables {P₁ P₂ P₃ : Type*} {v₁ : ι → P₁} {v₂ : ι → P₂} {v₃ : ι → P₃}
  [metric_space P₁] [metric_space P₂] [metric_space P₃]

namespace congruence


lemma to_dist_eq_dist (h : v₁ ≅ v₂) (i₁ i₂ : ι) : dist (v₁ i₁) (v₁ i₂) = dist (v₂ i₁) (v₂ i₂) :=
h i₁ i₂

protected lemma refl (v₁ : ι → P₁): v₁ ≅ v₁ := λ i₁ i₂, rfl

protected lemma symm (h : v₁ ≅ v₂) : v₂ ≅ v₁ := λ i₁ i₂, (h i₁ i₂).symm

protected lemma trans (h₁₂ : v₁ ≅ v₂) (h₂₃ : v₂ ≅ v₃) : v₁ ≅ v₃ :=
λ i₁ i₂, (h₁₂ i₁ i₂).trans (h₂₃ i₁ i₂)


-- this lemma is useful for changing the index set ι
lemma sub_congruence {ι' : Type*} (f : ι' → ι) (h : v₁ ≅ v₂) : (v₁ ∘ f) ≅ (v₂ ∘ f) :=
λ i₁ i₂, h (f i₁) (f i₂)


/-
this function maps the congruent points in one space to the corresponding points
in the other space.
-/
protected def map (h : v₁ ≅ v₂) : set.range v₁ → set.range v₂ :=
λ a, set.range_factorization v₂ $ set.range_splitting v₁ a

-- map does indeed preserve corresponding points
lemma map_sound (h : v₁ ≅ v₂) (i : ι) : ↑(h.map (set.range_factorization v₁ i)) = v₂ i :=
begin
  unfold congruence.map,
  rw set.range_factorization_coe v₂,
  rw ← dist_eq_zero,
  rw ← h,
  rw dist_eq_zero,
  rw set.apply_range_splitting v₁,
  rw set.range_factorization_coe v₁,
end

-- .map and .symm.map are inverses to eachother
protected lemma map_inverse_self (h : v₁ ≅ v₂) : function.left_inverse h.symm.map h.map :=
begin
  intro x,
  rw subtype.ext_iff,
  rw ← set.apply_range_splitting v₁ x,
  apply h.symm.map_sound (set.range_splitting v₁ x),
end

-- map as an `equiv`
protected def equiv (h : v₁ ≅ v₂) : set.range v₁ ≃ set.range v₂ :=
{ to_fun := h.map,
  inv_fun := h.symm.map,
  left_inv := h.map_inverse_self,
  right_inv := h.symm.map_inverse_self}

lemma equiv_sound (h : v₁ ≅ v₂) (i : ι) : ↑(h.equiv (set.range_factorization v₁ i)) = v₂ i :=
h.map_sound i

-- map as an `isometry_equiv`
protected def isometry (h : v₁ ≅ v₂) : set.range v₁ ≃ᵢ set.range v₂ :=
{ to_equiv := h.equiv,
  isometry_to_fun :=
  begin
    intros fx fy,
    rw [edist_dist, edist_dist], apply congr_arg ennreal.of_real,
    rw subtype.dist_eq fx fy,
    rw [← set.apply_range_splitting v₁ fx, ← set.apply_range_splitting v₁ fy],
    rw h.to_dist_eq_dist,
    refl,
  end}

lemma isometry_sound (h : v₁ ≅ v₂) (i : ι) :
  ↑(h.isometry (set.range_factorization v₁ i)) = v₂ i :=
h.map_sound i




open_locale euclidean_geometry

variables {V₁ V₂ : Type*} [inner_product_space ℝ  V₁] [inner_product_space ℝ V₂]
  [normed_add_torsor V₁ P₁] [normed_add_torsor V₂ P₂]





include V₁ V₂

lemma to_angle_eq_angle (h : v₁ ≅ v₂) (i₁ i₂ i₃ : ι) :
  ∠ (v₁ i₁) (v₁ i₂) (v₁ i₃) = ∠ (v₂ i₁) (v₂ i₂) (v₂ i₃) :=
begin
  unfold euclidean_geometry.angle, unfold inner_product_geometry.angle,
  have key := abs_le.1 (abs_real_inner_div_norm_mul_norm_le_one _ _),
  have key':= abs_le.1 (abs_real_inner_div_norm_mul_norm_le_one _ _),
  rw real.arccos_inj key.1 key.2 key'.1 key'.2,
  simp [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    ← normed_add_torsor.dist_eq_norm', h.to_dist_eq_dist],
end

omit V₁ V₂

variables {a b c : P₁} {d e f : P₂}


lemma _root_.fin.fin_3_swap_left {α : Type*} (a b c : α) : ![a,b,c] = ![b,a,c] ∘ ![1,0,2] :=
by {ext x, fin_cases x; refl}
lemma _root_.fin.fin_3_swap_right {α : Type*} (a b c : α) : ![a,b,c] = ![a,c,b] ∘ ![0,2,1] :=
by {ext x, fin_cases x; refl}


lemma triangle_swap_left (h : ![a,b,c] ≅ ![d,e,f]) : ![b,a,c] ≅ ![e,d,f] :=
begin
  rw [fin.fin_3_swap_left b a c, fin.fin_3_swap_left e d f],
  apply sub_congruence ![1,0,2] h,
end
lemma triangle_swap_right (h : ![a,b,c] ≅ ![d,e,f]) : ![a,c,b] ≅ ![d,f,e] :=
begin
  rw [fin.fin_3_swap_right a c b, fin.fin_3_swap_right d f e],
  apply sub_congruence ![0,2,1] h,
end

lemma side_side_side {a b c : P₁} {d e f : P₂} (hs₁ : dist a b = dist d e)
  (hs₂ : dist a c = dist d f) (hs₃ : dist b c = dist e f) : ![a,b,c] ≅ ![d,e,f] :=
begin
  intro i₁, fin_cases i₁; intro i₂; fin_cases i₂;
    simp [dist_comm]; assumption,
end

include V₁

lemma cos_angle_elim : real.cos (∠ a b c) =
  (dist a b * dist a b + dist b c * dist b c - dist a c * dist a c) / (2 * dist a b * dist b c) :=
begin
  unfold euclidean_geometry.angle, rw inner_product_geometry.cos_angle,
  rw real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
  simp [ ← normed_add_torsor.dist_eq_norm'],
  rw [div_div, mul_assoc, dist_comm b c],
end



lemma sin_angle_elim : real.sin (∠ a b c) =
  real.sqrt (1 - ((dist a b ^ 2 + dist b c ^ 2 - dist a c ^ 2) ^ 2) /
    (2 * dist a b * dist b c) ^ 2) :=
begin
  rw real.sin_eq_sqrt_one_sub_cos_sq
    (euclidean_geometry.angle_nonneg a b c)
    (euclidean_geometry.angle_le_pi a b c),
  rw [cos_angle_elim, ← pow_two, ← pow_two, ← pow_two, div_pow],
end

omit V₁

/-
the library contains a similar lemma, but it requires the numerator to be positive instead of
the denominator, so this is more useful in this case.
-/
lemma _root_.real.sqrt_div_sq :
  ∀ {y : ℝ}, 0 ≤ y → ∀ (x : ℝ), real.sqrt (x / y^2) = real.sqrt x / y :=
begin
  intros y hy x,
  rw [div_eq_inv_mul, div_eq_inv_mul],
  rw [real.sqrt_mul, real.sqrt_inv, real.sqrt_sq hy],
  rw inv_nonneg, exact sq_nonneg y,
end



include V₁ V₂

lemma side_angle_side (ha : ∠ a b c = ∠ d e f)
  (hs₁ : dist a b = dist d e) (hs₂ : dist b c = dist e f) : ![a,b,c] ≅ ![d,e,f] :=
begin
  refine side_side_side hs₁ _ hs₂,
  by_cases h : dist a b = 0,
  { rw h at hs₁,
    replace hs₁ := hs₁.symm,
    rw dist_eq_zero at hs₁ h,
    rw [h, hs₁], exact hs₂ },
  by_cases h' : dist b c = 0,
  { rw h' at hs₂,
    replace hs₂ := hs₂.symm,
    rw dist_eq_zero at hs₂ h',
    rw [← h', ← hs₂], exact hs₁ },

  apply_fun real.cos at ha,
  simp [cos_angle_elim, ← hs₁, ← hs₂] at ha,
  rw div_left_inj'
    (mul_ne_zero_iff.2 ⟨mul_ne_zero_iff.2 ⟨show (2:ℝ) ≠ 0, from by simp, h⟩, h'⟩) at ha,
  rw sub_right_inj at ha,
  rw [← pow_two , ← pow_two] at ha,
  rw sq_eq_sq dist_nonneg dist_nonneg at ha,
  exact ha,

end

omit V₂

lemma sine_rule (hac : a ≠ c) (hbc : b ≠ c) :
  real.sin (∠ a b c) / dist a c = real.sin (∠ b a c) / dist b c :=
begin
  by_cases hab : a = b, rw hab, change a ≠ b at hab,
  rw ← dist_pos at hab hbc hac,

  simp [sin_angle_elim, dist_comm],
  rw [sub_div', sub_div', real.sqrt_div_sq, div_div],
  rw [real.sqrt_div_sq, div_div],
  ring_nf,
  { apply mul_nonneg, apply mul_nonneg, simp, exact dist_nonneg, exact dist_nonneg },
  { apply mul_nonneg, apply mul_nonneg, simp, exact dist_nonneg, exact dist_nonneg },
  { apply ne_of_gt, apply sq_pos_of_ne_zero, apply mul_ne_zero, apply mul_ne_zero,
    simp, exact ne_of_gt hab, exact ne_of_gt hac },
  { apply ne_of_gt, apply sq_pos_of_ne_zero, apply mul_ne_zero, apply mul_ne_zero,
    simp, exact ne_of_gt hab, exact ne_of_gt hbc },
end

include V₂


lemma angle_angle_side (ha₁ : ∠ a b c = ∠ d e f) (ha₂ : ∠ b a c = ∠ e d f)
  (hs : dist b c = dist e f)
  (habc : ¬ collinear ℝ ({a, b, c} : set P₁)) (hdef : ¬ collinear ℝ ({d, e, f} : set P₂)) :
    ![a,b,c] ≅ ![d,e,f] :=
begin
  swap_var [b ↔ c, e ↔ f],
  have ha₃ := euclidean_geometry.angle_add_angle_add_angle_eq_pi
    (ne₁₃_of_not_collinear habc) (ne₂₃_of_not_collinear habc),
  rw ← euclidean_geometry.angle_add_angle_add_angle_eq_pi
    (ne₁₃_of_not_collinear hdef) (ne₂₃_of_not_collinear hdef) at ha₃,
  simp [euclidean_geometry.angle_comm] at ha₃,
  rw [ha₁, ha₂, add_left_cancel_iff] at ha₃,

  have s := sine_rule (ne₁₃_of_not_collinear habc) (ne₂₃_of_not_collinear habc),
  have s':= sine_rule (ne₁₃_of_not_collinear hdef) (ne₂₃_of_not_collinear hdef),
  rw [ha₁, ha₂, hs] at s,
  rw ← s' at s,
  rw [div_eq_mul_inv, div_eq_mul_inv] at s,
  rw mul_right_inj' at s, swap,
  { apply ne_of_gt,
    apply real.sin_pos_of_pos_of_lt_pi,
    apply euclidean_geometry.angle_pos_of_not_collinear hdef,
    apply euclidean_geometry.angle_lt_pi_of_not_collinear hdef },
  rw inv_inj at s,
  apply triangle_swap_right,
  rw [dist_comm c b, dist_comm f e] at hs,
  apply side_angle_side ha₃ s hs,
end

end congruence
