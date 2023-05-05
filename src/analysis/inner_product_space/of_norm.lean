/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/

import topology.algebra.algebra
import analysis.inner_product_space.basic

/-!
# Inner product space derived from a norm

This file defines an `inner_product_space` instance from a norm that respects the
parallellogram identity. The parallelogram identity is a way to express the inner product of `x` and
`y` in terms of the norms of `x`, `y`, `x + y`, `x - y`.

## Main results

- `inner_product_space.of_norm`: a normed space whose norm respects the parallellogram identity,
  can be seen as an inner product space.

## Tags

inner product space, Hilbert space, norm

## References

- [Jordan, P. and von Neumann, J., *On inner products in linear, metric spaces*][Jordan1935]
- https://math.stackexchange.com/questions/21792/norms-induced-by-inner-products-and-the-parallelogram-law
- https://math.dartmouth.edu/archive/m113w10/public_html/jordan-vneumann-thm.pdf
-/

open is_R_or_C
open_locale complex_conjugate

/-- Predicate for the parallelogram identity to hold. -/
class inner_product_spaceable (E : Type*) [normed_add_comm_group E] : Prop :=
(parallelogram_identity :
  ∀ x y : E, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖))

variables (𝕜 : Type*) [is_R_or_C 𝕜] {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  [inner_product_spaceable E]

variables (𝕜)

local notation `𝓚` := algebra_map ℝ 𝕜

/-- Auxiliary definition of the inner product derived from the norm. -/
private noncomputable def inner_ (x y : E) : 𝕜 :=
4⁻¹ * ((𝓚 ‖x + y‖) * (𝓚 ‖x + y‖) - (𝓚 ‖x - y‖) * (𝓚 ‖x - y‖)
          + (I:𝕜) * (𝓚 ‖(I:𝕜) • x + y‖) * (𝓚 ‖(I:𝕜) • x + y‖)
          - (I:𝕜) * (𝓚 ‖(I:𝕜) • x - y‖) * (𝓚 ‖(I:𝕜) • x - y‖))

namespace inner_product_spaceable

variables {𝕜} (E)

/-- Auxiliary definition for the `add_left` property -/
private def inner_prop (r : 𝕜) : Prop := ∀ x y : E, inner_ 𝕜 (r • x) y = conj r * inner_ 𝕜 x y

variables {E}

private lemma add_left_aux1 [inner_product_spaceable E] (x y z : E) :
  ‖x + y + z‖ * ‖x + y + z‖ =
    (‖2 • x + y‖ * ‖2 • x + y‖ + ‖2 • z + y‖ * ‖2 • z + y‖) / 2 - ‖x - z‖ * ‖x - z‖ :=
begin
  rw [eq_sub_iff_add_eq, eq_div_iff (two_ne_zero' ℝ), mul_comm _ (2 : ℝ), eq_comm],
  convert parallelogram_identity (x + y + z) (x - z) using 4; { rw two_smul, abel }
end

private lemma add_left_aux2 [inner_product_spaceable E] (x y z : E) :
  ‖x + y - z‖ * ‖x + y - z‖ =
    (‖2 • x + y‖ * ‖2 • x + y‖ + ‖y - 2 • z‖ * ‖y - 2 • z‖) / 2 - ‖x + z‖ * ‖x + z‖ :=
begin
  rw [eq_sub_iff_add_eq, eq_div_iff (two_ne_zero' ℝ), mul_comm _ (2 : ℝ), eq_comm],
  have h₀ := parallelogram_identity (x + y - z) (x + z),
  convert h₀ using 4; { rw two_smul, abel }
end

private lemma add_left_aux2' [inner_product_spaceable E] (x y z : E) :
  ‖x + y + z‖ * ‖x + y + z‖ - ‖x + y - z‖ * ‖x + y - z‖ =
  ‖x + z‖ * ‖x + z‖ - ‖x - z‖ * ‖x - z‖ +
      (‖2 • z + y‖ * ‖2 • z + y‖ - ‖y - 2 • z‖ * ‖y - 2 • z‖) / 2 :=
by { rw [add_left_aux1 , add_left_aux2], ring }

private lemma add_left_aux3 [inner_product_spaceable E] (y z : E) :
  ‖2 • z + y‖ * ‖2 • z + y‖ = 2 * (‖y + z‖ * ‖y + z‖ + ‖z‖ * ‖z‖) - ‖y‖ * ‖y‖ :=
begin
  apply eq_sub_of_add_eq,
  convert parallelogram_identity (y + z) z using 4; { try { rw two_smul }, abel }
end

private lemma add_left_aux4 [inner_product_spaceable E] (y z : E) :
  ‖y - 2 • z‖ * ‖y - 2 • z‖ = 2 * (‖y - z‖ * ‖y - z‖ + ‖z‖ * ‖z‖) - ‖y‖ * ‖y‖ :=
begin
  apply eq_sub_of_add_eq,
  have h₀ := parallelogram_identity (y - z) z,
  conv_lhs at h₀ { rw add_comm },
  convert h₀ using 4; { try { rw two_smul }, abel }
end

private lemma add_left_aux4' [inner_product_spaceable E] (y z : E) :
  (‖2 • z + y‖ * ‖2 • z + y‖ - ‖y - 2 • z‖ * ‖y - 2 • z‖) / 2 =
    (‖y + z‖ * ‖y + z‖) - (‖y - z‖ * ‖y - z‖) :=
by { rw [add_left_aux3 , add_left_aux4], ring }

lemma add_left_aux5 [inner_product_spaceable E] (x y z : E) :
  ‖(I : 𝕜) • (x + y) + z‖ * ‖(I : 𝕜) • (x + y) + z‖ =
    (‖(I : 𝕜) • (2 • x + y)‖ * ‖(I : 𝕜) • (2 • x + y)‖ +
      ‖(I : 𝕜) • y + 2 • z‖ * ‖(I : 𝕜) • y + 2 • z‖) / 2 -
    ‖(I : 𝕜) • x - z‖ * ‖(I : 𝕜) • x - z‖ :=
begin
  rw [eq_sub_iff_add_eq, eq_div_iff (two_ne_zero' ℝ), mul_comm _ (2 : ℝ), eq_comm],
  have h₀ := parallelogram_identity ((I : 𝕜) • (x + y) + z) ((I : 𝕜) • x - z),
  convert h₀ using 4; { try { simp only [two_smul, smul_add] }, abel }
end

lemma add_left_aux6 [inner_product_spaceable E] (x y z : E) :
  ‖(I : 𝕜) • (x + y) - z‖ * ‖(I : 𝕜) • (x + y) - z‖ =
    (‖(I : 𝕜) • (2 • x + y)‖ * ‖(I : 𝕜) • (2 • x + y)‖ +
      ‖(I : 𝕜) • y - 2 • z‖ * ‖(I : 𝕜) • y - 2 • z‖) / 2 -
    ‖(I : 𝕜) • x + z‖ * ‖(I : 𝕜) • x + z‖ :=
begin
  rw [eq_sub_iff_add_eq, eq_div_iff (two_ne_zero' ℝ), mul_comm _ (2 : ℝ), eq_comm],
  have h₀ := parallelogram_identity ((I : 𝕜) • (x + y) - z) ((I : 𝕜) • x + z),
  convert h₀ using 4; { try { simp only [two_smul, smul_add] }, abel }
end

lemma add_left_aux7 [inner_product_spaceable E] (y z : E) :
  ‖(I : 𝕜) • y + 2 • z‖ * ‖(I : 𝕜) • y + 2 • z‖ =
    2 * (‖(I : 𝕜) • y + z‖ * ‖(I : 𝕜) • y + z‖ + ‖z‖ * ‖z‖) -
    ‖(I : 𝕜) • y‖ * ‖(I : 𝕜) • y‖ :=
begin
  apply eq_sub_of_add_eq,
  have h₀ := parallelogram_identity ((I : 𝕜) • y + z) z,
  convert h₀ using 4; { try { simp only [two_smul, smul_add] }, abel }
end

lemma add_left_aux8 [inner_product_spaceable E] (y z : E) :
  ‖(I : 𝕜) • y - 2 • z‖ * ‖(I : 𝕜) • y - 2 • z‖ =
    2 * (‖(I : 𝕜) • y - z‖ * ‖(I : 𝕜) • y - z‖ + ‖z‖ * ‖z‖) -
    ‖(I : 𝕜) • y‖ * ‖(I : 𝕜) • y‖ :=
begin
  apply eq_sub_of_add_eq,
  have h₀ := parallelogram_identity ((I : 𝕜) • y - z) z,
  rw add_comm,
  convert h₀ using 4; { try { simp only [two_smul, smul_add] }, abel }
end

lemma add_left [inner_product_spaceable E] (x y z : E) :
  inner_ 𝕜 (x + y) z = inner_ 𝕜 x z + inner_ 𝕜 y z :=
begin
  simp only [inner_, ←mul_add],
  congr,
  simp only [mul_assoc, ←map_mul, add_sub_assoc, ←mul_sub, ←map_sub],
  rw add_add_add_comm,
  simp only [←map_add, ←mul_add],
  congr,
  { rw [←add_sub_assoc, add_left_aux2', add_left_aux4'] },
  { rw [add_left_aux5, add_left_aux6, add_left_aux7, add_left_aux8],
    simp only [map_sub, map_mul, map_add, div_eq_mul_inv],
    ring }
end

lemma nat [inner_product_spaceable E] (n : ℕ) (x y : E) :
  inner_ 𝕜 ((n : 𝕜) • x) y = (n : 𝕜) * inner_ 𝕜 x y :=
begin
  induction n with n ih,
  { simp only [inner_, nat.nat_zero_eq_zero, zero_sub, nat.cast_zero, zero_mul, eq_self_iff_true,
      zero_smul, zero_add, mul_zero, sub_self, norm_neg, smul_zero], },
  { simp only [nat.cast_succ, add_smul, one_smul],
    rw [add_left, ih, add_mul, one_mul] }
end

private lemma nat_prop [inner_product_spaceable E] (r : ℕ) :
  inner_prop E (r : 𝕜) :=
λ x y, by { simp only [map_nat_cast], exact nat r x y }

lemma inner_prop_neg_one : inner_prop E ((-1 : ℤ) : 𝕜) :=
begin
  intros x y,
  simp only [inner_, neg_mul_eq_neg_mul, one_mul, int.cast_one, one_smul, ring_hom.map_one,
    map_neg, int.cast_neg, neg_smul, neg_one_mul],
  rw neg_mul_comm,
  congr' 1,
  have h₁ : ‖-x - y‖ = ‖x + y‖,
  { rw [←neg_add', norm_neg], },
  have h₂ : ‖-x + y‖ = ‖x - y‖,
  { rw [←neg_sub, norm_neg, sub_eq_neg_add], },
  have h₃ : ‖(I : 𝕜) • (-x) + y‖ = ‖(I : 𝕜) • x - y‖,
  { rw [←neg_sub, norm_neg, sub_eq_neg_add, ←smul_neg], },
  have h₄ : ‖(I : 𝕜) • (-x) - y‖ = ‖(I : 𝕜) • x + y‖,
  { rw [smul_neg, ←neg_add', norm_neg] },
  rw [h₁, h₂, h₃, h₄],
  ring,
end

lemma int_prop [inner_product_spaceable E] (n : ℤ) :
  inner_prop E (n : 𝕜) :=
begin
  intros x y,
  rw ←n.sign_mul_nat_abs,
  simp only [int.cast_coe_nat, map_nat_cast, map_int_cast, int.cast_mul, map_mul, mul_smul],
  obtain hn | rfl | hn := lt_trichotomy n 0,
  { rw [int.sign_eq_neg_one_of_neg hn, inner_prop_neg_one ((n.nat_abs : 𝕜) • x), nat],
    simp only [map_neg, neg_mul, one_mul, mul_eq_mul_left_iff, true_or,
      int.nat_abs_eq_zero, eq_self_iff_true, int.cast_one, map_one, neg_inj, nat.cast_eq_zero,
      int.cast_neg] },
  { simp only [inner_, int.cast_zero, zero_sub, nat.cast_zero, zero_mul, eq_self_iff_true,
      int.sign_zero, zero_smul, zero_add, mul_zero, smul_zero, sub_self, norm_neg,
      int.nat_abs_zero] },
  { rw int.sign_eq_one_of_pos hn,
    simp only [one_mul, mul_eq_mul_left_iff, true_or, int.nat_abs_eq_zero, eq_self_iff_true,
      int.cast_one, one_smul, nat.cast_eq_zero, nat] }
end

lemma rat_prop [inner_product_spaceable E] (r : ℚ) :
  inner_prop E (r : 𝕜) :=
begin
  intros x y,
  have : (r.denom : 𝕜) ≠ 0,
  { haveI : char_zero 𝕜 := is_R_or_C.char_zero_R_or_C,
    exact_mod_cast r.pos.ne' },
  rw [←r.num_div_denom, ←mul_right_inj' this, ←nat r.denom _ y, smul_smul, rat.cast_div],
  simp only [map_nat_cast, rat.cast_coe_nat, map_int_cast, rat.cast_coe_int, map_div₀],
  rw [←mul_assoc, mul_div_cancel' _ this, int_prop _ x, map_int_cast],
end

lemma continuous.inner_ {α : Type*} [topological_space α]
  {f : α → E} {g : α → E} (hf : continuous f) (hg : continuous g) :
  continuous (λ x, inner_ 𝕜 (f x) (g x)) :=
begin
  simp only [inner_],
  refine continuous_const.mul (continuous.sub (continuous.add (continuous.sub _ _) _) _),
  { refine continuous.mul _ _;
    { apply (continuous_algebra_map ℝ 𝕜).comp,
      apply continuous_norm.comp,
      apply continuous.add hf hg } },
  { refine continuous.mul _ _;
    { apply (continuous_algebra_map ℝ 𝕜).comp,
      apply continuous_norm.comp,
      apply continuous.sub hf hg } },
  { refine continuous.mul (continuous_const.mul _) _;
    { apply (continuous_algebra_map ℝ 𝕜).comp,
      apply continuous_norm.comp,
      refine continuous.add (hf.const_smul _) hg } },
  { refine continuous.mul (continuous_const.mul _) _;
    { apply (continuous_algebra_map ℝ 𝕜).comp,
      apply continuous_norm.comp,
      refine continuous.sub (hf.const_smul _) hg } },
end

lemma real_prop [inner_product_spaceable E] (r : ℝ) :
  inner_prop E (r : 𝕜) :=
begin
  intros x y,
  revert r,
  rw ←function.funext_iff,
  refine rat.dense_embedding_coe_real.dense.equalizer _ _ (funext $ λ X, _),
  { exact (continuous_of_real.smul continuous_const).inner_ continuous_const },
  { exact (continuous_conj.comp continuous_of_real).mul continuous_const },
  { simp only [function.comp_app, is_R_or_C.of_real_rat_cast, rat_prop _ _] }
end

lemma I_prop [inner_product_spaceable E] : inner_prop E (I : 𝕜) :=
begin
  by_cases hI : (I : 𝕜) = 0,
  { rw [hI, ←nat.cast_zero], exact nat_prop _  },
  intros x y,
  have hI' : (-I : 𝕜) * I = 1,
  { rw [←inv_I, inv_mul_cancel hI], },
  rw [conj_I, inner_, inner_, mul_left_comm],
  congr' 1,
  rw [smul_smul, I_mul_I_of_nonzero hI, neg_one_smul],
  rw [mul_sub, mul_add, mul_sub,
    mul_assoc I (𝓚 ‖I • x - y‖), ←mul_assoc (-I) I, hI', one_mul,
    mul_assoc I (𝓚 ‖I • x + y‖), ←mul_assoc (-I) I, hI', one_mul],
  have h₁ : ‖-x - y‖ = ‖x + y‖,
  { rw [←neg_add', norm_neg], },
  have h₂ : ‖-x + y‖ = ‖x - y‖,
  { rw [←neg_sub, norm_neg, sub_eq_neg_add], },
  rw [h₁, h₂],
  simp only [sub_eq_add_neg, mul_assoc],
  rw [←neg_mul_eq_neg_mul, ←neg_mul_eq_neg_mul],
  abel
end

lemma inner_prop [inner_product_spaceable E] (r : 𝕜) : inner_prop E r :=
begin
  intros x y,
  rw [←re_add_im r, add_smul, add_left, real_prop _ x, ←smul_smul, real_prop _ _ y, I_prop,
    map_add, map_mul, conj_of_real, conj_of_real, conj_I],
  ring,
end

lemma inner_.norm_sq (x : E) : ‖x‖ ^ 2 = re (inner_ 𝕜 x x) :=
begin
  simp only [inner_],
  have h₁ : norm_sq (4 : 𝕜) = 16,
  { have : ((4 : ℝ) : 𝕜) = (4 : 𝕜),
    { simp only [of_real_one, of_real_bit0] },
    rw [←this, norm_sq_eq_def', is_R_or_C.norm_eq_abs,
      is_R_or_C.abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)],
    norm_num },
  have h₂ : ‖x + x‖ = 2 * ‖x‖,
  { have : ‖(2 : 𝕜)‖ = 2,
    { rw [is_R_or_C.norm_eq_abs, is_R_or_C.abs_two] },
    rw [←this, ←norm_smul, two_smul] },
  simp only [inner, h₁, h₂, one_im, bit0_zero, add_zero, norm_zero, I_re, of_real_im,
    add_monoid_hom.map_add, bit0_im, zero_div, zero_mul, add_monoid_hom.map_neg, of_real_re,
    add_monoid_hom.map_sub, sub_zero, inv_re, one_re, inv_im, bit0_re, mul_re, mul_zero, sub_self,
    neg_zero, algebra_map_eq_of_real],
  ring,
end

lemma inner_.conj_symm (x y : E) : conj (inner_ 𝕜 y x) = inner_ 𝕜 x y :=
begin
  simp only [inner_],
  have h4 : conj (4⁻¹ : 𝕜) = 4⁻¹,
  { rw [is_R_or_C.conj_inv, ←of_real_one, ←of_real_bit0, ←of_real_bit0, conj_of_real] },
  rw [map_mul, h4],
  congr' 1,
  simp only [map_sub, map_add, algebra_map_eq_of_real, ←of_real_mul, conj_of_real, map_mul, conj_I],
  rw [add_comm y x, norm_sub_rev],
  by_cases hI : (I : 𝕜) = 0,
  { simp only [hI, neg_zero, zero_mul] },
  have h₁ : ‖(I : 𝕜) • y - x‖ = ‖(I : 𝕜) • x + y‖,
  { transitivity ‖(I : 𝕜) • ((I : 𝕜) • y - x)‖,
    { rw [norm_smul, norm_I_of_nonzero hI, one_mul] },
    { rw [smul_sub, smul_smul, I_mul_I_of_nonzero hI, neg_one_smul, ←neg_add', add_comm,
        norm_neg] } },
  have h₂ : ‖(I : 𝕜) • y + x‖ = ‖(I : 𝕜) • x - y‖,
  { transitivity ‖(I : 𝕜) • ((I : 𝕜) • y + x)‖,
    { rw [norm_smul, norm_I_of_nonzero hI, one_mul] },
    { rw [smul_add, smul_smul, I_mul_I_of_nonzero hI, neg_one_smul, ←neg_add_eq_sub]  }},
  rw [h₁, h₂, ←sub_add_eq_add_sub],
  simp only [neg_mul, sub_eq_add_neg, neg_neg],
end

end inner_product_spaceable

open inner_product_spaceable

/-- **Fréchet–von Neumann–Jordan Theorem**. A normed space `E` whose norm satisfies the
parallelogram identity can be given a compatible inner product. -/
noncomputable def inner_product_space.of_norm
  (h : ∀ x y : E, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) :
  inner_product_space 𝕜 E :=
begin
  haveI : inner_product_spaceable E := ⟨h⟩,
  exact
  { inner := inner_ 𝕜,
    norm_sq_eq_inner := inner_.norm_sq,
    conj_symm := inner_.conj_symm,
    add_left := add_left,
    smul_left := λ _ _ _, inner_prop _ _ _ }
end
