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

- http://www.mathematik.uni-muenchen.de/~michel/jordan-von_neumann_-_parallelogram_identity.pdf
- https://math.stackexchange.com/questions/21792/norms-induced-by-inner-products-and-the-parallelogram-law
- https://math.dartmouth.edu/archive/m113w10/public_html/jordan-vneumann-thm.pdf
-/

variables {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E] [normed_space 𝕜 E]

local notation `𝓚` := algebra_map ℝ 𝕜
open is_R_or_C
open_locale complex_conjugate

variables (𝕜)

/-- Auxiliary definition of the inner product derived from the norm. -/
private noncomputable def inner_ (x y : E) : 𝕜 :=
4⁻¹ * ((𝓚 ∥x + y∥) * (𝓚 ∥x + y∥) - (𝓚 ∥x - y∥) * (𝓚 ∥x - y∥)
          + (I:𝕜) * (𝓚 ∥(I:𝕜) • x + y∥) * (𝓚 ∥(I:𝕜) • x + y∥)
          - (I:𝕜) * (𝓚 ∥(I:𝕜) • x - y∥) * (𝓚 ∥(I:𝕜) • x - y∥))

variables {𝕜}

lemma inner_.add_left_aux1
  (h : ∀ x y : E, ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥))
  (x y z : E) :
  ∥x + y + z∥ * ∥x + y + z∥ =
    (∥2 • x + y∥ * ∥2 • x + y∥ + ∥2 • z + y∥ * ∥2 • z + y∥) / 2 - ∥x - z∥ * ∥x - z∥ :=
begin
  apply eq_sub_of_add_eq,
  rw [eq_div_iff (@_root_.two_ne_zero ℝ _ _), mul_comm _ (2 : ℝ)],
  symmetry,
  have h₀ := h (x + y + z) (x - z),
  convert h₀ using 4; { rw two_smul, abel }
end

lemma inner_.add_left_aux2
  (h : ∀ x y : E, ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥))
  (x y z : E) :
  ∥x + y - z∥ * ∥x + y - z∥ =
    (∥2 • x + y∥ * ∥2 • x + y∥ + ∥y - 2 • z∥ * ∥y - 2 • z∥) / 2 - ∥x + z∥ * ∥x + z∥ :=
begin
  apply eq_sub_of_add_eq,
  rw [eq_div_iff (@_root_.two_ne_zero ℝ _ _), mul_comm _ (2 : ℝ)],
  symmetry,
  have h₀ := h (x + y - z) (x + z),
  convert h₀ using 4; { rw two_smul, abel }
end

lemma inner_.add_left_aux2'
  (h : ∀ x y : E, ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥))
  (x y z : E) :
  ∥x + y + z∥ * ∥x + y + z∥ - ∥x + y - z∥ * ∥x + y - z∥ =
  ∥x + z∥ * ∥x + z∥ - ∥x - z∥ * ∥x - z∥ +
      (∥2 • z + y∥ * ∥2 • z + y∥ - ∥y - 2 • z∥ * ∥y - 2 • z∥) / 2 :=
begin
  rw [inner_.add_left_aux1 h, inner_.add_left_aux2 h],
  ring,
end

lemma inner_.add_left_aux3
  (h : ∀ x y : E, ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥))
  (y z : E) :
  ∥2 • z + y∥ * ∥2 • z + y∥ = 2 * (∥y + z∥ * ∥y + z∥ + ∥z∥ * ∥z∥) - ∥y∥ * ∥y∥ :=
begin
  apply eq_sub_of_add_eq,
  have h₀ := h (y + z) z,
  convert h₀ using 4; { try { rw two_smul }, abel }
end

lemma inner_.add_left_aux4
  (h : ∀ x y : E, ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥))
  (y z : E) :
  ∥y - 2 • z∥ * ∥y - 2 • z∥ = 2 * (∥y - z∥ * ∥y - z∥ + ∥z∥ * ∥z∥) - ∥y∥ * ∥y∥ :=
begin
  apply eq_sub_of_add_eq,
  have h₀ := h (y - z) z,
  conv_lhs at h₀ { rw add_comm },
  convert h₀ using 4; { try { rw two_smul }, abel }
end

lemma inner_.add_left_aux4'
  (h : ∀ x y : E, ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥))
  (y z : E) :
  (∥2 • z + y∥ * ∥2 • z + y∥ - ∥y - 2 • z∥ * ∥y - 2 • z∥) / 2 =
  (∥y + z∥ * ∥y + z∥) - (∥y - z∥ * ∥y - z∥) :=
begin
  rw [inner_.add_left_aux3 h, inner_.add_left_aux4 h],
  ring,
end

lemma inner_.add_left_aux5
  (h : ∀ x y : E, ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥))
  (x y z : E) :
  ∥(I : 𝕜) • (x + y) + z∥ * ∥(I : 𝕜) • (x + y) + z∥ =
    (∥(I : 𝕜) • (2 • x + y)∥ * ∥(I : 𝕜) • (2 • x + y)∥ +
      ∥(I : 𝕜) • y + 2 • z∥ * ∥(I : 𝕜) • y + 2 • z∥) / 2 -
    ∥(I : 𝕜) • x - z∥ * ∥(I : 𝕜) • x - z∥ :=
begin
  apply eq_sub_of_add_eq,
  rw [eq_div_iff (@_root_.two_ne_zero ℝ _ _), mul_comm _ (2 : ℝ)],
  symmetry,
  have h₀ := h ((I : 𝕜) • (x + y) + z) ((I : 𝕜) • x - z),
  convert h₀ using 4; { try { simp only [two_smul, smul_add] }, abel }
end

lemma inner_.add_left_aux6
  (h : ∀ x y : E, ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥))
  (x y z : E) :
  ∥(I : 𝕜) • (x + y) - z∥ * ∥(I : 𝕜) • (x + y) - z∥ =
    (∥(I : 𝕜) • (2 • x + y)∥ * ∥(I : 𝕜) • (2 • x + y)∥ +
      ∥(I : 𝕜) • y - 2 • z∥ * ∥(I : 𝕜) • y - 2 • z∥) / 2 -
    ∥(I : 𝕜) • x + z∥ * ∥(I : 𝕜) • x + z∥ :=
begin
  apply eq_sub_of_add_eq,
  rw [eq_div_iff (@_root_.two_ne_zero ℝ _ _), mul_comm _ (2 : ℝ)],
  symmetry,
  have h₀ := h ((I : 𝕜) • (x + y) - z) ((I : 𝕜) • x + z),
  convert h₀ using 4; { try { simp only [two_smul, smul_add] }, abel }
end

lemma inner_.add_left_aux7
  (h : ∀ x y : E, ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥))
  (y z : E) :
  ∥(I : 𝕜) • y + 2 • z∥ * ∥(I : 𝕜) • y + 2 • z∥ =
    2 * (∥(I : 𝕜) • y + z∥ * ∥(I : 𝕜) • y + z∥ + ∥z∥ * ∥z∥) -
    ∥(I : 𝕜) • y∥ * ∥(I : 𝕜) • y∥ :=
begin
  apply eq_sub_of_add_eq,
  have h₀ := h ((I : 𝕜) • y + z) z,
  convert h₀ using 4; { try { simp only [two_smul, smul_add] }, abel }
end

lemma inner_.add_left_aux8
  (h : ∀ x y : E, ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥))
  (y z : E) :
  ∥(I : 𝕜) • y - 2 • z∥ * ∥(I : 𝕜) • y - 2 • z∥ =
    2 * (∥(I : 𝕜) • y - z∥ * ∥(I : 𝕜) • y - z∥ + ∥z∥ * ∥z∥) -
    ∥(I : 𝕜) • y∥ * ∥(I : 𝕜) • y∥ :=
begin
  apply eq_sub_of_add_eq,
  have h₀ := h ((I : 𝕜) • y - z) z,
  rw add_comm,
  convert h₀ using 4; { try { simp only [two_smul, smul_add] }, abel }
end

lemma inner_.add_left
  (h : ∀ x y : E, ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥))
  (x y z : E) :
  inner_ 𝕜 (x + y) z = inner_ 𝕜 x z + inner_ 𝕜 y z :=
begin
  simp only [inner_],
  rw ←mul_add,
  congr,
  simp only [mul_assoc, ←map_mul, add_sub_assoc, ←mul_sub, ←map_sub],
  rw add_add_add_comm,
  simp only [←map_add, ←mul_add],
  congr,
  { rw [←add_sub_assoc, inner_.add_left_aux2' h, inner_.add_left_aux4' h] },
  { rw [inner_.add_left_aux5 h, inner_.add_left_aux6 h,
      inner_.add_left_aux7 h, inner_.add_left_aux8 h],
    simp only [map_sub, map_mul, map_add, div_eq_mul_inv],
    ring },
end

variables (𝕜 E)

/-- Auxiliary definition for the `add_left` property -/
private def inner_prop (r : 𝕜) : Prop := ∀ x y : E, inner_ 𝕜 (r • x) y = conj r * inner_ 𝕜 x y

variables {𝕜 E}

lemma inner_.nat
  (h : ∀ (x y : E), ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥))
  (r : ℕ) (x y : E) :
  inner_ 𝕜 ((r : 𝕜) • x) y = (r : 𝕜) * inner_ 𝕜 x y :=
begin
  induction r with r ih,
  { simp only [inner_, nat.nat_zero_eq_zero, zero_sub, nat.cast_zero, zero_mul, eq_self_iff_true,
      zero_smul, zero_add, mul_zero, sub_self, norm_neg, smul_zero], },
  { simp only [nat.cast_succ, add_smul, one_smul],
    rw [inner_.add_left h, ih, add_mul, one_mul] },
end

lemma inner_.nat_prop (r : ℕ)
  (h : ∀ (x y : E), ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥)) :
  inner_prop 𝕜 E r :=
begin
  intros x y,
  simp only [map_nat_cast],
  exact inner_.nat h r x y
end

lemma inner_.neg_one : inner_prop 𝕜 E (-1 : ℤ) :=
begin
  intros x y,
  simp only [inner_, neg_mul_eq_neg_mul, one_mul, int.cast_one, one_smul, ring_hom.map_one,
    map_neg, int.cast_neg, neg_smul, neg_one_mul],
  rw neg_mul_comm,
  congr' 1,
  have h₁ : ∥-x - y∥ = ∥x + y∥,
  { rw [←neg_add', norm_neg], },
  have h₂ : ∥-x + y∥ = ∥x - y∥,
  { rw [←neg_sub, norm_neg, sub_eq_neg_add], },
  have h₃ : ∥(I : 𝕜) • (-x) + y∥ = ∥(I : 𝕜) • x - y∥,
  { rw [←neg_sub, norm_neg, sub_eq_neg_add, ←smul_neg], },
  have h₄ : ∥(I : 𝕜) • (-x) - y∥ = ∥(I : 𝕜) • x + y∥,
  { rw [smul_neg, ←neg_add', norm_neg] },
  rw [h₁, h₂, h₃, h₄],
  ring,
end

lemma inner_.int_prop (r : ℤ)
  (h : ∀ (x y : E), ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥)) :
  inner_prop 𝕜 E r :=
begin
  intros x y,
  rw ←r.sign_mul_nat_abs,
  simp only [int.cast_coe_nat, map_nat_cast, map_int_cast, int.cast_mul, map_mul, mul_smul],
  obtain hr|rfl|hr := lt_trichotomy r 0,
  { rw [int.sign_eq_neg_one_of_neg hr, inner_.neg_one ((r.nat_abs : 𝕜) • x) y, inner_.nat h],
    simp only [map_neg, neg_mul, one_mul, mul_eq_mul_left_iff, true_or,
      int.nat_abs_eq_zero, eq_self_iff_true, int.cast_one, map_one, neg_inj, nat.cast_eq_zero,
      int.cast_neg] },
  { simp only [inner_, int.cast_zero, zero_sub, nat.cast_zero, zero_mul, eq_self_iff_true,
      int.sign_zero, zero_smul, zero_add, mul_zero, smul_zero, sub_self, norm_neg,
      int.nat_abs_zero] },
  { rw int.sign_eq_one_of_pos hr,
    simp only [one_mul, mul_eq_mul_left_iff, true_or, int.nat_abs_eq_zero, eq_self_iff_true,
      int.cast_one, one_smul, nat.cast_eq_zero, inner_.nat h] }
end

lemma inner_.rat_prop (r : ℚ)
  (h : ∀ (x y : E), ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥)) :
  inner_prop 𝕜 E r :=
begin
  intros x y,
  have : (r.denom : 𝕜) ≠ 0,
  { haveI : char_zero 𝕜 := is_R_or_C.char_zero_R_or_C,
    exact_mod_cast r.pos.ne' },
  rw [←r.num_div_denom, ←mul_right_inj' this, ←inner_.nat h r.denom, smul_smul, rat.cast_div],
  simp only [map_nat_cast, rat.cast_coe_nat, map_int_cast, rat.cast_coe_int, map_div₀],
  rw [←mul_assoc, mul_div_cancel' _ this, inner_.int_prop _ h, map_int_cast],
end

lemma inner_.continuous {α} [topological_space α] {f : α → E} {g : α → E}
  (hf : continuous f) (hg : continuous g) :
  continuous (λ x, inner_ 𝕜 (f x) (g x)) :=
begin
  simp only [inner_ ],
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

lemma inner_.real_prop (r : ℝ)
  (h : ∀ (x y : E), ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥)) :
  inner_prop 𝕜 E r :=
begin
  intros x y,
  revert r,
  rw ←function.funext_iff,
  refine rat.dense_embedding_coe_real.dense.equalizer _ _ _,
  { exact inner_.continuous (continuous_of_real.smul continuous_const) continuous_const },
  { exact (continuous_conj.comp continuous_of_real).mul
      (inner_.continuous continuous_const continuous_const) },
  funext X,
  simp only [function.comp_app, is_R_or_C.of_real_rat_cast, inner_.rat_prop _ h _ _],
end

lemma inner_.I_prop
  (h : ∀ (x y : E), ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥)) :
  inner_prop 𝕜 E (I : 𝕜 ) :=
begin
  by_cases hI : (I : 𝕜) = 0,
  { rw [hI, ←nat.cast_zero], apply inner_.nat_prop _ h },
  intros x y,
  have hI' : (-I : 𝕜) * I = 1,
  { rw [←inv_I, inv_mul_cancel hI], },
  rw [conj_I, inner_, inner_, mul_left_comm],
  congr' 1,
  rw [smul_smul, I_mul_I_of_nonzero hI, neg_one_smul],
  rw [mul_sub, mul_add, mul_sub,
    mul_assoc I (𝓚 ∥I • x - y∥), ←mul_assoc (-I) I, hI', one_mul,
    mul_assoc I (𝓚 ∥I • x + y∥), ←mul_assoc (-I) I, hI', one_mul],
  have h₁ : ∥-x - y∥ = ∥x + y∥,
  { rw [←neg_add', norm_neg], },
  have h₂ : ∥-x + y∥ = ∥x - y∥,
  { rw [←neg_sub, norm_neg, sub_eq_neg_add], },
  rw [h₁, h₂],
  simp only [sub_eq_add_neg, mul_assoc],
  rw [←neg_mul_eq_neg_mul, ←neg_mul_eq_neg_mul],
  abel
end

lemma inner_.smul_left
  (h : ∀ (x y : E), ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥))
  (x y : E) (r : 𝕜) :
  inner_ 𝕜 (r • x) y = conj r * inner_ 𝕜 x y :=
begin
  rw [←re_add_im r, add_smul, inner_.add_left h, inner_.real_prop _ h, ←smul_smul,
    inner_.real_prop _ h, inner_.I_prop h, map_add, map_mul, conj_of_real, conj_of_real, conj_I],
  ring,
end

lemma inner_.norm_sq (x : E) : ∥x∥ ^ 2 = re (inner_ 𝕜 x x) :=
begin
  simp only [inner_],
  have h₁ : norm_sq (4 : 𝕜) = 16,
  { have : ((4 : ℝ) : 𝕜) = (4 : 𝕜),
    { simp only [of_real_one, of_real_bit0] },
    rw [←this, norm_sq_eq_def', is_R_or_C.norm_eq_abs,
      is_R_or_C.abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)],
    norm_num },
  have h₂ : ∥x + x∥ = 2 * ∥x∥,
  { have : ∥(2 : 𝕜)∥ = 2,
    { rw [is_R_or_C.norm_eq_abs, is_R_or_C.abs_two] },
    rw [←this, ←norm_smul, two_smul] },
  simp only [inner, h₁, h₂, one_im, bit0_zero, add_zero, norm_zero, I_re, of_real_im,
    add_monoid_hom.map_add, bit0_im, zero_div, zero_mul, add_monoid_hom.map_neg, of_real_re,
    add_monoid_hom.map_sub, sub_zero, inv_re, one_re, inv_im, bit0_re, mul_re, mul_zero, sub_self,
    neg_zero, algebra_map_eq_of_real],
  ring,
end

lemma inner_.conj_sym (x y : E) : conj (inner_ 𝕜 y x) = inner_ 𝕜 x y :=
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
  have h₁ : ∥(I : 𝕜) • y - x∥ = ∥(I : 𝕜) • x + y∥,
  { transitivity ∥(I : 𝕜) • ((I : 𝕜) • y - x)∥,
    { rw [norm_smul, norm_I_of_nonzero hI, one_mul] },
    { rw [smul_sub, smul_smul, I_mul_I_of_nonzero hI, neg_one_smul, ←neg_add', add_comm,
        norm_neg] } },
  have h₂ : ∥(I : 𝕜) • y + x∥ = ∥(I : 𝕜) • x - y∥,
  { transitivity ∥(I : 𝕜) • ((I : 𝕜) • y + x)∥,
    { rw [norm_smul, norm_I_of_nonzero hI, one_mul] },
    { rw [smul_add, smul_smul, I_mul_I_of_nonzero hI, neg_one_smul, ←neg_add_eq_sub]  }},
  rw [h₁, h₂, ←sub_add_eq_add_sub],
  simp only [neg_mul, sub_eq_add_neg, neg_neg],
end

/-- Fréchet–von Neumann–Jordan theorm. A normed space `E` whose norm satisfies the parallelogram
identity can be given a compatible inner product. -/
noncomputable def inner_product_space.of_norm
  (h : ∀ x y : E, ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥)) :
  inner_product_space 𝕜 E :=
{ inner := inner_ 𝕜,
  norm_sq_eq_inner := inner_.norm_sq,
  conj_sym := inner_.conj_sym,
  add_left := inner_.add_left h,
  smul_left := inner_.smul_left h }
