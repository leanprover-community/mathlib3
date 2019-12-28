/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/

import analysis.calculus.local_extr

/-!
# The mean value inequality and equalities

In this file we prove the following facts:

* `convex.norm_image_sub_le_of_norm_deriv_le` : if `f` is differentaible on a convex set `s`
  and the norm of its derivative is bounded by `C`, then `f` is Lipschitz continuous on `s` with
  constant `C`.

* `convex.is_const_of_fderiv_within_eq_zero` : if a function has derivative `0` on a convex set `s`,
  then it is a constant on `s`.

* `exists_ratio_has_deriv_at_eq_ratio_slope` and `exists_ratio_deriv_eq_ratio_slope` :
  Cauchy's Mean Value Theorem.

* `exists_has_deriv_at_eq_slope` and `exists_deriv_eq_slope` : Lagrange's Mean Value Theorem.

* `convex.image_sub_lt_mul_sub_of_deriv_lt`, `convex.mul_sub_lt_image_sub_of_lt_deriv`,
  `convex.image_sub_le_mul_sub_of_deriv_le`, `convex.mul_sub_le_image_sub_of_le_deriv`,
  if `∀ x, C (</≤/>/≥) (f' x)`, then `C * (y - x) (</≤/>/≥) (f y - f x)` whenever `x < y`.

* `convex.mono_of_deriv_nonneg`, `convex.antimono_of_deriv_nonpos`,
  `convex.strict_mono_of_deriv_pos`, `convex.strict_antimono_of_deriv_neg` :
  if the derivative of a function is non-negative/non-positive/positive/negative, then
  the function is monotone/monotonically decreasing/strictly monotone/strictly monotonically
  decreasing.

* `convex_on_of_deriv_mono`, `convex_on_of_deriv2_nonneg` : if the derivative of a function
  is increasing or its second derivative is nonnegative, then the original function is convex.
-/

set_option class.instance_max_depth 120

variables {E : Type*} [normed_group E] [normed_space ℝ E]
          {F : Type*} [normed_group F] [normed_space ℝ F]

open metric set lattice asymptotics continuous_linear_map

/-! ### Vector-valued functions `f : E → F` -/

/-- The mean value theorem along a segment: a bound on the derivative of a function along a segment
implies a bound on the distance of the endpoints images -/
theorem norm_image_sub_le_of_norm_deriv_le_segment {f : ℝ → F} {C : ℝ}
  (hf : differentiable_on ℝ f (Icc 0 1))
  (bound : ∀t ∈ Icc (0:ℝ) 1, ∥deriv_within f (Icc 0 1) t∥ ≤ C) :
  ∥f 1 - f 0∥ ≤ C :=
begin
  /- Let D > C. We will show that, for all t ∈ [0,1], one has ∥f t - f 0∥ ≤ D * t. This is true
  for t=0. Let k be maximal in [0,1] for which this holds. By continuity of all functions, the
  maximum is realized. If k were <1, then a point x slightly to its right would satisfy
  ∥f x - f k∥ ≤ D * (k-x), since the differential of f at k has norm at most C < D. Therefore,
  the point x also satisfies ∥f x - f 0∥ ≤ D * x, contradicting the maximality of k. Hence, k = 1. -/
  refine le_of_forall_le_of_dense (λD hD, _),
  let K := {t ∈ Icc (0 : ℝ) 1 | ∥f t - f 0∥ ≤ D * t},
  let k := Sup K,
  have k_mem_K : k ∈ K,
  { refine cSup_mem_of_is_closed _ _ _,
    show K ≠ ∅,
    { have : (0 : ℝ) ∈ K, by simp [K, le_refl, zero_le_one],
      apply ne_empty_of_mem this },
    show bdd_above K, from ⟨1, λy hy, hy.1.2⟩,
    have A : continuous_on (λt:ℝ, (∥f t - f 0∥, D * t)) (Icc 0 1),
    { apply continuous_on.prod,
      { refine continuous_norm.comp_continuous_on _,
        apply continuous_on.sub hf.continuous_on continuous_on_const },
      { exact (continuous_const.mul continuous_id).continuous_on } },
    show is_closed K, from
      A.preimage_closed_of_closed is_closed_Icc (ordered_topology.is_closed_le' _) },
  have : k = 1,
  { by_contradiction k_ne_1,
    have k_lt_1 : k < 1 := lt_of_le_of_ne k_mem_K.1.2 k_ne_1,
    have : 0 ≤ k := k_mem_K.1.1,
    let g := deriv_within f (Icc 0 1) k,
    let h := λx, f x - f k - (x-k) • g,
    have : is_o (λ x, h x) (λ x, x - k) (nhds_within k (Icc 0 1)) :=
      (hf k k_mem_K.1).has_deriv_within_at,
    have : {x | ∥h x∥ ≤ (D-C) * ∥x-k∥} ∈ nhds_within k (Icc 0 1) :=
      this (D-C) (sub_pos_of_lt hD),
    rcases mem_nhds_within.1 this with ⟨s, s_open, ks, hs⟩,
    rcases is_open_iff.1 s_open k ks with ⟨ε, εpos, hε⟩,
    change 0 < ε at εpos,
    let δ := min ε (1-k),
    have δpos : 0 < δ, by simp [δ, εpos, k_lt_1],
    let x := k + δ/2,
    have k_lt_x : k < x, by { simp only [x], linarith },
    have x_lt_1 : x < 1 := calc
      x < k + δ : add_lt_add_left (half_lt_self δpos) _
      ... ≤ k + (1-k) : add_le_add_left (min_le_right _ _) _
      ... = 1 : by ring,
    have xε : x ∈ ball k ε,
    { simp [dist, x, abs_of_nonneg (le_of_lt (half_pos δpos))],
      exact lt_of_lt_of_le (half_lt_self δpos) (min_le_left _ _) },
    have xI : x ∈ Icc (0:ℝ) 1 :=
      ⟨le_of_lt (lt_of_le_of_lt (k_mem_K.1.1) k_lt_x), le_of_lt x_lt_1⟩,
    have Ih : ∥h x∥ ≤ (D - C) * ∥x - k∥ :=
      hs ⟨hε xε, xI⟩,
    have I : ∥f x - f k∥ ≤ D * (x-k) := calc
      ∥f x - f k∥ = ∥(x-k) • g + h x∥ : by { congr' 1, simp only [h], abel }
      ... ≤ ∥g∥ * ∥x-k∥ + (D-C) * ∥x-k∥ : norm_add_le_of_le (by rw [norm_smul, mul_comm]) Ih
      ... ≤ C * ∥x-k∥ + (D-C) * ∥x-k∥ :
        add_le_add_right (mul_le_mul_of_nonneg_right (bound k k_mem_K.1) (norm_nonneg _)) _
      ... = D * ∥x-k∥ : by ring
      ... = D * (x-k) : by simp [norm, abs_of_nonneg (le_of_lt (half_pos δpos))],
    have : ∥f x - f 0∥ ≤ D * x := calc
      ∥f x - f 0∥ = ∥(f x - f k) + (f k - f 0)∥ : by { congr' 1, abel }
      ... ≤ D * (x - k) + D * k : norm_add_le_of_le I (k_mem_K.2)
      ... = D * x : by ring,
    have xK : x ∈ K := ⟨xI, this⟩,
    have : x ≤ k := le_cSup ⟨1, λy hy, hy.1.2⟩ xK,
    exact (not_le_of_lt k_lt_x) this },
  rw this at k_mem_K,
  simpa [this] using k_mem_K.2
end

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by C, then
the function is C-Lipschitz -/
theorem convex.norm_image_sub_le_of_norm_deriv_le {f : E → F} {C : ℝ} {s : set E} {x y : E}
  (hf : differentiable_on ℝ f s) (bound : ∀x∈s, ∥fderiv_within ℝ f s x∥ ≤ C)
  (hs : convex s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x∥ ≤ C * ∥y - x∥ :=
begin
  /- By composition with t ↦ x + t • (y-x), we reduce to a statement for functions defined
  on [0,1], for which it is proved in `norm_image_sub_le_of_norm_deriv_le_segment`.
  We just have to check the differentiability of the composition and bounds on its derivative,
  which is straightforward but tedious for lack of automation. -/
  have C0 : 0 ≤ C := le_trans (norm_nonneg _) (bound x xs),
  let g := λ(t:ℝ), f (x + t • (y-x)),
  have D1 : differentiable ℝ (λt:ℝ, x + t • (y-x)) :=
    differentiable.add (differentiable_const _)
      (differentiable.smul' differentiable_id (differentiable_const _)),
  have segm : (λ (t : ℝ), x + t • (y - x)) '' Icc 0 1 ⊆ s,
    by { rw [← segment_eq_image_Icc_zero_one], apply convex_segment_iff.1 hs x y xs ys },
  have : f x = g 0, by { simp only [g], rw [zero_smul, add_zero] },
  rw this,
  have : f y = g 1, by { simp only [g], rw one_smul, congr' 1, abel },
  rw this,
  apply norm_image_sub_le_of_norm_deriv_le_segment
    (hf.comp D1.differentiable_on (image_subset_iff.1 segm)) (λt ht, _),
  /- It remains to check that the derivative of g is bounded by C ∥y-x∥ at any t ∈ [0,1] -/
  have t_s : x + t • (y-x) ∈ s := segm (mem_image_of_mem _ ht),
  /- Expand the derivative of the composition, and bound its norm by the product of the norms -/
  rw fderiv_within.comp_deriv_within t (hf _ t_s) ((D1 t).differentiable_within_at)
    (image_subset_iff.1 segm) (unique_diff_on_Icc_zero_one t ht),
  refine le_trans (le_op_norm _ _) (mul_le_mul (bound _ t_s) _ (norm_nonneg _) C0),
  have : deriv_within (λ (t : ℝ), x + t • (y - x)) (Icc 0 1) t = y - x := calc
    deriv_within (λ (t : ℝ), x + t • (y - x)) (Icc 0 1) t
    = deriv (λ (t : ℝ), x + t • (y - x)) t :
      differentiable_at.deriv_within (D1 t) (unique_diff_on_Icc_zero_one t ht)
    ... = deriv (λ (t : ℝ), x) t + deriv (λ (t : ℝ), t • (y-x)) t :
      deriv_add (differentiable_at_const _) ((differentiable.smul' differentiable_id (differentiable_const _)) t)
    ... = deriv (λ (t : ℝ), t • (y-x)) t :
      by rw [deriv_const, zero_add]
    ... = t • deriv (λ (t : ℝ), (y-x)) t + (deriv (@_root_.id ℝ) t) • (y - x) :
      deriv_smul' differentiable_at_id (differentiable_at_const _)
    ... = y - x :
      by rw [deriv_const, smul_zero, zero_add, deriv_id, one_smul],
  rw [this]
end

/-- If a function has zero Fréchet derivative at every point of a convex set,
then it is a constant on this set. -/
theorem convex.is_const_of_fderiv_within_eq_zero {s : set E} (hs : convex s)
  {f : E → F} (hf : differentiable_on ℝ f s) (hf' : ∀ x ∈ s, fderiv_within ℝ f s x = 0)
  {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
  f x = f y :=
have bound : ∀ x ∈ s, ∥fderiv_within ℝ f s x∥ ≤ 0,
  from λ x hx, by simp only [hf' x hx, _root_.norm_zero],
by simpa only [(dist_eq_norm _ _).symm, zero_mul, dist_le_zero, eq_comm]
  using hs.norm_image_sub_le_of_norm_deriv_le hf bound hx hy

/-! ### Functions `[a, b] → ℝ`. -/

section interval

-- Declare all variables here to make sure they come in a correct order
variables (f f' : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hfc : continuous_on f (Icc a b))
  (hff' : ∀ x ∈ Ioo a b, has_deriv_at f (f' x) x) (hfd : differentiable_on ℝ f (Ioo a b))
  (g g' : ℝ → ℝ) (hgc : continuous_on g (Icc a b)) (hgg' : ∀ x ∈ Ioo a b, has_deriv_at g (g' x) x)
  (hgd : differentiable_on ℝ g (Ioo a b))

include hab hfc hff' hgc hgg'

/-- Cauchy's Mean Value Theorem, `has_deriv_at` version. -/
lemma exists_ratio_has_deriv_at_eq_ratio_slope :
  ∃ c ∈ Ioo a b, (g b - g a) * f' c = (f b - f a) * g' c :=
begin
  let h := λ x, (g b - g a) * f x - (f b - f a) * g x,
  have hI : h a = h b,
  { simp only [h], ring },
  let h' := λ x, (g b - g a) * f' x - (f b - f a) * g' x,
  have hhh' : ∀ x ∈ Ioo a b, has_deriv_at h (h' x) x,
  { assume x hx,
    convert ((has_deriv_at_const x (g b - g a)).mul (hff' x hx)).sub
      ((has_deriv_at_const x (f b - f a)).mul (hgg' x hx)),
    simp only [h', mul_zero, add_zero] },
  have hhc : continuous_on h (Icc a b),
    from (continuous_on_const.mul hfc).sub (continuous_on_const.mul hgc),
  rcases exists_has_deriv_at_eq_zero h h' hab hhc hI hhh' with ⟨c, cmem, hc⟩,
  exact ⟨c, cmem, sub_eq_zero.1 hc⟩
end

omit hgc hgg'

/-- Lagrange's Mean Value Theorem, `has_deriv_at` version -/
lemma exists_has_deriv_at_eq_slope : ∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a) :=
begin
  rcases exists_ratio_has_deriv_at_eq_ratio_slope f f' hab hfc hff'
    id 1 continuous_id.continuous_on (λ x hx, has_deriv_at_id x) with ⟨c, cmem, hc⟩,
  use [c, cmem],
  simp only [_root_.id, pi.one_apply, mul_one] at hc,
  rw [← hc, mul_div_cancel_left],
  exact ne_of_gt (sub_pos.2 hab)
end

omit hff'

/-- Cauchy's Mean Value Theorem, `deriv` version. -/
lemma exists_ratio_deriv_eq_ratio_slope :
  ∃ c ∈ Ioo a b, (g b - g a) * (deriv f c) = (f b - f a) * (deriv g c) :=
exists_ratio_has_deriv_at_eq_ratio_slope f (deriv f) hab hfc
  (λ x hx, ((hfd x hx).differentiable_at $ mem_nhds_sets is_open_Ioo hx).has_deriv_at)
  g (deriv g) hgc (λ x hx, ((hgd x hx).differentiable_at $ mem_nhds_sets is_open_Ioo hx).has_deriv_at)

/-- Lagrange's Mean Value Theorem, `deriv` version. -/
lemma exists_deriv_eq_slope : ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
exists_has_deriv_at_eq_slope f (deriv f) hab hfc
  (λ x hx, ((hfd x hx).differentiable_at $ mem_nhds_sets is_open_Ioo hx).has_deriv_at)

end interval

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `C < f'`, then
`f` grows faster than `C * x` on `D`, i.e., `C * (y - x) < f y - f x` whenever `x, y ∈ D`,
`x < y`. -/
theorem convex.mul_sub_lt_image_sub_of_lt_deriv {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  {C} (hf'_gt : ∀ x ∈ interior D, C < deriv f x) :
  ∀ x y ∈ D, x < y → C * (y - x) < f y - f x :=
begin
  assume x y hx hy hxy,
  have hxyD : Icc x y ⊆ D, from convex_real_iff.1 hD hx hy,
  have hxyD' : Ioo x y ⊆ interior D,
    from subset_sUnion_of_mem ⟨is_open_Ioo, subset.trans Ioo_subset_Icc_self hxyD⟩,
  obtain ⟨a, a_mem, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x),
    from exists_deriv_eq_slope f hxy (hf.mono hxyD) (hf'.mono hxyD'),
  have : C < (f y - f x) / (y - x), by { rw [← ha], exact hf'_gt _ (hxyD' a_mem) },
  exact (lt_div_iff (sub_pos.2 hxy)).1 this
end

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `C ≤ f'`, then
`f` grows at least as fast as `C * x` on `D`, i.e., `C * (y - x) ≤ f y - f x` whenever `x, y ∈ D`,
`x ≤ y`. -/
theorem convex.mul_sub_le_image_sub_of_le_deriv {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  {C} (hf'_ge : ∀ x ∈ interior D, C ≤ deriv f x) :
  ∀ x y ∈ D, x ≤ y → C * (y - x) ≤ f y - f x :=
begin
  assume x y hx hy hxy,
  cases eq_or_lt_of_le hxy with hxy' hxy', by rw [hxy', sub_self, sub_self, mul_zero],
  have hxyD : Icc x y ⊆ D, from convex_real_iff.1 hD hx hy,
  have hxyD' : Ioo x y ⊆ interior D,
    from subset_sUnion_of_mem ⟨is_open_Ioo, subset.trans Ioo_subset_Icc_self hxyD⟩,
  obtain ⟨a, a_mem, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x),
    from exists_deriv_eq_slope f hxy' (hf.mono hxyD) (hf'.mono hxyD'),
  have : C ≤ (f y - f x) / (y - x), by { rw [← ha], exact hf'_ge _ (hxyD' a_mem) },
  exact (le_div_iff (sub_pos.2 hxy')).1 this
end

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f' C C`, then
`f` grows slower than `C * x` on `D`, i.e., `f y - f x < C * (y - x)` whenever `x, y ∈ D`,
`x < y`. -/
theorem convex.image_sub_lt_mul_sub_of_deriv_lt {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  {C} (lt_hf' : ∀ x ∈ interior D, deriv f x < C) :
  ∀ x y ∈ D, x < y → f y - f x < C * (y - x) :=
begin
  assume x y hx hy hxy,
  have hf'_gt : ∀ x ∈ interior D, -C < deriv (λ y, -f y) x,
  { assume x hx,
    rw [deriv_neg, neg_lt_neg_iff],
    exact lt_hf' x hx },
  simpa [-neg_lt_neg_iff]
    using neg_lt_neg (hD.mul_sub_lt_image_sub_of_lt_deriv hf.neg hf'.neg hf'_gt x y hx hy hxy)
end

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f' ≤ C`, then
`f` grows at most as fast as `C * x` on `D`, i.e., `f y - f x ≤ C * (y - x)` whenever `x, y ∈ D`,
`x ≤ y`. -/
theorem convex.image_sub_le_mul_sub_of_deriv_le {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  {C} (le_hf' : ∀ x ∈ interior D, deriv f x ≤ C) :
  ∀ x y ∈ D, x ≤ y → f y - f x ≤ C * (y - x) :=
begin
  assume x y hx hy hxy,
  have hf'_ge : ∀ x ∈ interior D, -C ≤ deriv (λ y, -f y) x,
  { assume x hx,
    rw [deriv_neg, neg_le_neg_iff],
    exact le_hf' x hx },
  simpa [-neg_le_neg_iff]
    using neg_le_neg (hD.mul_sub_le_image_sub_of_le_deriv hf.neg hf'.neg hf'_ge x y hx hy hxy)
end

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is positive, then
`f` is a strictly monotonically increasing function on `D`. -/
theorem convex.strict_mono_of_deriv_pos {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  (hf'_pos : ∀ x ∈ interior D, 0 < deriv f x) :
  ∀ x y ∈ D, x < y → f x < f y :=
by simpa only [zero_mul, sub_pos] using hD.mul_sub_lt_image_sub_of_lt_deriv hf hf' hf'_pos

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is nonnegative, then
`f` is a monotonically increasing function on `D`. -/
theorem convex.mono_of_deriv_nonneg {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  (hf'_nonneg : ∀ x ∈ interior D, 0 ≤ deriv f x) :
  ∀ x y ∈ D, x ≤ y → f x ≤ f y :=
by simpa only [zero_mul, sub_nonneg] using hD.mul_sub_le_image_sub_of_le_deriv hf hf' hf'_nonneg

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is negative, then
`f` is a strictly monotonically decreasing function on `D`. -/
theorem convex.strict_antimono_of_deriv_neg {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  (hf'_neg : ∀ x ∈ interior D, deriv f x < 0) :
  ∀ x y ∈ D, x < y → f y < f x :=
by simpa only [zero_mul, sub_lt_zero] using hD.image_sub_lt_mul_sub_of_deriv_lt hf hf' hf'_neg

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is nonpositive, then
`f` is a monotonically decreasing function on `D`. -/
theorem convex.antimono_of_deriv_nonpos {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  (hf'_nonpos : ∀ x ∈ interior D, deriv f x ≤ 0) :
  ∀ x y ∈ D, x ≤ y → f y ≤ f x :=
by simpa only [zero_mul, sub_nonpos] using hD.image_sub_le_mul_sub_of_deriv_le hf hf' hf'_nonpos

theorem convex_on_of_deriv_mono {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  (hf'_mono : ∀ x y ∈ interior D, x ≤ y → deriv f x ≤ deriv f y) :
  convex_on D f :=
convex_on_real_of_slope_mono_adjacent hD
begin
  intros x y z hx hz hxy hyz,
  -- First we prove some trivial inclusions
  have hxzD : Icc x z ⊆ D, from convex_real_iff.1 hD hx hz,
  have hxyD : Icc x y ⊆ D, from subset.trans (Icc_subset_Icc_right $ le_of_lt hyz) hxzD,
  have hxyD' : Ioo x y ⊆ interior D,
    from subset_sUnion_of_mem ⟨is_open_Ioo, subset.trans Ioo_subset_Icc_self hxyD⟩,
  have hyzD : Icc y z ⊆ D, from subset.trans (Icc_subset_Icc_left $ le_of_lt hxy) hxzD,
  have hyzD' : Ioo y z ⊆ interior D,
    from subset_sUnion_of_mem ⟨is_open_Ioo, subset.trans Ioo_subset_Icc_self hyzD⟩,
  -- Then we apply MVT to both `[x, y]` and `[y, z]`
  obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x),
    from exists_deriv_eq_slope f hxy (hf.mono hxyD) (hf'.mono hxyD'),
  obtain ⟨b, ⟨hyb, hbz⟩, hb⟩ : ∃ b ∈ Ioo y z, deriv f b = (f z - f y) / (z - y),
    from exists_deriv_eq_slope f hyz (hf.mono hyzD) (hf'.mono hyzD'),
  rw [← ha, ← hb],
  exact hf'_mono a b (hxyD' ⟨hxa, hay⟩) (hyzD' ⟨hyb, hbz⟩) (le_of_lt $ lt_trans hay hyb)
end

theorem convex_on_of_deriv2_nonneg {D : set ℝ} (hD : convex D) {f : ℝ → ℝ}
  (hf : continuous_on f D) (hf' : differentiable_on ℝ f (interior D))
  (hf'' : differentiable_on ℝ (deriv f) (interior D))
  (hf''_nonneg : ∀ x ∈ interior D, 0 ≤ (deriv^[2] f x)) :
  convex_on D f :=
convex_on_of_deriv_mono hD hf hf' $
assume x y hx hy hxy,
hD.interior.mono_of_deriv_nonneg hf''.continuous_on (by rwa [interior_interior])
  (by rwa [interior_interior]) _ _ hx hy hxy
