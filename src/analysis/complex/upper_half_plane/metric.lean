import analysis.complex.upper_half_plane
import analysis.special_functions.arsinh
import geometry.euclidean.inversion

/-!
-/

noncomputable theory

open_locale upper_half_plane complex_conjugate nnreal topological_space
open set metric filter real

variables {z w : ℍ} {r R : ℝ}

namespace upper_half_plane

instance : has_dist ℍ :=
⟨λ z w, 2 * arsinh (dist (z : ℂ) w / (2 * sqrt (z.im * w.im)))⟩

lemma dist_eq (z w : ℍ) : dist z w = 2 * arsinh (dist (z : ℂ) w / (2 * sqrt (z.im * w.im))) :=
rfl

lemma sinh_half_dist (z w : ℍ) :
  sinh (dist z w / 2) = dist (z : ℂ) w / (2 * sqrt (z.im * w.im)) :=
by rw [dist_eq, mul_div_cancel_left (arsinh _) two_ne_zero, sinh_arsinh]

lemma cosh_half_dist (z w : ℍ) :
  cosh (dist z w / 2) = dist (z : ℂ) (conj (w : ℂ)) / (2 * sqrt (z.im * w.im)) :=
begin
  have H₁ : (2 ^ 2 : ℝ) = 4, by norm_num1,
  have H₂ : 0 < z.im * w.im, from mul_pos z.im_pos w.im_pos,
  have H₃ : 0 < 2 * sqrt (z.im * w.im), from mul_pos two_pos (sqrt_pos.2 H₂),
  rw [← sq_eq_sq (cosh_pos _).le (div_nonneg dist_nonneg H₃.le), cosh_sq', sinh_half_dist, div_pow,
    div_pow, one_add_div (pow_ne_zero 2 H₃.ne'), mul_pow, sq_sqrt H₂.le, H₁],
  congr' 1,
  simp only [complex.dist_eq, complex.sq_abs, complex.norm_sq_sub, complex.norm_sq_conj,
    complex.conj_conj, complex.mul_re, complex.conj_re, complex.conj_im, coe_im],
  ring
end

lemma exp_half_dist (z w : ℍ) :
  exp (dist z w / 2) = (dist (z : ℂ) w + dist (z : ℂ) (conj ↑w)) / (2 * sqrt (z.im * w.im)) :=
by rw [← sinh_add_cosh, sinh_half_dist, cosh_half_dist, add_div]

lemma cosh_dist (z w : ℍ) : cosh (dist z w) = 1 + dist (z : ℂ) w ^ 2 / (2 * z.im * w.im) :=
by rw [dist_eq, cosh_two_mul, cosh_sq', add_assoc, ← two_mul, sinh_arsinh, div_pow, mul_pow,
  sq_sqrt (mul_pos z.im_pos w.im_pos).le, sq (2 : ℝ), mul_assoc, ← mul_div_assoc,
  mul_assoc, mul_div_mul_left _ _ (@two_ne_zero ℝ _ _)]

lemma sinh_half_dist_add_dist (a b c : ℍ) :
  sinh ((dist a b + dist b c) / 2) =
    (dist (a : ℂ) b * dist (c : ℂ) (conj ↑b) + dist (b : ℂ) c * dist (a : ℂ) (conj ↑b)) /
      (2 * sqrt (a.im * c.im) * dist (b : ℂ) (conj ↑b)) :=
begin
  simp only [add_div _ _ (2 : ℝ), sinh_add, sinh_half_dist, cosh_half_dist, div_mul_div_comm],
  rw [← add_div, complex.dist_self_conj, coe_im, abs_of_pos b.im_pos, mul_comm (dist ↑b _),
    dist_comm (b : ℂ), complex.dist_conj_comm, mul_mul_mul_comm, mul_mul_mul_comm _ _ _ b.im],
  congr' 2,
  rw [sqrt_mul, sqrt_mul, sqrt_mul, mul_comm (sqrt a.im), mul_mul_mul_comm, mul_self_sqrt,
    mul_comm]; exact (im_pos _).le
end

protected lemma dist_comm (z w : ℍ) : dist z w = dist w z :=
by simp only [dist_eq, dist_comm (z : ℂ), mul_comm]

lemma dist_le_iff_le_sinh :
  dist z w ≤ r ↔ dist (z : ℂ) w / (2 * sqrt (z.im * w.im)) ≤ sinh (r / 2) :=
by rw [← div_le_div_right (@two_pos ℝ _ _), ← sinh_le_sinh, sinh_half_dist]

lemma dist_eq_iff_eq_sinh :
  dist z w = r ↔ dist (z : ℂ) w / (2 * sqrt (z.im * w.im)) = sinh (r / 2) :=
by rw [← div_left_inj' (@two_ne_zero ℝ _ _), ← sinh_inj, sinh_half_dist]

lemma dist_eq_iff_eq_sq_sinh (hr : 0 ≤ r) :
  dist z w = r ↔ dist (z : ℂ) w ^ 2 / (4 * z.im * w.im) = sinh (r / 2) ^ 2 :=
begin
  rw [dist_eq_iff_eq_sinh, ← sq_eq_sq, div_pow, mul_pow, sq_sqrt, mul_assoc],
  { norm_num },
  { exact (mul_pos z.im_pos w.im_pos).le },
  { exact div_nonneg dist_nonneg (mul_nonneg zero_le_two $ sqrt_nonneg _) },
  { exact sinh_nonneg_iff.2 (div_nonneg hr zero_le_two) }
end

protected lemma dist_triangle (a b c : ℍ) : dist a c ≤ dist a b + dist b c :=
begin
  rw [dist_le_iff_le_sinh, sinh_half_dist_add_dist,
    div_mul_eq_div_div _ _ (dist _ _), le_div_iff, div_mul_eq_mul_div],
  { exact div_le_div_of_le (mul_nonneg zero_le_two (sqrt_nonneg _))
      (euclidean_geometry.mul_dist_le_mul_dist_add_mul_dist (a : ℂ) b c (conj ↑b)) },
  { rw [dist_comm, dist_pos, ne.def, complex.eq_conj_iff_im],
    exact b.im_ne_zero }
end

lemma dist_le_dist_coe_div_sqrt (z w : ℍ) :
  dist z w ≤ dist (z : ℂ) w / sqrt (z.im * w.im) :=
begin
  rw [dist_le_iff_le_sinh, ← div_mul_eq_div_div_swap, self_le_sinh_iff],
  exact div_nonneg dist_nonneg (mul_nonneg zero_le_two (sqrt_nonneg _))
end

def metric_space_aux : metric_space ℍ :=
{ dist := dist,
  dist_self := λ z, by rw [dist_eq, dist_self, zero_div, arsinh_zero, mul_zero],
  dist_comm := upper_half_plane.dist_comm,
  dist_triangle := upper_half_plane.dist_triangle,
  eq_of_dist_eq_zero := λ z w h,
    by simpa [dist_eq, real.sqrt_eq_zero', (mul_pos z.im_pos w.im_pos).not_le, subtype.coe_inj]
      using h }

open complex

lemma cosh_dist' (z w : ℍ) :
  real.cosh (dist z w) = ((z.re - w.re) ^ 2 + z.im ^ 2 + w.im ^ 2) / (2 * z.im * w.im) :=
have H : 0 < 2 * z.im * w.im, from mul_pos (mul_pos two_pos z.im_pos) w.im_pos,
by { field_simp [cosh_dist, complex.dist_eq, complex.sq_abs, norm_sq_apply, H, H.ne'], ring }

lemma cmp_dist_eq_cmp_dist_coe (z w : ℍ) (r : ℝ) :
  cmp (dist z w) r = cmp (dist (z : ℂ) ⟨w.re, w.im * real.cosh r⟩) (w.im * sinh r) :=
begin
  letI := metric_space_aux,
  cases lt_or_le r 0 with hr₀ hr₀,
  { transitivity ordering.gt,
    exacts [(hr₀.trans_le dist_nonneg).cmp_eq_gt,
      ((mul_neg_of_pos_of_neg w.im_pos (sinh_neg_iff.2 hr₀)).trans_le
        dist_nonneg).cmp_eq_gt.symm] },
  have hr₀' : 0 ≤ w.im * sinh r, from mul_nonneg w.im_pos.le (sinh_nonneg_iff.2 hr₀),
  have hzw₀ : 0 < 2 * z.im * w.im, from mul_pos (mul_pos two_pos z.im_pos) w.im_pos,
  calc cmp (dist z w) r
      = cmp (((z.re - w.re) ^ 2 + z.im ^ 2 + w.im ^ 2) / (2 * z.im * w.im)) (cosh r) :
    by rw [← cosh_dist' z w, cosh_strict_mono_on.cmp_map_eq dist_nonneg hr₀]
  ... = cmp ((z.re - w.re) ^ 2 + z.im ^ 2 + w.im ^ 2) (2 * z.im * w.im * cosh r) :
    by rw [← cmp_mul_pos_left hzw₀, mul_div_cancel' _ hzw₀.ne']
  ... = cmp ((z.re - w.re) ^ 2 + (z.im - w.im * cosh r) ^ 2 - (w.im * sinh r) ^ 2) 0 :
    by { rw [← cmp_sub_zero, sub_sq _ (_ * _), mul_pow, real.cosh_sq], congr' 1, ring }
  ... = cmp (dist (z : ℂ) ⟨w.re, w.im * real.cosh r⟩ ^ 2) ((w.im * sinh r) ^ 2) :
    by simp only [cmp_sub_zero, complex.dist_eq, complex.sq_abs, norm_sq_apply, ← sq,
      sub_re, sub_im, coe_re, coe_im]
  ... = cmp (dist (z : ℂ) ⟨w.re, w.im * real.cosh r⟩) (w.im * sinh r) :
    (@strict_mono_on_pow ℝ _ _ two_pos).cmp_map_eq dist_nonneg hr₀'
end

lemma dist_eq_iff_dist_coe_eq :
  dist z w = r ↔ dist (z : ℂ) ⟨w.re, w.im * real.cosh r⟩ = w.im * real.sinh r :=
eq_iff_eq_of_cmp_eq_cmp (cmp_dist_eq_cmp_dist_coe z w r)

protected lemma dist_centers (z : ℍ) (r : ℝ) :
  dist (z : ℂ) ⟨z.re, z.im * cosh r⟩ = z.im * (cosh r - 1) :=
calc dist (z : ℂ)  ⟨z.re, z.im * cosh r⟩ = dist z.im (z.im * cosh r) : complex.dist_of_re_eq rfl
... =  z.im * (cosh r - 1) :
  begin
    rw [dist_comm, real.dist_eq, mul_sub, mul_one],
    exact abs_of_nonneg (sub_nonneg.2 $ le_mul_of_one_le_right z.im_pos.le (one_le_cosh _))
  end

protected lemma dist_center (z w : ℍ) :
  dist (z : ℂ) ⟨w.re, w.im * real.cosh (dist z w)⟩ = w.im * real.sinh (dist z w) :=
dist_eq_iff_dist_coe_eq.1 rfl

lemma dist_lt_iff_dist_coe_lt :
  dist z w < r ↔ dist (z : ℂ) ⟨w.re, w.im * real.cosh r⟩ < w.im * real.sinh r :=
lt_iff_lt_of_cmp_eq_cmp (cmp_dist_eq_cmp_dist_coe z w r)

lemma lt_dist_iff_lt_dist_coe :
  r < dist z w ↔ w.im * real.sinh r < dist (z : ℂ) ⟨w.re, w.im * real.cosh r⟩ :=
lt_iff_lt_of_cmp_eq_cmp (cmp_eq_cmp_symm.1 $ cmp_dist_eq_cmp_dist_coe z w r)

lemma dist_le_iff_dist_coe_le :
  dist z w ≤ r ↔ dist (z : ℂ) ⟨w.re, w.im * real.cosh r⟩ ≤ w.im * real.sinh r :=
le_iff_le_of_cmp_eq_cmp (cmp_dist_eq_cmp_dist_coe z w r)

lemma le_dist_iff_le_dist_coe :
  r < dist z w ↔ w.im * real.sinh r < dist (z : ℂ) ⟨w.re, w.im * real.cosh r⟩ :=
lt_iff_lt_of_cmp_eq_cmp (cmp_eq_cmp_symm.1 $ cmp_dist_eq_cmp_dist_coe z w r)

/-- For two points on the same vertical line, the distance is equal to the distance between the
logarithms of their imaginary parts. -/
lemma dist_of_re_eq (h : z.re = w.re) : dist z w = dist (log z.im) (log w.im) :=
begin
  have h₀ : 0 < z.im / w.im, from div_pos z.im_pos w.im_pos,
  rw [dist_eq_iff_dist_coe_eq, real.dist_eq, ← abs_sinh, cosh_abs,
    ← log_div z.im_ne_zero w.im_ne_zero, sinh_log h₀, cosh_log h₀, inv_div, dist_of_re_eq];
    [skip, exact h],
  nth_rewrite 3 [← abs_of_pos w.im_pos],
  simp only [← _root_.abs_mul, coe_im, real.dist_eq],
  congr' 1,
  field_simp [z.im_pos, w.im_pos, z.im_ne_zero, w.im_ne_zero],
  ring
end

lemma dist_log_im_le (z w : ℍ) : dist (log z.im) (log w.im) ≤ dist z w :=
calc dist (log z.im) (log w.im) = @dist ℍ _ ⟨⟨0, z.im⟩, z.im_pos⟩ ⟨⟨0, w.im⟩, w.im_pos⟩ :
  eq.symm $ @dist_of_re_eq ⟨⟨0, z.im⟩, z.im_pos⟩ ⟨⟨0, w.im⟩, w.im_pos⟩ rfl
... ≤ dist z w :
  mul_le_mul_of_nonneg_left (arsinh_le_arsinh.2 $ div_le_div_of_le
    (mul_nonneg zero_le_two (sqrt_nonneg _)) $
      by simpa [sqrt_sq_eq_abs] using complex.abs_im_le_abs (z - w)) zero_le_two

lemma im_le_im_mul_exp_dist (z w : ℍ) : z.im ≤ w.im * exp (dist z w) :=
begin
  rw [← div_le_iff' w.im_pos, ← exp_log z.im_pos, ← exp_log w.im_pos, ← real.exp_sub, exp_le_exp],
  exact (le_abs_self _).trans (dist_log_im_le z w)
end

lemma im_div_exp_dist_le (z w : ℍ) : z.im / exp (dist z w) ≤ w.im :=
(div_le_iff (exp_pos _)).2 (im_le_im_mul_exp_dist z w)

/-- An upper estimate on the complex distance between two points in terms of the hyperbolic distance
and the imaginary part of one of the points. -/
lemma dist_coe_le (z w : ℍ) : dist (z : ℂ) w ≤ w.im * (exp (dist z w) - 1) :=
calc dist (z : ℂ) w
    ≤ dist (z : ℂ) ⟨w.re, w.im * cosh (dist z w)⟩ + dist (w : ℂ) ⟨w.re, w.im * cosh (dist z w)⟩ :
  dist_triangle_right _ _ _
... = w.im * sinh (dist z w) + w.im * (cosh (dist z w) - 1) :
  congr_arg2 (+) (z.dist_center w) (w.dist_centers _)
... = w.im  * (exp (dist z w) - 1) :
  by rw [← mul_add, ← add_sub_assoc, real.sinh_add_cosh]

/-- An upper estimate on the complex distance between two points in terms of the hyperbolic distance
and the imaginary part of one of the points. -/
lemma le_dist_coe (z w : ℍ) : w.im * (1 - exp (-dist z w)) ≤ dist (z : ℂ) w :=
calc w.im * (1 - exp (-dist z w)) = w.im * sinh (dist z w) - w.im * (cosh (dist z w) - 1) :
  by { rw [sub_eq_neg_add, ← real.sinh_sub_cosh], ring }
... = dist (z : ℂ) ⟨w.re, w.im * cosh (dist z w)⟩ - dist (w : ℂ) ⟨w.re, w.im * cosh (dist z w)⟩ :
  congr_arg2 _ (z.dist_center w).symm (w.dist_centers _).symm
... ≤ dist (z : ℂ) w : sub_le_iff_le_add.2 $ dist_triangle _ _ _

/-- The hyperbolic metric on the upper half plane. -/
instance : metric_space ℍ := metric_space_aux.replace_topology $
begin
  refine le_antisymm (continuous_id_iff_le.1 _) _,
  { refine (@continuous_iff_continuous_dist _ _ metric_space_aux.to_pseudo_metric_space _ _).2 _,
    have : ∀ (x : ℍ × ℍ), 2 * real.sqrt (x.1.im * x.2.im) ≠ 0,
      from λ x, mul_ne_zero two_ne_zero (real.sqrt_pos.2 $ mul_pos x.1.im_pos x.2.im_pos).ne',
    -- `continuity` fails to apply `continuous.div`
    apply_rules [continuous.div, continuous.mul, continuous_const, continuous.arsinh,
      continuous.dist, continuous_coe.comp, continuous_fst, continuous_snd,
      real.continuous_sqrt.comp, continuous_im.comp] },
  { letI : metric_space ℍ := metric_space_aux,
    refine le_of_nhds_le_nhds (λ z, _),
    rw [nhds_induced],
    refine (nhds_basis_ball.le_basis_iff (nhds_basis_ball.comap _)).2 (λ R hR, _),
    have h₁ : 1 < R / im z + 1, from lt_add_of_pos_left _ (div_pos hR z.im_pos),
    have h₀ : 0 < R / im z + 1, from one_pos.trans h₁,
    refine ⟨log (R / im z + 1), real.log_pos h₁, _⟩,
    refine λ w hw, (dist_coe_le w z).trans_lt _,
    rwa [← lt_div_iff' z.im_pos, sub_lt_iff_lt_add, ← real.lt_log_iff_exp_lt h₀] }
end

end upper_half_plane
