import analysis.complex.upper_half_plane
import analysis.special_functions.arsinh
import geometry.euclidean.inversion

/-!
-/

noncomputable theory

open_locale upper_half_plane complex_conjugate nnreal topological_space
open metric filter

variables {z w : ℍ} {r R : ℝ}

namespace upper_half_plane

section real

open real

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

#check strict_mono

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

/-- For two points on the same vertical line, the distance is equal to the distance between the
logarithms of their imaginary parts. -/
lemma dist_of_re_eq (h : z.re = w.re) : dist z w = dist (log z.im) (log w.im) :=
begin
  rw [dist_eq_iff_eq_sq_sinh dist_nonneg, complex.dist_of_re_eq h, sinh_sq'''',
    mul_div_cancel' (dist _ _) two_ne_zero, real.dist_eq, _root_.sq_abs, real.dist_eq,
    cosh_abs, ← log_div z.im_ne_zero w.im_ne_zero, cosh_log (div_pos z.im_pos w.im_pos), inv_div,
    div_add_div _ _ w.im_ne_zero z.im_ne_zero, ← div_mul_eq_div_div_swap, div_sub_one,
    ← div_mul_eq_div_div_swap, coe_im, coe_im, sub_sq, sq, sq],
  { congr' 1; ring },
  { exact mul_ne_zero two_ne_zero (mul_ne_zero w.im_ne_zero z.im_ne_zero) }
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
  rw [← div_le_iff' w.im_pos, ← exp_log z.im_pos, ← exp_log w.im_pos, ← exp_sub, exp_le_exp],
  exact (le_abs_self _).trans (dist_log_im_le z w)
end

lemma im_div_exp_dist_le (z w : ℍ) : z.im / exp (dist z w) ≤ w.im :=
(div_le_iff (exp_pos _)).2 (im_le_im_mul_exp_dist z w)


end real

open real (sinh arsinh log) complex

def metric_space_aux : metric_space ℍ :=
{ dist := dist,
  dist_self := λ z, by rw [dist_of_re_eq rfl, dist_self],
  dist_comm := upper_half_plane.dist_comm,
  dist_triangle := upper_half_plane.dist_triangle,
  eq_of_dist_eq_zero := λ z w h,
    by simpa [dist_eq, real.sqrt_eq_zero', (mul_pos z.im_pos w.im_pos).not_le, subtype.coe_inj]
      using h }

lemma dist_eq_iff_complex_dist_eq {z w : ℍ} {r : ℝ} :
  dist z w = r ↔ dist (z.re + z.im * real.cosh r * I : ℂ) w = z.im * real.sinh r :=
begin
  letI := metric_space_aux,
  cases lt_or_le r 0 with hr₀ hr₀,
  { split,
    { rintro rfl,
      exact absurd hr₀ dist_nonneg.not_lt },
    { intro H,
      exact absurd (dist_nonneg.trans_eq H)
        (mul_neg_of_pos_of_neg z.im_pos (real.sinh_neg_iff.2 hr₀)).not_le } },
  rw [dist_eq_iff_eq_sq_sinh hr₀],
end

instance : metric_space ℍ := metric_space_aux.replace_topology $
begin
  -- letI : metric_space ℍ := metric_space_aux,
  refine le_antisymm (continuous_id_iff_le.1 _) _,
  { refine (@continuous_iff_continuous_dist _ _ metric_space_aux.to_pseudo_metric_space _ _).2 _,
    have : ∀ (x : ℍ × ℍ), 2 * real.sqrt (x.1.im * x.2.im) ≠ 0,
      from λ x, mul_ne_zero two_ne_zero (real.sqrt_pos.2 $ mul_pos x.1.im_pos x.2.im_pos).ne',
    -- `continuity` fails to apply `continuous.div`
    apply_rules [continuous.div, continuous.mul, continuous_const, continuous.arsinh,
      continuous.dist, continuous_coe.comp, continuous_fst, continuous_snd,
      real.continuous_sqrt.comp, continuous_im.comp] },
  { refine le_of_nhds_le_nhds (λ x, _),
    rw [nhds_induced],
    refine ((@nhds_basis_ball _ metric_space_aux.to_pseudo_metric_space _).le_basis_iff
      (nhds_basis_ball.comap _)).2 (λ R hR, _),
    refine ⟨
 }
end

end upper_half_plane
