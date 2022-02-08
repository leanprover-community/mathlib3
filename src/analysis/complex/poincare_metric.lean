import analysis.complex.upper_half_plane
import analysis.special_functions.log

/-!
-/

noncomputable theory

open_locale upper_half_plane complex_conjugate nnreal
open real (sqrt log) complex

namespace upper_half_plane

instance : has_dist ℍ :=
⟨λ z w, 2 * log ((dist (z : ℂ) w + dist (z : ℂ) (conj (w : ℂ))) / (2 * sqrt (z.im * w.im)))⟩

lemma dist_eq (z w : ℍ) :
  dist z w = 2 * log ((dist (z : ℂ) w + dist (z : ℂ) (conj (w : ℂ))) / (2 * sqrt (z.im * w.im))) :=
rfl

lemma dist_mk_eq (x₁ y₁ h₁ x₂ y₂ h₂) :
  @dist ℍ _ ⟨⟨x₁, y₁⟩, h₁⟩ ⟨⟨x₂, y₂⟩, h₂⟩ =
    2 * log ((sqrt ((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2) + sqrt ((x₁ - x₂) ^ 2 + (y₁ + y₂) ^ 2)) /
      (2 * sqrt (y₁ * y₂))) :=
by simp [dist_eq, complex.dist_eq, complex.abs, complex.norm_sq_apply, sq, im]

lemma dist_num_pos (z w : ℍ) : 0 < dist (z : ℂ) w + dist (z : ℂ) (conj ↑w) :=
calc 0 < dist (w : ℂ) (conj ↑w) : by simp [eq_comm.trans eq_conj_iff_im, w.im_pos.ne']
... ≤ dist (z : ℂ) w + dist (z : ℂ) (conj ↑w) : dist_triangle_left _ _ _

lemma dist_denom_pos (z w : ℍ) : 0 < 2 * sqrt (z.im * w.im) :=
mul_pos two_pos (real.sqrt_pos.2 $ mul_pos z.im_pos w.im_pos)

lemma dist_log_arg_pos (z w : ℍ) :
  0 < (dist (z : ℂ) w + dist (z : ℂ) (conj (w : ℂ))) / (2 * sqrt (z.im * w.im)) :=
div_pos (dist_num_pos z w) (dist_denom_pos z w)

protected lemma dist_comm (z w : ℍ) : dist z w = dist w z :=
by simp only [dist_eq, dist_comm (z : ℂ), dist_conj_comm, mul_comm]

protected lemma dist_triangle (a b c : ℍ) : dist a c ≤ dist a b + dist b c :=
begin
  have H := dist_log_arg_pos,
  simp only [dist_eq, ← mul_add, mul_le_mul_left (@two_pos ℝ _ _)],
  rw [← real.log_mul (H a b).ne' (H b c).ne', real.log_le_log (H _ _) (mul_pos (H _ _) (H _ _)),
    div_mul_div, div_le_div_iff (dist_denom_pos _ _)
      (mul_pos (dist_denom_pos _ _) (dist_denom_pos _ _))],
end

lemma dist_eq_iff_complex_dist_eq {z w : ℍ} {r : ℝ≥0} :
  dist z w = r ↔ dist (z.re + (z.re / real.exp r + z.re * real.exp r) / 2 * I : ℂ) w = r :=
begin
  simp only [dist_eq, complex.dist_eq],
end


/-- For two points on the same vertical line, the distance is equal to the distance between the
logarithms of their imaginary parts. -/
lemma dist_of_re_eq {z w : ℍ} (h : z.re = w.re) : dist z w = dist (log z.im) (log w.im) :=
begin
  wlog H : w.im ≤ z.im := le_total w.im z.im using [z w, w z] tactic.skip, rotate,
  { simpa only [eq_comm, dist_comm, upper_half_plane.dist_comm] using this },
  calc dist z w = 2 * log ((|z.im - w.im| + z.im + w.im) / (2 * sqrt (z.im * w.im))) :
    begin
      conv_lhs { rw [dist_eq, ← complex.re_add_im z, ← complex.re_add_im w] },
      simp only [coe_re, coe_im, h, map_add, complex.conj_of_real, complex.dist_eq,
        add_sub_add_left_eq_sub, map_mul, complex.conj_I, ← neg_mul_eq_mul_neg, sub_neg_eq_add,
        ← sub_mul, ← add_mul, complex.abs_mul, complex.abs_I, mul_one, ← complex.of_real_add,
        ← complex.of_real_sub, complex.abs_of_real, abs_of_pos (add_pos z.im_pos w.im_pos),
        add_assoc]
    end
  ... = dist (log z.im) (log w.im) :
    begin
      rw [_root_.abs_of_nonneg (sub_nonneg.2 H), add_right_comm, sub_add_cancel, ← two_mul,
        ← div_div_eq_div_mul, mul_div_cancel_left z.im two_ne_zero, real.sqrt_mul z.im_pos.le,
        ← div_div_eq_div_mul, real.div_sqrt, ← real.sqrt_div z.im_pos.le, real.log_sqrt,
        real.log_div, mul_div_cancel', real.dist_eq, _root_.abs_of_nonneg],
      exacts [sub_nonneg.2 $ (real.log_le_log w.im_pos z.im_pos).2 H, two_ne_zero, z.im_pos.ne',
        w.im_pos.ne', div_nonneg z.im_pos.le w.im_pos.le]
    end
end

def metric_space_aux : metric_space ℍ :=
{ dist := dist,
  dist_self := λ z, by rw [dist_of_re_eq rfl, dist_self],
  dist_comm := upper_half_plane.dist_comm,
  dist_triangle := λ z₁ z₂ z₃, sorry,
  eq_of_dist_eq_zero := λ z w h,
    begin
      wlog hzw : z.im ≤ w.im, rotate,
      { rw upper_half_plane.dist_comm at h, exact (this h).symm },
      simp only [dist_eq, mul_eq_zero, two_ne_zero, false_or] at h,
      replace h := (eq_of_div_eq_one (real.eq_one_of_pos_of_log_eq_zero
        (dist_log_arg_pos _ _) h)).le,
      replace hzw : z.im = w.im,
      { replace h := (dist_triangle_left _ _ _).trans h,
        rw [dist_self_conj, mul_le_mul_left (@two_pos ℝ _ _), ← real.sqrt_mul_self_eq_abs,
          real.sqrt_le_sqrt_iff, w.coe_im, mul_le_mul_right w.im_pos] at h,
        exacts [hzw.antisymm h, mul_nonneg z.im_pos.le w.im_pos.le] },
      suffices : z.re = w.re, by ext; assumption,
      rw [hzw, real.sqrt_mul_self_eq_abs, ← coe_im, ← dist_self_conj] at h,
      replace h := h.antisymm (dist_triangle_left _ _ _),
    end }

end upper_half_plane
