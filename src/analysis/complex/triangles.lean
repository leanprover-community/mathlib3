import analysis.complex.basic
import data.zmod.basic
import measure_theory.interval_integral

noncomputable theory

open_locale big_operators
open set function finset

/-- A triangle is a function from `ℤ/3ℤ` to `ℂ` (this definition allows for the description of
adjacent vertices as `i` and `i + 1`, cyclically). -/
def triangle := zmod 3 → ℂ

/-- Given a function `f : ℂ → ℂ`, the contour integral of `f` along the segment from `a` to `b` is
defined to be the (real) integral from `0` to `1` of the function
`λ t, f ((1 - t) * a + t * b) * (b - a)`. -/
def contour_integral_segment (f : ℂ → ℂ) (a b : ℂ) : ℂ :=
∫ (t : ℝ) in 0..1, f ((1 - t) * a + t * b) * (b - a)

/-- The contour integral of a constant `c` along the segment from `a` to `b` is `c * (b - a)`. -/
lemma contour_integral_segment.integral_const (c : ℂ) (a b : ℂ) :
  contour_integral_segment (λ z, c) a b = c * (b - a) :=
by simp [contour_integral_segment, interval_integral.integral_const]

/-- Given a function `f : ℂ → ℂ`, the contour integral of `f` around a triangle is defined to be the
sum of the contour integrals along the three segments forming its sides. -/
def contour_integral (f : ℂ → ℂ) (T : triangle) : ℂ :=
∑ i, contour_integral_segment f (T i) (T (i + 1))

/-- The contour integral of a constant `c` around a triangle is `0`. -/
lemma contour_integral.integral_const (c : ℂ) (T : triangle) : contour_integral (λ z, c) T = 0 :=
begin
  simp only [contour_integral, contour_integral_segment.integral_const],
  calc ∑ i, c * (T (i + 1) - T i)
      =  ∑ i, (c * T (i + 1) - c * T i) : by { congr, ext; ring }
  ... = c * (∑ i, T (i + 1)) - c * (∑ i, T i) : by simp [mul_sum]
  ... = 0 : _,
  rw sub_eq_zero,
  congr' 1,
  exact (equiv.add_left (1 : zmod 3)).sum_comp _
end

/-- The function partitioning a triangle into four smaller triangles, parametrized by `ℤ/3ℤ` (one
for each of the three corner triangles) and `none` (for the centre triangle). -/
def quadrisect (T : triangle) : option (zmod 3) → triangle
| none := λ j, ((∑ i, T i) - T j) / 2
| (some i) := λ j, (T i + T j) / 2
