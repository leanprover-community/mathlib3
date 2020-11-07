import measure_theory.prod
import analysis.normed_space.box_subadditive
import measure_theory.interval_integral

noncomputable theory

open fin set function
open_locale big_operators

/-- Given a point `x` in the plane, an index `i`, and a real number `a`, we introduce a definition
for the integral of a function along the segment obtained by varying the `i`-th coordinate of `x`
between its original variable and `a`. -/
def segment_parametrized_integral (f : (fin 2 → ℝ) → ℝ) (x : fin 2 → ℝ) (i : fin 2) (a : ℝ) : ℝ :=
∫ t in (x i)..a, f (update x i t)

variables {u : (fin 2 → ℝ) → ℝ} (hu : continuous u)

include hu

/-- Given a rectangle (defined by two points, the bottom-left corner `a` and the top-right corner
`b`), and a fixed continuous function `u` on the plane, and an index `i` in `fin 2`, the function
that sends a rectangle to the integral of `u` in opposite directions along the two sides parallel to
the `i`-axis. -/
def box_line_integral (i : fin 2) (a b : fin 2 → ℝ) : ℝ :=
(segment_parametrized_integral u a i (b i) - segment_parametrized_integral u b i (a i))

/-- The function `box_line_integral` is additive over rectangles. -/
lemma is_box_additive_line_integral (i : fin 2) : box_additive_on (box_line_integral hu i) univ :=
sorry
