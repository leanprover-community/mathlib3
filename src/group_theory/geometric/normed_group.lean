import analysis.normed.group.basic
import analysis.seminorm

/-!
# Multiplicative normed groups

This file defines multiplicative normed groups.
-/

variables (E : Type*)

/-- A semi-normed group is a group endowed with a norm for which `dist x y = ∥x⁻¹*y∥`
defines a metric space structure. -/
class seminormed_mul_group extends has_norm E, group E, pseudo_metric_space E :=
(dist := λ x y, ∥x⁻¹*y∥)
(dist_eq : ∀ x y, dist x y = ∥x⁻¹*y∥ . obviously)

/-- A normed group is an additive group endowed with a norm for which `dist x y = ∥x - y∥` defines
a metric space structure. -/
class normed_mul_group extends has_norm E, group E, metric_space E :=
(dist := λ x y, ∥x⁻¹*y∥)
(dist_eq : ∀ x y, dist x y = ∥x⁻¹*y∥ . obviously)

@[priority 100] -- See note [lower instance priority]
instance normed_mul_group.to_seminormed_mul_group [normed_mul_group E] : seminormed_mul_group E :=
{ ..‹normed_mul_group E› }

variables [group E]

/-- A norm on a group `G` is a function `f : G → ℝ` that preserves zero, takes nonnegative values,
is submultiplicative and such that `f x⁻¹ = f x` and `f x = 0 → x = 1` for all `x`. -/
@[nolint has_inhabited_instance] structure group_norm extends group_seminorm E :=
(eq_one_of_to_fun : ∀ ⦃x : E⦄, to_fun x = 0 → x = 1)

/-- Constructing a seminormed group from a seminorm, i.e., registering the pseudodistance and the
pseudometric space structure from the seminorm properties. Note that in most cases this instance
creates bad definitional equalities (e.g., it does not take into account a possibly existing
`uniform_space` instance on `E`). -/
def group_seminorm.to_seminormed_mul_group (p : group_seminorm E) : seminormed_mul_group E :=
{ norm := p,
  dist := λ x y, p (x⁻¹*y),
  dist_self := λ x, by simp [p.map_one],
  dist_triangle := λ x y z,
    calc p (x⁻¹*z) = p (x⁻¹*y * (y⁻¹*z)) : by rw [mul_assoc, mul_inv_cancel_left]
            ... ≤ p (x⁻¹*y) + p (y⁻¹*z)  : p.mul_le _ _,
  dist_comm := λ x y,
    calc p (x⁻¹*y) = p (y⁻¹*x)⁻¹ : by rw [mul_inv_rev,inv_inv]
            ... = p (y⁻¹*x) : p.inv _
 }

/-- Constructing a normed group from a norm, i.e., registering the distance and the metric space
structure from the norm properties. Note that in most cases this instance creates bad definitional
equalities (e.g., it does not take into account a possibly existing `uniform_space instance on `E`).
-/
def group_norm.to_normed_mul_group (p : group_norm E) : normed_mul_group E :=
{ eq_of_dist_eq_zero := λ x y h, inv_mul_eq_one.1 $ p.eq_one_of_to_fun h,
  ..p.to_group_seminorm.to_seminormed_mul_group _ }
