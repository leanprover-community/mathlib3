/-
Copyright (c) 2022 Mark Lavrentyev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Lavrentyev
-/

import topology.homotopy.equiv
import algebraic_topology.fundamental_groupoid.retraction
import algebraic_topology.fundamental_groupoid.fundamental_group
import data.real.sqrt
import analysis.normed_space.basic
-- import topology.metric_space.basic

/-
# Covering spaces

## Main definitions

  - `no_retraction f` - a
  - `brouwer_fixed_point`
-/

noncomputable theory


section brouwer_fixed_point

variables (n : ℕ) {h_two : n = 2} -- NOTE: `h_two` is here since we are limiting ourselves to D².

private def real_space : Type* := fin n → ℝ
instance : has_dist (real_space n) := ⟨λx y, sorry⟩
instance : pseudo_metric_space (real_space n) :=
{ dist_self := sorry,
  dist_comm := sorry,
  dist_triangle := sorry, }
instance : has_zero (real_space n) := ⟨λ_, 0⟩

def ball : Type* := metric.ball (0 : real_space n) 1
instance : topological_space (ball n) := subtype.topological_space
def ball_boundary : set (ball n) := frontier set.univ


-- TODO: sorry'd out fundamental group computations


theorem no_retraction (f : C(ball n, ball_boundary n)) : ¬(is_top_retraction f) :=
begin
  by_contradiction,
  sorry,
end

def ray_function (f : C(ball n, ball n)) (h_no_fixed_point : ∀x, f x ≠ x ) :
  C(ball n, ball_boundary n) :=
{ to_fun := λx, _, }

theorem brouwer_fixed_point (f : C(ball n, ball n)) : ∃(x : ball n), f x = x :=
begin
  by_contradiction,
  let retraction_fn := ray_function n f (not_exists.mp h),
  have h_is_retraction : is_top_retraction retraction_fn := ⟨retraction_fn.continuous_to_fun, sorry⟩,
  have h_not_retraction : ¬is_top_retraction retraction_fn := no_retraction n retraction_fn,
  contradiction,
end

end brouwer_fixed_point
