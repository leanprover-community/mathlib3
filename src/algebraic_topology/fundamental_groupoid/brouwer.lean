/-
Copyright (c) 2022 Mark Lavrentyev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Lavrentyev
-/

import topology.homotopy.equiv
import algebraic_topology.fundamental_groupoid.retraction
import algebraic_topology.fundamental_groupoid.fundamental_group
import algebra.group.type_tags
import data.real.sqrt
import analysis.inner_product_space.pi_L2

/-
# Covering spaces

## Main definitions

  - `no_retraction f` - a
  - `brouwer_fixed_point`
-/
noncomputable theory

universe u

open fundamental_groupoid category_theory fundamental_groupoid_functor

open_locale fundamental_groupoid unit_interval


section brouwer_fixed_point

variables (n : ℕ) {h_two : n = 2} -- NOTE: `h_two` is here since we are limiting ourselves to D².

def ball : set (euclidean_space ℝ (fin n)) := euclidean.ball 0 1
instance : topological_space (ball n) := subtype.topological_space
def ball_boundary : set (ball n) := frontier set.univ


-- TODO: sorry'd out fundamental groupoid computations

lemma fundamental_group_ball :
  Group.of(fundamental_group (ball 2) _) ≅ Group.of unit := sorry
lemma fundamental_group_frontier_ball :
  Group.of (fundamental_group (ball_boundary 2) _) ≅ Group.of (muliplicative ℤ) := sorry


theorem no_retraction (f : C(ball n, ball_boundary n)) : ¬(is_top_retraction f) :=
begin
  by_contradiction,
  let r : top_retraction (ball n) (ball_boundary n) := ⟨f, h⟩,
  have h_epi_groupoid := top_retraction.fundamental_groupoid_epi_of_top_retraction r,
  apply absurd h_epi_groupoid,
  -- TODO: prove that it can't be an epi, based on fg computations
  sorry,
end

lemma scale_of_two_points (x y : ball n) (h_neq : x ≠ y) : ∃(t : ℝ), x + ((y - x) * t) ∈ ball_boundary n :=
sorry

-- TODO: use abs_abs_sub_abs_le_abs_sub to prove we have such a `t` via IVT
def ray_function (f : C(ball n, ball n)) (h_no_fixed_point : ∀x, f x ≠ x ) :
  C(ball n, ball_boundary n) :=
⟨λx, ⟨x + ((f x - x) * 0.5), sorry⟩⟩

theorem brouwer_fixed_point (f : C(ball n, ball n)) : ∃(x : ball n), f x = x :=
begin
  by_contradiction,
  let retraction_fn := ray_function n f (not_exists.mp h),
  have h_is_retraction : is_top_retraction retraction_fn := ⟨retraction_fn.continuous_to_fun, sorry⟩,
  have h_not_retraction : ¬is_top_retraction retraction_fn := no_retraction n retraction_fn,
  contradiction,
end

end brouwer_fixed_point
