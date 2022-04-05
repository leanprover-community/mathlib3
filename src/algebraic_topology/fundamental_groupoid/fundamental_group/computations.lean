/-
Copyright (c) 2022 Mark Lavrentyev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Lavrentyev
-/
import topology.metric_space.basic
import algebraic_topology.fundamental_groupoid.fundamental_group.basic
import algebraic_topology.fundamental_groupoid.basic
import analysis.normed_space.basic
import analysis.convex.basic
import algebra.category.Group.basic

/-!
# Fundamental group computations

Provides basic computations of fundamental groups of common spaces. Useful for proving
various theorems about these spaces later.
-/

universes u v
local attribute [instance] path.homotopic.setoid

variables (n : ℕ) {hn_nonneg : n > 0}
local notation `ℝⁿ` := fin n → ℝ
local notation `ℝⁿ⁺¹` := fin (n + 1) → ℝ

section convex_space

variables (X : set ℝⁿ) {x₀ x₁ : X}

instance has_scalar.ℝⁿ : has_scalar unit_interval ℝⁿ :=
⟨λ(k : unit_interval) (x : ℝⁿ),
  λ(i : fin n), (x i) * k⟩

/-- In a convex subset X ⊆ ℝⁿ, any two paths are homotopic via straight line homotopy. -/
noncomputable def path_homotopic_of_convex (p₀ p₁ : path x₀ x₁) (h_convex : convex ℝ X) :
  p₀.homotopy p₁ :=
{ to_fun := λii, ⟨ii.fst.val • (p₁ ii.snd).val + (unit_interval.symm ii.fst).val • (p₀ ii.snd).val,
                  begin
                    apply h_convex,
                    { apply subtype.coe_prop },
                    { apply subtype.coe_prop },
                    { rw subtype.val_eq_coe,
                      exact unit_interval.nonneg ii.fst },
                    { rw [subtype.val_eq_coe, unit_interval.coe_symm_eq, sub_nonneg],
                      exact unit_interval.le_one ii.fst },
                    { rw [subtype.val_eq_coe, subtype.val_eq_coe, unit_interval.coe_symm_eq,
                          add_sub_cancel'_right], }
                  end⟩,
  continuous_to_fun := sorry, --by simp,
  map_zero_left' := sorry, --by simp,
  map_one_left' := sorry, --by simp,
  prop' := sorry,
}

/-- The fundamental group of a convex subset X ⊆ ℝⁿ is isomorphic to the trivial group. -/
noncomputable lemma trivial_fundamental_group_of_convex (h_convex : convex ℝ X):
  fundamental_group X x₀ ≃* Group.of unit :=
{
  to_fun := λ_, unit.star,
  inv_fun := λs, @fundamental_group.from_path (Top.of X) x₀ (⟦path.refl x₀⟧),
  left_inv :=
    begin
      rw function.left_inverse,
      sorry,
    end,
  right_inv := sorry,
  map_mul' := sorry,
}

end convex_space


section unit_disk

/-- The unit disk Dⁿ ⊆ ℝⁿ. -/
def unit_disk := metric.closed_ball (0 : ℝⁿ) 1

set_option trace.simplify.rewrite true
lemma convex_of_unit_disk : convex ℝ (unit_disk n) :=
begin
  rw convex,
  intros x y hx hy a b ha hb hab,
  rw [unit_disk, metric.closed_ball, set.mem_set_of_eq, dist_zero_right],
  sorry,
end

/-- A convenient basepoint for computing the fundamental group, namely (1, 0 ...). -/
def unit_disk_basepoint : unit_disk n :=
⟨λi, if i = ⟨0, hn_nonneg⟩ then 1 else 0, sorry⟩

/-- The fundamental group of the disk is isomorphic to the trivial group. -/
noncomputable lemma fundamental_group_trivial :
  fundamental_group (unit_disk n) (@unit_disk_basepoint n hn_nonneg) ≃* Group.of unit :=
trivial_fundamental_group_of_convex n (unit_disk n) (convex_of_unit_disk n)

end unit_disk


section unit_sphere

/-- The unit sphere Sⁿ ⊆ ℝⁿ⁺¹. -/
def unit_sphere := metric.sphere (0 : ℝⁿ⁺¹) 1

/-- A convenient basepoint for computing the fundamental group, namely (1, 0 ...). -/
def unit_sphere_basepoint : unit_sphere n := sorry

/-- The fundamental group of the circle S¹ is isomorphic to the group of integers. -/
noncomputable lemma fundamental_group_circle_iso_int :
  fundamental_group (unit_sphere 1) (unit_sphere_basepoint 1) ≃* ℤ :=
sorry

noncomputable lemma fundamental_group_sphere_trivial (n : ℕ) (hn : n ≥ 2) :
  fundamental_group (unit_sphere n) (unit_sphere_basepoint n) ≃* Group.of unit :=
sorry

end unit_sphere
