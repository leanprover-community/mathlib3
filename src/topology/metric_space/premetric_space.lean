/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Premetric spaces.

Author: Sébastien Gouëzel

Metric spaces are often defined as quotients of spaces endowed with a "distance"
function satisfying the triangular inequality, but for which `dist x y = 0` does
not imply x = y. We call such a space a premetric space.
`dist x y = 0` defines an equivalence relation, and the quotient
is canonically a metric space.
-/

import topology.metric_space.basic tactic.linarith
noncomputable theory

universes u v
variables {α : Type u}

class premetric_space (α : Type u) extends has_dist α : Type u :=
(dist_self : ∀ x : α, dist x x = 0)
(dist_comm : ∀ x y : α, dist x y = dist y x)
(dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)

namespace premetric
section

protected lemma dist_nonneg {α : Type u} [premetric_space α] {x y : α} : 0 ≤ dist x y :=
begin
  have := calc
    0 = dist x x : (premetric_space.dist_self _).symm
    ... ≤ dist x y + dist y x : premetric_space.dist_triangle _ _ _
    ... = dist x y + dist x y : by simp [premetric_space.dist_comm],
  by linarith
end

/-- The canonical equivalence relation on a premetric space. -/
def dist_setoid (α : Type u) [premetric_space α] : setoid α :=
setoid.mk (λx y, dist x y = 0)
begin
  unfold equivalence,
  repeat { split },
  { exact premetric_space.dist_self },
  { assume x y h, rwa premetric_space.dist_comm },
  { assume x y z hxy hyz,
    refine le_antisymm _ premetric.dist_nonneg,
    calc dist x z ≤ dist x y + dist y z : premetric_space.dist_triangle _ _ _
         ... = 0 + 0 : by rw [hxy, hyz]
         ... = 0 : by simp }
end

local attribute [instance] dist_setoid

/-- The canonical quotient of a premetric space, identifying points at distance 0. -/
@[reducible] definition metric_quot (α : Type u) [premetric_space α] : Type* :=
quotient (premetric.dist_setoid α)

instance has_dist_metric_quot {α : Type u} [premetric_space α] : has_dist (metric_quot α) :=
{ dist := quotient.lift₂ (λp q : α, dist p q)
begin
  assume x y x' y' hxx' hyy',
  have Hxx' : dist x x' = 0 := hxx',
  have Hyy' : dist y y' = 0 := hyy',
  have A : dist x y ≤ dist x' y' := calc
    dist x y ≤ dist x x' + dist x' y : premetric_space.dist_triangle _ _ _
    ... = dist x' y : by simp [Hxx']
    ... ≤ dist x' y' + dist y' y : premetric_space.dist_triangle _ _ _
    ... = dist x' y' : by simp [premetric_space.dist_comm, Hyy'],
  have B : dist x' y' ≤ dist x y := calc
    dist x' y' ≤ dist x' x + dist x y' : premetric_space.dist_triangle _ _ _
    ... = dist x y' : by simp [premetric_space.dist_comm, Hxx']
    ... ≤ dist x y + dist y y' : premetric_space.dist_triangle _ _ _
    ... = dist x y : by simp [Hyy'],
  exact le_antisymm A B
end }

lemma metric_quot_dist_eq {α : Type u} [premetric_space α] (p q : α) : dist ⟦p⟧ ⟦q⟧ = dist p q := rfl

instance metric_space_quot {α : Type u} [premetric_space α] : metric_space (metric_quot α) :=
{ dist_self := begin
    refine quotient.ind (λy, _),
    exact premetric_space.dist_self _
  end,
  eq_of_dist_eq_zero :=
    λxc yc, quotient.induction_on₂ xc yc (λx y H, quotient.sound H),
  dist_comm :=
    λxc yc, quotient.induction_on₂ xc yc (λx y, premetric_space.dist_comm _ _),
  dist_triangle :=
    λxc yc zc, quotient.induction_on₃ xc yc zc (λx y z, premetric_space.dist_triangle _ _ _) }

end --section
end premetric --namespace
