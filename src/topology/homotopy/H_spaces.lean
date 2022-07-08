/-
Copyright (c) 2022 Filippo A. E. Nuccio Mortarino Majno di Capriglio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/

import topology.homotopy.basic
import topology.homotopy.path

universe u

noncomputable theory

open path

open_locale unit_interval

namespace H_space

class H_space (X : Type u) [topological_space X]  :=
(Hmul : X × X → X)
(e : X)
(cont' : continuous Hmul)
(Hmul_e_e : Hmul (e, e) = e)
(left_Hmul_e : ∀ x : X,
  @continuous_map.homotopy_rel (X) (X) _ _
  ⟨(λ x : X, Hmul (e, x)), (continuous.comp cont' (continuous_const.prod_mk continuous_id'))⟩
  ⟨(λ x : X, Hmul (e, x)), (continuous.comp cont' (continuous_const.prod_mk continuous_id'))⟩
  {e})
(right_Hmul_e : ∀ x : X,
  @continuous_map.homotopy_rel (X) (X) _ _
  ⟨(λ x : X, Hmul (x, e)), (continuous.comp cont'(continuous_id'.prod_mk continuous_const))⟩
  ⟨(λ x : X, Hmul (x, e)), (continuous.comp cont'(continuous_id'.prod_mk continuous_const))⟩
  {e})

instance topological_group_H_space (G : Type u) [topological_space G] [group G]
  [topological_group G]: H_space G :=
{ Hmul := function.uncurry has_mul.mul,
  e := 1,
  cont' := continuous_mul,
  Hmul_e_e := by {simp only [function.uncurry_apply_pair, mul_one]},
  left_Hmul_e := λ _, continuous_map.homotopy_rel.refl _ _ ,
  right_Hmul_e := λ _, continuous_map.homotopy_rel.refl _ _ }

-- instance S0_H_space : H_space (metric.sphere (0 : ℝ × ℝ) 1) := sorry
-- instance S1_H_space : H_space (metric.sphere (0 : ℝ × ℝ) 1) := sorry
-- instance S3_H_space : H_space (metric.sphere (0 : ℝ × ℝ) 1) := sorry
-- instance S7_H_space : H_space (metric.sphere (0 : ℝ × ℝ) 1) := sorry

variables {X : Type u} [topological_space X]

def loop_space (x : X) : Type u := {f : C(I, X) // f 0 = x ∧ f 1 = x}

instance (x : X) : topological_space (loop_space x) := by {exact subtype.topological_space}

instance loop_space_is_H_space (x : X) : H_space (loop_space x) :=
{ Hmul := sorry,
  e := sorry,
  cont' := sorry,
  Hmul_e_e := sorry,
  left_Hmul_e := sorry,
  right_Hmul_e := sorry}


end H_space
