/-
Copyright (c) 2022 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/

import topology.homotopy.basic
import topology.homotopy.path

-- variables (X : Type*) [topological_space X]

noncomputable theory

open path --continuous_map.homotopy_rel --homotopy--homotopic_with

open_locale unit_interval

namespace H_space

class H_space (X : Type*) [topological_space X] :=
(H_mul : X × X → X)
(e : X)
(cont' : continuous H_mul)
(self_e : H_mul (e, e) = e)
(left_mul_e : ∀ x : X,
  @continuous_map.homotopy_rel (X) (X) _ _
  ⟨(λ x : X, H_mul (e, x)), (continuous.comp cont' (continuous_const.prod_mk continuous_id'))⟩
  ⟨(λ x : X, H_mul (e, x)), (continuous.comp cont' (continuous_const.prod_mk continuous_id'))⟩
  {e})
(right_mul_e : ∀ x : X,
  @continuous_map.homotopy_rel (X) (X) _ _
  ⟨(λ x : X, H_mul (x, e)), (continuous.comp cont'(continuous_id'.prod_mk continuous_const))⟩
  ⟨(λ x : X, H_mul (x, e)), (continuous.comp cont'(continuous_id'.prod_mk continuous_const))⟩
  {e})

end H_space
