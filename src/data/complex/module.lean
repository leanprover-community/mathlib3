/-
Copyright (c) 2020 Alexander Bentkamp, Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Sébastien Gouëzel
-/
import data.complex.basic
import ring_theory.algebra
/-!
This file contains three instances:
* `ℂ` is an `ℝ` algebra;
* any complex vector space is a real vector space;
* the space of `ℝ`-linear maps from a real vector space to a complex vector space is a complex
  vector space.
-/
noncomputable theory

namespace complex

instance algebra_over_reals : algebra ℝ ℂ := (complex.of_real).to_algebra

end complex

/- Register as an instance (with low priority) the fact that a complex vector space is also a real
vector space. -/
instance module.complex_to_real (E : Type*) [add_comm_group E] [module ℂ E] : module ℝ E :=
semimodule.restrict_scalars' ℝ ℂ E
attribute [instance, priority 900] module.complex_to_real

instance (E : Type*) [add_comm_group E] [module ℝ E]
  (F : Type*) [add_comm_group F] [module ℂ F] : module ℂ (E →ₗ[ℝ] F) :=
linear_map.module_extend_scalars _ _ _ _
