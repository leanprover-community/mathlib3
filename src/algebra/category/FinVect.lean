/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import linear_algebra.finite_dimensional
import .Module.basic


/-!
# The category of finite dimensional `R`-modules

-/
open category_theory

universes v u

variables (K : Type u) [field K]

namespace FinVect

--TODO decide between this and a new structure extending `Module`.
instance FinVect_category : category { V : Module K // finite_dimensional K V } := by apply_instance

end FinVect
