/-
Copyright (c) 2021 Scott Morrison All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Module.adjunctions
import category_theory.epi_mono

/-!
# Monomorphisms in `Module R`

This file shows that an `R`-linear map is a monomorphism in the category of `R`-modules
if and only if it is injective.
-/

universe u

open category_theory
open Module

namespace Module

variables {R : Type u} [ring R]

lemma mono_iff_injective {X Y : Module.{u} R} (f : X ⟶ Y) : mono f ↔ function.injective f :=
begin
  rw ←category_theory.mono_iff_injective,
  exact ⟨right_adjoint_preserves_mono (adj R), faithful_reflects_mono (forget (Module.{u} R))⟩,
end

end Module
