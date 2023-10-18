/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import topology.category.Top.adjunctions

/-!
# Epi- and monomorphisms in `Top`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file shows that a continuous function is an epimorphism in the category of topological spaces
if and only if it is surjective, and that a continuous function is a monomorphism in the category of
topological spaces if and only if it is injective.
-/

universe u

open category_theory
open Top

namespace Top

lemma epi_iff_surjective {X Y : Top.{u}} (f : X ⟶ Y) : epi f ↔ function.surjective f :=
begin
  suffices : epi f ↔ epi ((forget Top).map f),
  { rw [this, category_theory.epi_iff_surjective], refl },
  split,
  { introI, apply_instance },
  { apply functor.epi_of_epi_map }
end

lemma mono_iff_injective {X Y : Top.{u}} (f : X ⟶ Y) : mono f ↔ function.injective f :=
begin
  suffices : mono f ↔ mono ((forget Top).map f),
  { rw [this, category_theory.mono_iff_injective], refl },
  split,
  { introI, apply_instance },
  { apply functor.mono_of_mono_map }
end

end Top
