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
if and only if it is injective, and similarly an epimorphism if and only if it is surjective.
-/

universes v u

open category_theory
open Module

namespace Module

variables {R : Type u} [ring R]

/--
We could also give a direct proof via `linear_map.ker_eq_bot_of_cancel`.
(This would allow generalising from `Module.{u}` to `Module.{v}`.)
-/
lemma mono_iff_injective {X Y : Module.{u} R} (f : X ⟶ Y) : mono f ↔ function.injective f :=
begin
  rw ←category_theory.mono_iff_injective,
  exact ⟨right_adjoint_preserves_mono (adj R), faithful_reflects_mono (forget (Module.{u} R))⟩,
end

lemma epi_iff_surjective {X Y : Module.{v} R} (f : X ⟶ Y) : epi f ↔ function.surjective f :=
begin
  fsplit,
  { intro h,
    rw ←linear_map.range_eq_top,
    apply linear_map.range_eq_top_of_cancel,
    -- Now we have to fight a bit with the difference between `Y` and `↥Y`.
    intros u v w,
    change Y ⟶ Module.of R (linear_map.range f).quotient at u,
    change Y ⟶ Module.of R (linear_map.range f).quotient at v,
    apply (cancel_epi (Module.of_self_iso Y).hom).mp,
    apply h.left_cancellation,
    cases X, cases Y, -- after this we can see `Module.of_self_iso` is just the identity.
    convert w; { dsimp, erw category.id_comp, }, },
  { rw ←category_theory.epi_iff_surjective,
    exact faithful_reflects_epi (forget (Module.{v} R)), },
end


end Module
