-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.limits.limits
import order.complete_lattice

universes u

open category_theory
open lattice

namespace category_theory.limits

variables {α : Type u}

-- It would be nice to only use the `Inf` half of the complete lattice, but
-- this seems not to have been described separately.
instance has_limits_of_complete_lattice [complete_lattice α] : has_limits.{u} α :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F,
    { cone :=
      { X := Inf (set.range F.obj),
        π :=
        { app := λ j, ⟨⟨complete_lattice.Inf_le _ _ (set.mem_range_self _)⟩⟩ } },
      is_limit :=
      { lift := λ s, ⟨⟨complete_lattice.le_Inf _ _
        begin rintros _ ⟨j, rfl⟩, exact (s.π.app j).down.down, end⟩⟩ } } } }

instance has_colimits_of_complete_lattice [complete_lattice α] : has_colimits.{u} α :=
{ has_colimits_of_shape := λ J 𝒥, by exactI
  { has_colimit := λ F,
    { cocone :=
      { X := Sup (set.range F.obj),
        ι :=
        { app := λ j, ⟨⟨complete_lattice.le_Sup _ _ (set.mem_range_self _)⟩⟩ } },
      is_colimit :=
      { desc := λ s, ⟨⟨complete_lattice.Sup_le _ _
        begin rintros _ ⟨j, rfl⟩, exact (s.ι.app j).down.down, end⟩⟩ } } } }

end category_theory.limits
