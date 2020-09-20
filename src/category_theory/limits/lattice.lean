/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.finite_limits
import order.complete_lattice

universes u

open category_theory

namespace category_theory.limits

variables {α : Type u}

@[priority 100] -- see Note [lower instance priority]
instance has_finite_limits_of_semilattice_inf_top [semilattice_inf_top α] :
  has_finite_limits α :=
λ J 𝒥₁ 𝒥₂, by exactI
  { has_limit := λ F, has_limit.mk
    { cone :=
      { X := finset.univ.inf F.obj,
        π := { app := λ j, hom_of_le (finset.inf_le (fintype.complete _)) } },
      is_limit := { lift := λ s, hom_of_le (finset.le_inf (λ j _, (s.π.app j).down.down)) } } }

@[priority 100] -- see Note [lower instance priority]
instance has_finite_colimits_of_semilattice_sup_bot [semilattice_sup_bot α] :
  has_finite_colimits α :=
λ J 𝒥₁ 𝒥₂, by exactI
  { has_colimit := λ F, has_colimit.mk
    { cocone :=
      { X := finset.univ.sup F.obj,
        ι := { app := λ i, hom_of_le (finset.le_sup (fintype.complete _)) } },
      is_colimit := { desc := λ s, hom_of_le (finset.sup_le (λ j _, (s.ι.app j).down.down)) } } }

-- It would be nice to only use the `Inf` half of the complete lattice, but
-- this seems not to have been described separately.
@[priority 100] -- see Note [lower instance priority]
instance has_limits_of_complete_lattice [complete_lattice α] : has_limits α :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit.mk
    { cone :=
      { X := Inf (set.range F.obj),
        π :=
        { app := λ j, hom_of_le (complete_lattice.Inf_le _ _ (set.mem_range_self _)) } },
      is_limit :=
      { lift := λ s, hom_of_le (complete_lattice.le_Inf _ _
        begin rintros _ ⟨j, rfl⟩, exact le_of_hom (s.π.app j), end) } } } }

@[priority 100] -- see Note [lower instance priority]
instance has_colimits_of_complete_lattice [complete_lattice α] : has_colimits α :=
{ has_colimits_of_shape := λ J 𝒥, by exactI
  { has_colimit := λ F, has_colimit.mk
    { cocone :=
      { X := Sup (set.range F.obj),
        ι :=
        { app := λ j, hom_of_le (complete_lattice.le_Sup _ _ (set.mem_range_self _)) } },
      is_colimit :=
      { desc := λ s, hom_of_le (complete_lattice.Sup_le _ _
        begin rintros _ ⟨j, rfl⟩, exact le_of_hom (s.ι.app j), end) } } } }

end category_theory.limits
