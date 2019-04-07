import category_theory.instances.Top.basic
import category_theory.limits.types
import category_theory.limits.preserves

open category_theory
open category_theory.instances
open topological_space

universe u

namespace category_theory.instances.Top

open category_theory.limits

variables {J : Type u} [small_category J]

def limit (F : J ⥤ Top.{u}) : cone F :=
{ X := ⟨limit (F ⋙ forget), ⨆ j, (F.obj j).str.induced (limit.π (F ⋙ forget) j)⟩,
  π :=
  { app := λ j, ⟨limit.π (F ⋙ forget) j, continuous_iff_induced_le.mpr (lattice.le_supr _ j)⟩,
    naturality' := λ j j' f, subtype.eq ((limit.cone (F ⋙ forget)).π.naturality f) } }

def limit_is_limit (F : J ⥤ Top.{u}) : is_limit (limit F) :=
by refine is_limit.of_faithful forget (limit.is_limit _) (λ s, ⟨_, _⟩) (λ s, rfl);
   exact continuous_iff_le_coinduced.mpr (lattice.supr_le $ λ j,
     induced_le_iff_le_coinduced.mpr $ continuous_iff_le_coinduced.mp (s.π.app j).property)

instance Top_has_limits : has_limits.{u} Top.{u} :=
{ has_limits_of_shape := λ J 𝒥,
  { has_limit := λ F, by exactI { cone := limit F, is_limit := limit_is_limit F } } }

instance forget_preserves_limits : preserves_limits (forget : Top.{u} ⥤ Type u) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit.is_limit F) (limit.is_limit (F ⋙ forget)) } }

def colimit (F : J ⥤ Top.{u}) : cocone F :=
{ X := ⟨colimit (F ⋙ forget), ⨅ j, (F.obj j).str.coinduced (colimit.ι (F ⋙ forget) j)⟩,
  ι :=
  { app := λ j, ⟨colimit.ι (F ⋙ forget) j, continuous_iff_le_coinduced.mpr (lattice.infi_le _ j)⟩,
    naturality' := λ j j' f, subtype.eq ((colimit.cocone (F ⋙ forget)).ι.naturality f) } }

def colimit_is_colimit (F : J ⥤ Top.{u}) : is_colimit (colimit F) :=
by refine is_colimit.of_faithful forget (colimit.is_colimit _) (λ s, ⟨_, _⟩) (λ s, rfl);
   exact continuous_iff_induced_le.mpr (lattice.le_infi $ λ j,
     induced_le_iff_le_coinduced.mpr $ continuous_iff_le_coinduced.mp (s.ι.app j).property)

instance Top_has_colimits : has_colimits.{u} Top.{u} :=
{ has_colimits_of_shape := λ J 𝒥,
  { has_colimit := λ F, by exactI { cocone := colimit F, is_colimit := colimit_is_colimit F } } }

instance forget_preserves_colimits : preserves_colimits (forget : Top.{u} ⥤ Type u) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_colimit_of_preserves_colimit_cocone
      (colimit.is_colimit F) (colimit.is_colimit (F ⋙ forget)) } }

end category_theory.instances.Top
